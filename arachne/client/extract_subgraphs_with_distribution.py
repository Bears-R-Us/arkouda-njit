"""
extract_subgraphs_with_distribution.py  —  split, analyze, and distribute cluster TSV files
for Chapel well-connectedness distributed execution.

Modes:
  split      — split a combined TSV (clusters separated by '-') into cluster_N.tsv
  analyze    — report inter-locale AND intra-locale balance for every strategy
  distribute — assign clusters to locale_0/.., locale_N/ subfolders

Typical workflow:
  1. python cluster_tools.py split   <combined.tsv>  --output_dir <flat_dir>
  2. python cluster_tools.py analyze <flat_dir>       --num_locales 4 --num_cores 64
  3. python cluster_tools.py distribute <flat_dir> <dist_dir> --num_locales 4
                             --num_cores 64 --strategy n+m
  4. Point Chapel's inputFolderPath to <dist_dir>  (see Chapel changes in README)
"""

from __future__ import annotations

import os
import math
import heapq
import argparse
from collections import defaultdict
from dataclasses import dataclass


# ---------------------------------------------------------------------------
# 1.  Split a combined TSV into per-cluster files
# ---------------------------------------------------------------------------

def split_clusters(input_file: str, output_dir: str = ".") -> None:
    """Split combined file (clusters separated by '-' lines) into cluster_N.tsv."""
    os.makedirs(output_dir, exist_ok=True)
    cluster_id = 0
    current_cluster: list[str] = []

    with open(input_file) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            if line == "-":
                if current_cluster:
                    _write_cluster(output_dir, cluster_id, current_cluster)
                    cluster_id += 1
                    current_cluster = []
            else:
                current_cluster.append(line)

    print("Last line")
    if current_cluster:
        _write_cluster(output_dir, cluster_id, current_cluster)
        cluster_id += 1

    print(f"Done. Created {cluster_id} cluster files in {output_dir}")


def _write_cluster(output_dir: str, cluster_id: int, lines: list[str]) -> None:
    path = os.path.join(output_dir, f"cluster_{cluster_id}.tsv")
    with open(path, "w") as out:
        out.write("\n".join(lines))
    print(f"Saved {path}")


# ---------------------------------------------------------------------------
# 2.  Cluster statistics
# ---------------------------------------------------------------------------

@dataclass
class ClusterInfo:
    cluster_id: int
    n: int          # distinct vertices  (0 in fast mode)
    m: int          # edges              (0 in fast mode)
    file_bytes: int # file size in bytes — always available, fast proxy for m
    filepath: str   # absolute path


def scan_cluster_stats(cluster_dir: str, fast: bool = False,
                       verbose: bool = True) -> list[ClusterInfo]:
    """
    Scan all cluster_*.tsv files and return ClusterInfo for each.

    fast=False  (default): open every file, count distinct vertices (n) and
                edges (m). Accurate but slow for 100 K+ files (~5-10 min).
    fast=True:  only stat() each file for byte size; n=0, m=0.
                Use when you only need file_bytes as weight proxy (seconds).
    """
    filenames = sorted(
        f for f in os.listdir(cluster_dir)
        if f.startswith("cluster_") and f.endswith(".tsv")
    )
    clusters: list[ClusterInfo] = []
    total = len(filenames)

    for i, fname in enumerate(filenames):
        stem = fname[len("cluster_"):-len(".tsv")]
        try:
            cid = int(stem)
        except ValueError:
            continue
        filepath = os.path.abspath(os.path.join(cluster_dir, fname))
        fsize = os.path.getsize(filepath)

        if fast:
            clusters.append(ClusterInfo(cluster_id=cid, n=0, m=0,
                                        file_bytes=fsize, filepath=filepath))
        else:
            vertices: set[str] = set()
            edges = 0
            with open(filepath) as f:
                for line in f:
                    parts = line.strip().split()
                    if len(parts) >= 2:
                        vertices.add(parts[0])
                        vertices.add(parts[1])
                        edges += 1
            clusters.append(ClusterInfo(cluster_id=cid, n=len(vertices), m=edges,
                                        file_bytes=fsize, filepath=filepath))

        if verbose and (i + 1) % 10_000 == 0:
            print(f"  Scanned {i + 1}/{total} ...")

    return clusters


# ---------------------------------------------------------------------------
# 3.  Inter-locale distribution strategies
# ---------------------------------------------------------------------------

Assignment = dict[int, list[ClusterInfo]]


def round_robin_by_position(clusters: list[ClusterInfo],
                             num_locales: int) -> Assignment:
    """
    Replicates the current Chapel code exactly:
      sort filenames as STRINGS (not numeric!), then locale L gets
      positions L, L+num_locales, L+2*num_locales, ...

    String sort matters: "cluster_10.tsv" < "cluster_2.tsv"
    so this differs from cluster_id % num_locales.
    """
    sorted_c = sorted(clusters, key=lambda c: f"cluster_{c.cluster_id}.tsv")
    result: Assignment = defaultdict(list)
    for idx, c in enumerate(sorted_c):
        result[idx % num_locales].append(c)
    return dict(result)


def greedy_lpt(clusters: list[ClusterInfo], num_locales: int,
               weight_fn) -> Assignment:
    """
    Greedy LPT (Longest Processing Time first):
    sort descending by weight, always assign next cluster to least-loaded locale.
    Standard O(C log L) approximation for makespan minimisation.
    Gives <= (4/3 - 1/(3L)) * OPT makespan guarantee.
    """
    sorted_c = sorted(clusters, key=lambda c: weight_fn(c), reverse=True)
    heap = [(0.0, i) for i in range(num_locales)]
    heapq.heapify(heap)
    result: Assignment = defaultdict(list)
    for c in sorted_c:
        w = weight_fn(c)
        total, loc_id = heapq.heappop(heap)
        result[loc_id].append(c)
        heapq.heappush(heap, (total + w, loc_id))
    return dict(result)


# Weight functions — (human description, callable | None)
# None means the strategy uses round_robin_by_position, not greedy_lpt.
WEIGHT_FUNCTIONS: dict[str, tuple[str, object]] = {
    "round_robin": ("position % L  — current Chapel code",           None),
    "bytes":       ("file size in bytes  (fast proxy for m)",         lambda c: c.file_bytes),
    "n":           ("vertex count  (n)",                              lambda c: c.n),
    "m":           ("edge count  (m)",                                lambda c: c.m),
    "n+m":         ("vertices + edges  (n+m)",                        lambda c: c.n + c.m),
    "n+2m":        ("n + 2*m  (undirected adj-list size)",            lambda c: c.n + 2 * c.m),
    "m*n":         ("edges × vertices  (m*n)",                        lambda c: c.m * c.n),
    "sqrt_nm":     ("sqrt(n*m)",                                      lambda c: math.sqrt(c.n * c.m)
                                                                                if c.n * c.m > 0 else 0.0),
    "m2_over_n":   ("m² / n  (dense-graph bias)",                     lambda c: (c.m ** 2) / c.n
                                                                                if c.n > 0 else 0.0),
    "n_log_n":     ("n·log₂(n)  (sort overhead in loadClusterFile)",  lambda c: c.n * math.log2(c.n)
                                                                                if c.n > 1 else 0.0),
    "m_log_n":     ("m·log₂(n)  (bridge-finding O(m+n·log n))",       lambda c: c.m * math.log2(c.n)
                                                                                if c.n > 1 else 0.0),
    "n_log_n_m":   ("(n+m)·log₂(n)  (sort + mincut composite cost)",  lambda c: (c.n + c.m) * math.log2(c.n)
                                                                                if c.n > 1 else float(c.n + c.m)),
}

# Strategies that require a full scan (need n and m)
NEEDS_FULL_SCAN = {"n", "m", "n+m", "n+2m", "m*n", "sqrt_nm", "m2_over_n", "n_log_n", "m_log_n",
                   "n_log_n_m"}


# ---------------------------------------------------------------------------
# 4.  Intra-locale ordering strategies
# ---------------------------------------------------------------------------

def order_string_sort(files: list[ClusterInfo]) -> list[ClusterInfo]:
    """Current Chapel behavior: sort by filename as string (lexicographic)."""
    return sorted(files, key=lambda c: f"cluster_{c.cluster_id}.tsv")


def order_lpt_desc(files: list[ClusterInfo], weight_fn) -> list[ClusterInfo]:
    """
    Sort descending by weight (heaviest first).
    With Chapel's static forall blocking, core 0 gets the heaviest
    contiguous block — can be WORSE than random for static schedules.
    Included for comparison.
    """
    return sorted(files, key=lambda c: weight_fn(c), reverse=True)


def order_lpt_interleaved(files: list[ClusterInfo], weight_fn,
                           num_cores: int) -> list[ClusterInfo]:
    """
    LPT Interleaved — the best ordering for Chapel's static forall blocking.

    Algorithm:
      1. Sort descending by weight.
      2. Extract every num_cores-th element starting at offset 0, 1, ..., num_cores-1.
         This creates num_cores stripes; each stripe is placed as a contiguous block.

    Result: each contiguous block of size (total/num_cores) contains one element
    from each "rank band", so all cores get a similar mix of heavy and light work.

    Example — 8 clusters, 2 cores, weights [10,9,8,7,6,5,4,3]:
      stripe 0 (positions 0,2,4,6): [10, 8, 6, 4]  total=28
      stripe 1 (positions 1,3,5,7): [ 9, 7, 5, 3]  total=24
      result list: [10, 8, 6, 4, 9, 7, 5, 3]
      Core 0 gets [10,8,6,4]=28   Core 1 gets [9,7,5,3]=24
      vs. sorted desc naive:  Core 0=[10,9,8,7]=34  Core 1=[6,5,4,3]=18  (worse)
    """
    sorted_files = sorted(files, key=lambda c: weight_fn(c), reverse=True)
    result: list[ClusterInfo] = []
    for offset in range(num_cores):
        result.extend(sorted_files[offset::num_cores])
    return result


ORDERINGS = {
    "string_sort":     "string sort  (current Chapel forall order)",
    "lpt_desc":        "descending weight  (heaviest block first)",
    "lpt_interleaved": "LPT interleaved  (balanced static chunks)  ← recommended",
}


# ---------------------------------------------------------------------------
# 5.  Intra-locale simulation: static blocking
# ---------------------------------------------------------------------------

def simulate_static_blocking(ordered_files: list[ClusterInfo],
                              num_cores: int,
                              weight_fn) -> dict:
    """
    Simulate Chapel's forall static blocking:
    divide file list into num_cores contiguous chunks, compute per-core weight total.

    Returns dict with keys: core_weights, max, avg, min, imbalance_pct
    imbalance_pct = (max - avg) / avg   (how much the slowest core exceeds average)
    """
    n = len(ordered_files)
    chunk = math.ceil(n / num_cores) if num_cores > 0 else n
    core_weights = []
    for core in range(num_cores):
        start = core * chunk
        end   = min(start + chunk, n)
        w = sum(weight_fn(f) for f in ordered_files[start:end]) if start < n else 0.0
        core_weights.append(w)
    mx  = max(core_weights)
    mn  = min(core_weights)
    avg = sum(core_weights) / num_cores
    imb = (mx - avg) / avg if avg > 0 else 0.0
    return {"core_weights": core_weights, "max": mx, "min": mn,
            "avg": avg, "imbalance_pct": imb}


# ---------------------------------------------------------------------------
# 6.  Reporting
# ---------------------------------------------------------------------------

def _stats(values: list[float]) -> tuple[float, float, float, float]:
    mn  = min(values)
    mx  = max(values)
    avg = sum(values) / len(values)
    sd  = math.sqrt(sum((v - avg) ** 2 for v in values) / len(values))
    return mn, mx, avg, sd


def _weight_for_strategy(strategy: str, weight_fn, fast: bool) -> object:
    """Return the weight function to use for intra-locale simulation."""
    if fast or strategy in ("round_robin", "bytes"):
        return lambda c: c.file_bytes
    return weight_fn if weight_fn is not None else (lambda c: c.n + c.m)


def print_distribution_report(clusters: list[ClusterInfo],
                               num_locales: int,
                               num_cores: int,
                               fast: bool,
                               calibration_times: list[float] | None = None,
                               calibration_strategy: str = "n",
                               strategy_whitelist: list[str] | None = None) -> None:
    """
    Print per-strategy inter/intra-locale balance analysis.

    calibration_times : actual Chapel wall times per locale (from a prior run),
                        e.g. [28.68, 22.42, 29.47, 16.95] for locales 0..3.
                        When provided, a RUNTIME PREDICTION table is appended that
                        converts simulated core weights to seconds using per-node
                        efficiency factors, accounting for:
                          - Chapel's static forall blocking (num_cores contiguous chunks)
                          - Wulver's per-node speed variance (GPFS I/O, NUMA, load)
    calibration_strategy : which strategy was used in the calibration run (default: n).
    """
    total_n     = sum(c.n for c in clusters)
    total_m     = sum(c.m for c in clusters)
    total_bytes = sum(c.file_bytes for c in clusters)

    print(f"\n{'='*88}")
    if fast:
        print(f"Dataset : {len(clusters)} clusters | {total_bytes:,} bytes total  [fast mode — n/m not scanned]")
    else:
        print(f"Dataset : {len(clusters)} clusters | {total_n:,} vertices | {total_m:,} edges | {total_bytes:,} bytes")
    print(f"Locales : {num_locales}   Cores per locale : {num_cores}")
    print(f"{'='*88}")

    # Skip strategies that need full scan when in fast mode.
    # Optionally restrict to a user-supplied whitelist (--strategies flag).
    active = {k: v for k, v in WEIGHT_FUNCTIONS.items()
              if not (fast and k in NEEDS_FULL_SCAN)}
    if strategy_whitelist:
        unknown = [k for k in strategy_whitelist if k not in WEIGHT_FUNCTIONS]
        if unknown:
            print(f"Warning: unknown strategies in --strategies: {unknown}")
        active = {k: v for k, v in active.items() if k in strategy_whitelist}

    # Track per-strategy scores for summary recommendation.
    scores: dict[str, tuple[float, float]] = {}  # key -> (inter_imb, intra_lpt_avg)

    # Piecewise cost model matching WellConnectedness.chpl criterionFunction:
    #   criterionValue = floor(log10(n))
    #   n <  10  (criterionValue=0): CC only         → O(n+m)
    #   n <  100 (criterionValue=1): bridge check    → O(n+m)
    #   n >= 100 (criterionValue≥2): c_computeMinCut → O(m·log n)
    #   All clusters: loadClusterFile sort(mapper)   → O(n·log n)
    #   Total: n·log n + (n+m)          for n <  100
    #          n·log n + m·log n = (n+m)·log n  for n >= 100
    # Fast mode uses file_bytes as a cheap proxy (avoids full scan).
    def _cluster_cost(c: "ClusterInfo") -> float:
        if c.n <= 1:
            return float(c.n + c.m)
        lg = math.log2(c.n)
        if c.n < 100:
            return c.n * lg + (c.n + c.m)   # sort + linear CC/bridge
        return (c.n + c.m) * lg             # sort + VieCut mincut

    n_fn: object = (lambda c: c.file_bytes) if fast else _cluster_cost
    strategy_locale_max_n: dict[str, list[float]] = {}
    all_assignments: dict[str, dict] = {}  # cache for cross-combination analysis

    for key, (description, weight_fn) in active.items():

        # --- build assignment ---
        if key == "round_robin":
            assignment = round_robin_by_position(clusters, num_locales)
        else:
            assignment = greedy_lpt(clusters, num_locales, weight_fn)
        all_assignments[key] = assignment

        sim_w = _weight_for_strategy(key, weight_fn, fast)

        # --- inter-locale ---
        w_totals = [sum(sim_w(c) for c in assignment.get(i, []))
                    for i in range(num_locales)]
        _, mx_w, avg_w, sd_w = _stats(w_totals)
        inter_imb = (mx_w - avg_w) / avg_w if avg_w > 0 else 0.0

        # Cost-model inter imbalance: measures whether the ACTUAL algorithmic cost
        # is balanced across locales (independent of the strategy's own weight units).
        # A strategy can show 0% weight-imbalance but huge cost-imbalance if the weight
        # metric is not correlated with real compute cost (e.g. m2_over_n assigns
        # dense-small clusters cheaply to one locale, sparse-large to others).
        cost_totals = [sum(n_fn(c) for c in assignment.get(i, []))
                       for i in range(num_locales)]
        _, mx_cost, avg_cost, _ = _stats(cost_totals)
        cost_inter_imb_val = (mx_cost - avg_cost) / avg_cost if avg_cost > 0 else 0.0

        print(f"\n{'─'*88}")
        print(f"STRATEGY : {key}  [{description}]")

        print(f"\n  ── INTER-LOCALE (which clusters go to which locale) ──")
        flag = "  ← WARNING: high cost imbalance" if cost_inter_imb_val > 0.10 else ""
        print(f"  Imbalance  weight-units: {inter_imb:.2%}   cost-model: {cost_inter_imb_val:.2%}   stddev={sd_w:.0f}{flag}")
        for i in range(num_locales):
            lc = assignment.get(i, [])
            w  = sum(sim_w(c) for c in lc)
            bar_len = int(40 * w / mx_w) if mx_w > 0 else 0
            print(f"  Locale {i}: {len(lc):>7} clusters | weight={w:>14,.0f}  {'█' * bar_len}")

        print(f"\n  ── INTRA-LOCALE (core balance within each locale, {num_cores} cores, static blocking) ──")
        print(f"  {'Ordering':<24}  {'avg locale imbalance':>22}  {'worst locale':>14}  {'best locale':>12}")
        print(f"  {'─'*24}  {'─'*22}  {'─'*14}  {'─'*12}")

        intra_lpt_avg = float("inf")
        lpt_max_n_per_locale: list[float] = []

        for ord_key in ORDERINGS:
            locale_imbs = []
            for i in range(num_locales):
                lc = assignment.get(i, [])
                if ord_key == "string_sort":
                    ordered = order_string_sort(lc)
                elif ord_key == "lpt_desc":
                    ordered = order_lpt_desc(lc, sim_w)
                else:
                    ordered = order_lpt_interleaved(lc, sim_w, num_cores)
                res = simulate_static_blocking(ordered, num_cores, sim_w)
                locale_imbs.append(res["imbalance_pct"])

                if ord_key == "lpt_interleaved":
                    # Also measure max core weight in n-units (the real compute proxy)
                    # for calibration-based time prediction.
                    res_n = simulate_static_blocking(ordered, num_cores, n_fn)
                    lpt_max_n_per_locale.append(res_n["max"])

            avg_i = sum(locale_imbs) / len(locale_imbs)
            worst = max(locale_imbs)
            best  = min(locale_imbs)
            if ord_key == "lpt_interleaved":
                intra_lpt_avg = avg_i
            marker = "  ←" if ord_key == "lpt_interleaved" else ""
            print(f"  {ord_key:<24}  avg={avg_i:>7.3%}  max={worst:>7.3%}  "
                  f"|  worst={worst:>7.3%}  best={best:>7.3%}{marker}")

        strategy_locale_max_n[key] = lpt_max_n_per_locale
        scores[key] = (inter_imb, intra_lpt_avg, cost_inter_imb_val)

    # --- Cross-combination analysis ---
    # For each (inter, intra) pair: simulate inter assignment, then within each
    # locale's specific subset simulate intra ordering, measure max core weight
    # in n-units.  This captures the inter/intra INTERACTION that the single-
    # strategy analysis misses: a subset assigned by one inter strategy may have
    # a different cluster size distribution that changes which intra strategy wins.
    #
    # Require BOTH filters to pass:
    #   1. weight-unit inter imbalance ≤ 5%  (LPT is working in its own metric)
    #   2. cost-model inter imbalance  ≤ 10% (the assignment is balanced in actual cost)
    # Filter 2 catches m2_over_n (balances in m²/n but puts cheap dense-small clusters
    # on one locale and expensive sparse-large clusters on others → 50% cost imbalance).
    # Filter 1 catches round_robin (5.6% weight imbalance, correctly excluded).
    def _eligible(k: str) -> bool:
        return scores[k][0] <= 0.05 and scores[k][2] <= 0.10
    eligible_inter = [k for k in active if _eligible(k)]
    if not eligible_inter:
        eligible_inter = [k for k in active if scores[k][2] <= 0.20]
    if not eligible_inter:
        eligible_inter = list(active.keys())
    intra_keys_x = [k for k in active if k != "round_robin"]

    cross: dict[tuple[str, str], tuple[float, list[float]]] = {}
    for inter_k in eligible_inter:
        asgn = all_assignments[inter_k]
        for intra_k in intra_keys_x:
            _, intra_fn_x = active[intra_k]
            intra_w_x = _weight_for_strategy(intra_k, intra_fn_x, fast)
            locale_scores_x: list[float] = []
            for i in range(num_locales):
                lc = asgn.get(i, [])
                ordered = order_lpt_interleaved(lc, intra_w_x, num_cores)
                res_n = simulate_static_blocking(ordered, num_cores, n_fn)
                locale_scores_x.append(res_n["max"])
            cross[(inter_k, intra_k)] = (max(locale_scores_x), locale_scores_x)

    sorted_cross = sorted(cross.items(), key=lambda x: x[1][0])
    best_wall_x = sorted_cross[0][1][0] if sorted_cross else 0.0

    # --- Summary ---
    eligible = {k: v for k, v in scores.items() if v[2] <= 0.10}
    if not eligible:
        eligible = scores
    best_key = min(eligible, key=lambda k: eligible[k][1])
    best_inter_imb, best_intra_imb, best_cost_imb = eligible[best_key]

    best_combo = sorted_cross[0][0] if sorted_cross else (best_key, best_key)
    best_inter_x, best_intra_x = best_combo

    n_label = "bytes" if fast else "cost-units"

    print(f"\n{'='*88}")
    print(f"\nCROSS-COMBINATION ANALYSIS  (inter × intra, measured via lpt_interleaved)")
    print(f"  Unlike per-strategy analysis, this tests EVERY (inter, intra) pair.")
    print(f"  Piecewise cost model (matches criterionFunction in WellConnectedness.chpl):")
    print(f"    n <  100 : n·log₂n + (n+m)        [sort + CC/bridge, no mincut]")
    print(f"    n >= 100 : (n+m)·log₂n             [sort + c_computeMinCut VieCut]")
    print(f"  Eligible inter strategies: weight imbalance ≤ 5% AND cost imbalance ≤ 10%")
    print(f"    (filters round_robin/m2_over_n/m*n which skew actual cost distribution)")
    print(f"  {'Strategy':<14}  {'weight-imb':>10}  {'cost-imb':>10}  eligible?")
    for k in active:
        wi = scores[k][0]; ci = scores[k][2]
        ok = "yes" if (wi <= 0.05 and ci <= 0.10) else "NO  ← excluded"
        print(f"  {k:<14}  {wi:>10.2%}  {ci:>10.2%}  {ok}")
    print()
    print(f"  {'Rank':<5} {'Inter':<13} {'Intra':<13} {'Score':>12}  {'vs best':>8}  Locale scores ({n_label})")
    print(f"  {'─'*5} {'─'*13} {'─'*13} {'─'*12}  {'─'*8}  {'─'*52}")
    for rank, ((inter_k, intra_k), (wall_n, loc_sc)) in enumerate(sorted_cross[:15], 1):
        vs_best = (wall_n - best_wall_x) / best_wall_x if best_wall_x > 0 else 0.0
        loc_str = "  ".join(f"L{i}:{s:,.0f}" for i, s in enumerate(loc_sc))
        marker = "  ← BEST" if rank == 1 else ""
        print(f"  {rank:<5} {inter_k:<13} {intra_k:<13} {wall_n:>12,.0f}  {vs_best:>+7.1%}  {loc_str}{marker}")

    print(f"\n{'='*88}")
    print(f"\nSUMMARY")
    print(f"  Strategies excluded from cross-combo (weight imbalance > 5% OR cost imbalance > 10%):")
    excl = [k for k, v in scores.items() if v[0] > 0.05 or v[2] > 0.10]
    print(f"    {excl or 'none'}")
    print(f"\n  Best single strategy (same inter+intra) : '{best_key}'")
    print(f"    inter-locale imbalance : {best_inter_imb:.2%}  (cost-model: {best_cost_imb:.2%})")
    print(f"    intra-locale imbalance (lpt_interleaved, global) : {best_intra_imb:.2%}")
    print(f"\n  Best cross-combination : inter='{best_inter_x}' + intra='{best_intra_x}'")
    print(f"    wall score : {best_wall_x:,.0f} {n_label}  "
          f"({'same' if best_inter_x == best_intra_x else 'DIFFERENT'} inter/intra strategies)")
    dist_inter = best_inter_x if best_inter_x != "round_robin" else "n"
    dist_intra = best_intra_x if best_intra_x != "round_robin" else "n"
    print(f"\n  Recommended distribute command:")
    print(f"    python extract_subgraphs_with_distribution.py distribute <flat_dir> <dist_dir> \\")
    print(f"        --num_locales {num_locales} --num_cores {num_cores} \\")
    print(f"        --inter_strategy {dist_inter} --intra_strategy {dist_intra}")
    print(f"  (use --inter_strategy / --intra_strategy independently to test combinations)")
    print()

    # --- Top 10 to test empirically ---
    # Pick top combinations from the cross-combination ranking while enforcing
    # diversity: at most 2 entries per inter strategy so the list covers a range
    # of inter approaches rather than being dominated by one.
    SIMPLE = {"n", "m", "n+m"}  # strategies simple enough to generalise across datasets

    seen_inter: dict[str, int] = {}
    top10: list[tuple[str, str, float]] = []
    for (ik, ak), (sc, _) in sorted_cross:
        if seen_inter.get(ik, 0) < 2:
            top10.append((ik, ak, sc))
            seen_inter[ik] = seen_inter.get(ik, 0) + 1
        if len(top10) == 10:
            break

    # Simple-strategy shortlist: best combination where BOTH inter and intra
    # are from {n, m, n+m}.  These generalise across datasets better than
    # complex formulas like n_log_n_m which may overfit one distribution.
    simple_cross = [(combo, data) for combo, data in sorted_cross
                    if combo[0] in SIMPLE and combo[1] in SIMPLE]
    simple_best = simple_cross[0] if simple_cross else None

    print(f"{'='*88}")
    print(f"\nTOP 10 COMBINATIONS TO TEST EMPIRICALLY")
    if strategy_whitelist:
        print(f"  (Restricted to --strategies: {', '.join(strategy_whitelist)})")
    print(f"  Sorted by simulation score (lower = better predicted wall time).")
    print(f"  At most 2 per inter strategy to ensure diverse coverage.")
    print(f"  Note: all scores are within ~0.5% — empirical node variance will dominate.")
    print(f"  Replace <flat_dir> / <dist_dir> with your actual paths.\n")
    for rank, (ik, ak, sc) in enumerate(top10, 1):
        di = ik if ik != "round_robin" else "n"
        da = ak if ak != "round_robin" else "n"
        vs_best = (sc - top10[0][2]) / top10[0][2] if top10[0][2] > 0 else 0.0
        simple_tag = "  [SIMPLE]" if (ik in SIMPLE and ak in SIMPLE) else ""
        print(f"  #{rank:>2}  inter={ik:<13} intra={ak:<13}  score={sc:>12,.0f}  vs best={vs_best:>+5.2%}{simple_tag}")
        print(f"       python extract_subgraphs_with_distribution.py distribute <flat_dir> <dist_dir> \\")
        print(f"           --num_locales {num_locales} --num_cores {num_cores} \\")
        print(f"           --inter_strategy {di} --intra_strategy {da}")
        print()

    if simple_best and not strategy_whitelist:
        (sik, sak), (ssc, _) = simple_best
        vs_overall = (ssc - top10[0][2]) / top10[0][2] if top10[0][2] > 0 else 0.0
        print(f"  BEST SIMPLE COMBINATION (inter+intra both from {{n, m, n+m}})")
        print(f"  Recommended for multi-dataset use: generalises better than complex formulas.")
        print(f"  inter={sik}  intra={sak}  score={ssc:,.0f}  vs overall best={vs_overall:>+5.2%}")
        print(f"  python extract_subgraphs_with_distribution.py distribute <flat_dir> <dist_dir> \\")
        print(f"      --num_locales {num_locales} --num_cores {num_cores} \\")
        print(f"      --inter_strategy {sik} --intra_strategy {sak}")
        print(f"  Tip: re-run with --strategies n,m,n+m to see only simple combinations.")
        print()

    print(f"{'='*88}")
    print()


    if calibration_times is None:
        return
    if len(calibration_times) != num_locales:
        print(f"Warning: --calibration_times has {len(calibration_times)} values "
              f"but num_locales={num_locales}. Skipping prediction.")
        return
    if calibration_strategy not in strategy_locale_max_n:
        print(f"Warning: calibration_strategy='{calibration_strategy}' was not analysed "
              f"(excluded in fast mode?). Skipping prediction.")
        return

    cal_max_n    = strategy_locale_max_n[calibration_strategy]
    n_unit_label = "bytes" if fast else "vertex-units"

    # Per-locale efficiency: how many n-units does each node process per second?
    # Derived from the actual calibration run times.
    # Captures GPFS I/O latency, NUMA topology, OS scheduler, any node-level variance —
    # everything that affects wall time but isn't visible to the simulation.
    efficiencies = [
        cal_max_n[i] / calibration_times[i] if calibration_times[i] > 0 else 1.0
        for i in range(num_locales)
    ]
    cal_wall = max(calibration_times)

    print(f"{'='*88}")
    print(f"RUNTIME PREDICTION")
    print(f"  Chapel execution model : coforall over {num_locales} locales (fully parallel)")
    print(f"                           forall over files — static {num_cores}-chunk blocking per locale")
    print(f"                           wall time = slowest locale (bottleneck)")
    print(f"  Wulver calibration     : per-node {n_unit_label}/sec from actual run")
    print(f"                           captures GPFS open latency, NUMA, node load")
    print(f"  Calibration run        : strategy='{calibration_strategy}', "
          f"locale times=[{', '.join(f'{t:.2f}s' for t in calibration_times)}]")
    print(f"  Note: file listing (~0.3s) and output writing (~0s) excluded — "
          f"constant across strategies")
    print()
    print(f"  Per-locale node speed ({n_unit_label}/sec):")
    for i in range(num_locales):
        print(f"    Locale {i}: {efficiencies[i]:>12,.0f}  "
              f"(calibrated from {calibration_times[i]:.2f}s actual)")
    print()

    # Prediction table
    col = 8
    header = (f"  {'Strategy':<15} | " +
              " | ".join(f"{'Locale '+str(i):>{col}}" for i in range(num_locales)) +
              f" | {'Wall':>{col}} | {'vs cal':>8}")
    sep = "  " + "─" * 15 + "─┼─" + "─┼─".join("─" * col for _ in range(num_locales)) + \
          "─┼─" + "─" * col + "─┼─" + "─" * 8
    print(header)
    print(sep)

    pred_walls: dict[str, float] = {}
    for key, max_n_list in strategy_locale_max_n.items():
        pred_times = [
            max_n_list[i] / efficiencies[i] if efficiencies[i] > 0 else 0.0
            for i in range(num_locales)
        ]
        wall = max(pred_times)
        pred_walls[key] = wall
        delta = (wall - cal_wall) / cal_wall if cal_wall > 0 else 0.0
        delta_str = f"{delta:+.1%}"
        times_str = " | ".join(f"{t:>{col}.1f}s" for t in pred_times)
        cal_marker = "  <- calibration" if key == calibration_strategy else ""
        print(f"  {key:<15} | {times_str} | {wall:>{col}.1f}s | {delta_str:>8}{cal_marker}")

    print()
    fastest = min(pred_walls, key=lambda k: pred_walls[k])
    print(f"  Fastest predicted (same strategy) : '{fastest}' → {pred_walls[fastest]:.1f}s wall time  "
          f"({(pred_walls[fastest]-cal_wall)/cal_wall:+.1%} vs calibration)")

    # Cross-combination runtime predictions (top 10)
    if sorted_cross:
        print()
        print(f"  Cross-combination predictions (top 10 by score):")
        ccol = 10
        cc_header = (f"  {'Inter':<13} {'Intra':<13} | " +
                     " | ".join(f"{'L'+str(i):>{ccol}}" for i in range(num_locales)) +
                     f" | {'Wall':>{ccol}} | {'vs cal':>8}")
        cc_sep = ("  " + "─"*13 + " " + "─"*13 + "─┼─" +
                  "─┼─".join("─"*ccol for _ in range(num_locales)) +
                  "─┼─" + "─"*ccol + "─┼─" + "─"*8)
        print(cc_header)
        print(cc_sep)
        cross_pred_walls: list[tuple[float, str, str]] = []
        for (inter_k, intra_k), (_, loc_sc) in sorted_cross[:10]:
            pred_times_x = [
                loc_sc[i] / efficiencies[i] if efficiencies[i] > 0 else 0.0
                for i in range(num_locales)
            ]
            wall_x = max(pred_times_x)
            cross_pred_walls.append((wall_x, inter_k, intra_k))
            delta_x = (wall_x - cal_wall) / cal_wall if cal_wall > 0 else 0.0
            times_str_x = " | ".join(f"{t:>{ccol}.1f}s" for t in pred_times_x)
            print(f"  {inter_k:<13} {intra_k:<13} | {times_str_x} | {wall_x:>{ccol}.1f}s | {delta_x:>+7.1%}")
        cross_pred_walls.sort()
        best_xw, best_xi, best_xo = cross_pred_walls[0]
        print()
        print(f"  Fastest predicted (cross-combination) : inter='{best_xi}' + intra='{best_xo}' "
              f"→ {best_xw:.1f}s  ({(best_xw-cal_wall)/cal_wall:+.1%} vs calibration)")
    print()


# ---------------------------------------------------------------------------
# 7.  Distribute clusters into per-locale subfolders
# ---------------------------------------------------------------------------

def distribute_clusters(cluster_dir: str, output_base: str,
                        num_locales: int, num_cores: int,
                        inter_strategy: str,
                        intra_strategy: str,
                        fast: bool = True,
                        use_symlinks: bool = True) -> None:
    """
    Assign cluster files to locale_0/.., locale_{N-1}/ subfolders.

    inter_strategy  controls WHICH clusters go to which locale
                    (greedy LPT by that weight — minimises makespan across locales).
    intra_strategy  controls the seq_NNNNNNN_ ordering WITHIN each locale folder
                    (lpt_interleaved by that weight — minimises static-blocking
                    imbalance across the 64 cores inside each locale).

    Both can differ — e.g. --inter_strategy n --intra_strategy sqrt_nm.

    File naming inside locale folders:
        seq_NNNNNNN_cluster_ORIGINAL_ID.tsv

    String sort of seq_ prefix recreates lpt_interleaved order in Chapel.
    Chapel auto-detects locale_0/ and uses the pre-distributed path.
    """
    for label, strat in [("inter", inter_strategy), ("intra", intra_strategy)]:
        if strat not in WEIGHT_FUNCTIONS:
            print(f"Unknown {label}_strategy '{strat}'. Choices: {list(WEIGHT_FUNCTIONS.keys())}")
            return

    inter_desc, inter_fn = WEIGHT_FUNCTIONS[inter_strategy]
    intra_desc, intra_fn = WEIGHT_FUNCTIONS[intra_strategy]

    need_full = (inter_strategy in NEEDS_FULL_SCAN or
                 intra_strategy in NEEDS_FULL_SCAN)
    actual_fast = fast and not need_full

    print(f"Scanning {cluster_dir} ...")
    if actual_fast:
        print("  (fast mode: using file size as weight proxy)")
    clusters = scan_cluster_stats(cluster_dir, fast=actual_fast, verbose=True)
    if not clusters:
        print("No cluster_*.tsv files found.")
        return

    print(f"Found {len(clusters)} clusters.")
    print(f"Inter-locale strategy : {inter_strategy}  [{inter_desc}]")
    print(f"Intra-locale strategy : {intra_strategy}  [{intra_desc}]")

    inter_w = _weight_for_strategy(inter_strategy, inter_fn, actual_fast)
    intra_w = _weight_for_strategy(intra_strategy, intra_fn, actual_fast)

    if inter_strategy == "round_robin":
        assignment = round_robin_by_position(clusters, num_locales)
    else:
        assignment = greedy_lpt(clusters, num_locales,
                                inter_fn if not actual_fast else inter_w)

    import shutil
    for loc_id in range(num_locales):
        locale_dir = os.path.join(output_base, f"locale_{loc_id}")
        os.makedirs(locale_dir, exist_ok=True)
        lc = assignment.get(loc_id, [])

        # LPT interleaved by intra_w: string sort of seq_ prefix recreates this
        # order in Chapel so each core gets a balanced mix of heavy/light clusters.
        ordered = order_lpt_interleaved(lc, intra_w, num_cores)

        for seq, c in enumerate(ordered):
            seq_name = f"seq_{seq:07d}_cluster_{c.cluster_id}.tsv"
            target   = os.path.join(locale_dir, seq_name)
            if os.path.exists(target) or os.path.islink(target):
                os.remove(target)
            if use_symlinks:
                os.symlink(c.filepath, target)
            else:
                shutil.copy2(c.filepath, target)

        w_inter = sum(inter_w(c) for c in lc)
        w_intra = sum(intra_w(c) for c in lc)
        print(f"  Locale {loc_id}: {len(lc):>7} clusters | "
              f"inter_w={w_inter:>14,.0f}  intra_w={w_intra:>14,.0f}  -> {locale_dir}")

    w_totals = [sum(inter_w(c) for c in assignment.get(i, [])) for i in range(num_locales)]
    _, mx_w, avg_w, _ = _stats(w_totals)
    inter_imb = (mx_w - avg_w) / avg_w if avg_w > 0 else 0.0
    print(f"\nPredicted inter-locale imbalance ({inter_strategy}) : {inter_imb:.2%}")
    print(f"Point Chapel inputFolderPath to  : {output_base}")
    print("Done.")


# ---------------------------------------------------------------------------
# 8.  CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = parser.add_subparsers(dest="mode", required=True)

    # split
    sp = sub.add_parser("split",
        help="Split a combined TSV file into cluster_N.tsv files.")
    sp.add_argument("input_file",
        help="Combined TSV with '-' line separators (e.g. au249's bitcoin_1_0.tsv).")
    sp.add_argument("--output_dir", default=".",
        help="Output directory for cluster_N.tsv files (default: current dir).")

    # analyze
    ap = sub.add_parser("analyze",
        help="Report inter-locale and intra-locale balance for all strategies.")
    ap.add_argument("cluster_dir",
        help="Directory containing cluster_*.tsv files.")
    ap.add_argument("--num_locales", type=int, default=4,
        help="Number of locales to simulate (default: 4).")
    ap.add_argument("--num_cores", type=int, default=64,
        help="Cores per locale for intra-locale simulation (default: 64).")
    ap.add_argument("--fast", action="store_true",
        help="Use file size as weight proxy instead of parsing n and m. "
             "Runs in seconds instead of minutes. Skips n/m-based strategies.")
    ap.add_argument("--calibration_times", default=None,
        help="Comma-separated actual Chapel wall times per locale from a prior run, "
             "in locale order 0..N-1. Example: --calibration_times 28.68,22.42,29.47,16.95 "
             "Enables the RUNTIME PREDICTION table at the end of the report.")
    ap.add_argument("--calibration_strategy", default="n",
        choices=list(WEIGHT_FUNCTIONS.keys()),
        help="Which strategy was used in the calibration run (default: n).")
    ap.add_argument("--strategies", default=None,
        help="Comma-separated whitelist of strategies to analyse, e.g. n,m,n+m  "
             "Restricts both per-strategy output and cross-combination table. "
             "Useful for multi-dataset comparison with simple generalizable strategies.")

    # distribute
    dp = sub.add_parser("distribute",
        help="Create locale_0/.., locale_N-1/ subfolders with chosen strategy.")
    dp.add_argument("cluster_dir",
        help="Flat directory containing cluster_*.tsv files.")
    dp.add_argument("output_base",
        help="Base directory; locale_0/, locale_1/, ... will be created here.")
    dp.add_argument("--num_locales", type=int, default=4,
        help="Number of locales (default: 4).")
    dp.add_argument("--num_cores", type=int, default=64,
        help="Cores per locale for intra-locale LPT ordering (default: 64).")
    dp.add_argument("--strategy", default="n",
        choices=list(WEIGHT_FUNCTIONS.keys()),
        help="Sets both inter and intra strategy (default: n). "
             "Overridden by --inter_strategy / --intra_strategy.")
    dp.add_argument("--inter_strategy", default=None,
        choices=list(WEIGHT_FUNCTIONS.keys()),
        help="Weight for greedy LPT inter-locale assignment. "
             "Overrides --strategy for inter step.")
    dp.add_argument("--intra_strategy", default=None,
        choices=list(WEIGHT_FUNCTIONS.keys()),
        help="Weight for lpt_interleaved ordering within each locale folder. "
             "Overrides --strategy for intra step.")
    dp.add_argument("--fast", action="store_true",
        help="Use file size as weight proxy (skips full n/m scan). "
             "Forces both strategies to 'bytes'.")
    dp.add_argument("--copy", action="store_true",
        help="Copy files instead of symlinking (no extra disk usage with symlinks).")

    args = parser.parse_args()

    if args.mode == "split":
        split_clusters(args.input_file, args.output_dir)

    elif args.mode == "analyze":
        clusters = scan_cluster_stats(args.cluster_dir, fast=args.fast, verbose=True)
        if not clusters:
            print("No cluster_*.tsv files found.")
            return
        cal_times = None
        if args.calibration_times:
            try:
                cal_times = [float(x) for x in args.calibration_times.split(",")]
            except ValueError:
                print("Error: --calibration_times must be comma-separated floats, "
                      "e.g. 28.68,22.42,29.47,16.95")
                return
        whitelist = [s.strip() for s in args.strategies.split(",") if s.strip()] \
                    if args.strategies else None
        print_distribution_report(clusters, args.num_locales, args.num_cores, args.fast,
                                   calibration_times=cal_times,
                                   calibration_strategy=args.calibration_strategy,
                                   strategy_whitelist=whitelist)

    elif args.mode == "distribute":
        if args.fast:
            inter_strat = intra_strat = "bytes"
        else:
            inter_strat = args.inter_strategy or args.strategy
            intra_strat = args.intra_strategy or args.strategy
        distribute_clusters(
            cluster_dir=args.cluster_dir,
            output_base=args.output_base,
            num_locales=args.num_locales,
            num_cores=args.num_cores,
            inter_strategy=inter_strat,
            intra_strategy=intra_strat,
            fast=args.fast,
            use_symlinks=not args.copy,
        )


if __name__ == "__main__":
    main()