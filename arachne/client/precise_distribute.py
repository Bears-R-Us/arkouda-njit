#!/usr/bin/env python3
"""
precise_distribute.py  - scan flat cluster dir(s) ONCE each, then distribute
using multiple strategies from the exact same n/m data.

This guarantees a 100% fair comparison: every strategy sees identical vertex
and edge counts, so differences in locale assignment come purely from the
strategy logic, not from GPFS read-order variation or timing.

Workflow (per dataset):
  1. Scan all cluster_*.tsv files once (reads every file to count n and m).
  2. Apply each (inter, intra) strategy to the same ClusterInfo list.
  3. Write symlinks into separate output dirs, one per strategy.

Batch mode (no positional args)
Scans DST_BASE for all flat dirs named 001, 0001, 001_flat, 0001_flat etc.
Output goes to DST_BASE/<dataset>/<thresh>_precise/<strategy_name>/locale_N/

    python precise_distribute.py
    python precise_distribute.py --only bitcoin,hyves
    python precise_distribute.py --skip_existing
    python precise_distribute.py --dry_run

Single-dir mode (explicit paths)
    python precise_distribute.py <flat_dir> <output_base>
    python precise_distribute.py /scratch/.../bitcoin/0001_flat /scratch/.../bitcoin/0001_precise

Common options
    --num_locales 4 --num_cores 32
    --strategies mlogn_m2n,n_n,npm_npm   # subset of registry
    --strategies_raw "m_log_n:m2_over_n,n:n"  # ad-hoc inter:intra pairs
    --fast         # skip file reads — use byte size as weight proxy (10-100× faster)
    --copy          # copy files instead of symlinking
    --list_strategies

Strategies (7 in registry):
  mlogn_m2n   m_log_n        m2_over_n   ★ recommended — wins 4/19 datasets
  n_n         n              n           best simple — 4/9 simple-eligible wins
  m_m         m              m           simple — wins cit_patents ×2
  npm_npm     n+m            n+m         symmetric — n+m inter wins wiki_links/0001
  m_m2n       m              m2_over_n   mixed — m2_over_n intra in 7/19 winners
  rr          round_robin    n+m         plain round-robin (replicates Chapel default)
  rr_npm      sorted_rr_npm  n+m         sorted round-robin — deals clusters like cards;
                                         each locale gets proportional heavy+light mix;
                                         designed to fix LPT's one-giant-per-locale problem
"""

from __future__ import annotations

import os
import sys
import math
import heapq
import shutil
import argparse
import time
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path

# ---------------------------------------------------------------------------
# Import weight functions and ClusterInfo from the sibling script
# ---------------------------------------------------------------------------
# DST_BASE is set from CLI --dst_base (batch mode only).  No default is hard-coded
# so the script works on any system without modification.
DST_BASE: Path | None = None

_here = Path(__file__).parent
sys.path.insert(0, str(_here))
from extract_subgraphs_with_distribution import (
    ClusterInfo,
    WEIGHT_FUNCTIONS,
    NEEDS_FULL_SCAN,
    scan_cluster_stats,
    greedy_lpt,
    round_robin_by_position,
    order_lpt_interleaved,
    _weight_for_strategy,
)


# ---------------------------------------------------------------------------
# Sorted round-robin inter assignment
# ---------------------------------------------------------------------------

# Maps the "sorted_rr_*" inter key used in Strategy.inter to the underlying
# WEIGHT_FUNCTIONS key used to sort clusters before dealing them round-robin.
_SORTED_RR_WEIGHT: dict[str, str] = {
    "sorted_rr_npm": "n+m",
    "sorted_rr_n":   "n",
    "sorted_rr_m":   "m",
}


def sorted_round_robin(
    clusters: list[ClusterInfo],
    num_locales: int,
    weight_fn,
) -> dict[int, list[ClusterInfo]]:
    """
    Sort clusters by weight descending, then deal like cards:
      locale 0 gets ranks 0, L, 2L, ...
      locale 1 gets ranks 1, L+1, 2L+1, ...
    Each locale gets a proportional mix of heavy AND light clusters,
    avoiding the LPT problem of dumping one giant onto a single locale.
    """
    sorted_c = sorted(clusters, key=weight_fn, reverse=True)
    result: dict[int, list[ClusterInfo]] = defaultdict(list)
    for idx, c in enumerate(sorted_c):
        result[idx % num_locales].append(c)
    return dict(result)


# ---------------------------------------------------------------------------
# Strategy registry
# ---------------------------------------------------------------------------
@dataclass
class Strategy:
    inter: str
    intra: str
    description: str
    recommended: bool = False


REGISTRY: dict[str, Strategy] = {
    "mlogn_m2n": Strategy("m_log_n",      "m2_over_n",
                          "m·log n matches O(m log n) mincut cost",
                          recommended=True),
    "n_n":       Strategy("n",            "n",
                          "best simple — wins 4/9 simple-eligible datasets"),
    "m_m":       Strategy("m",            "m",
                          "simple — edge-count for both; wins cit_patents ×2"),
    "npm_npm":   Strategy("n+m",          "n+m",
                          "simple symmetric — vertices+edges for both inter and intra; "
                          "n+m inter wins wiki_links/0001 overall"),
    "m_m2n":     Strategy("m",            "m2_over_n",
                          "mixed — edge inter, dense-graph-biased intra; "
                          "m2_over_n intra appears in 7/19 overall winners"),
    # Round-robin variants
    "rr":        Strategy("round_robin",  "n+m",
                          "plain round-robin by filename sort — replicates Chapel default; "
                          "zero sort overhead, ignores cluster size"),
    "rr_npm":    Strategy("sorted_rr_npm", "n+m",
                          "sorted round-robin — sort by n+m desc then deal like cards; "
                          "each locale gets a proportional mix of heavy+light clusters; "
                          "fixes LPT's one-giant-per-locale problem"),
}

DEFAULT_NAMES = list(REGISTRY.keys())


# ---------------------------------------------------------------------------
# Batch: find all flat dirs in DST_BASE
# ---------------------------------------------------------------------------

def find_flat_dirs(only: set[str] | None) -> list[tuple[str, str, Path, Path]]:
    """
    Scan DST_BASE for dirs containing cluster_*.tsv files.
    Handles both 'thresh' and 'thresh_flat' naming conventions.
    Returns (ds, thresh, flat_dir, output_base) tuples where
    output_base = DST_BASE / ds / f"{thresh}_precise".
    """
    results: list[tuple[str, str, Path, Path]] = []
    seen: set[tuple[str, str]] = set()

    if not DST_BASE.is_dir():
        print(f"ERROR: DST_BASE not found: {DST_BASE}")
        return results

    for ds_dir in sorted(DST_BASE.iterdir()):
        if not ds_dir.is_dir():
            continue
        ds = ds_dir.name
        if only and ds not in only:
            continue
        for sub in sorted(ds_dir.iterdir()):
            if not sub.is_dir():
                continue
            name = sub.name
            # Skip already-processed dirs
            if any(name.endswith(s) for s in ("_precise", "_dist", "_distributed")):
                continue
            if "_dist_" in name:
                continue
            # Canonical thresh: strip _flat suffix
            thresh = name[:-5] if name.endswith("_flat") else name
            if (ds, thresh) in seen:
                continue
            # Must contain at least one cluster file
            if not next(sub.glob("cluster_*.tsv"), None):
                continue
            output_base = DST_BASE / ds / f"{thresh}_precise"
            results.append((ds, thresh, sub, output_base))
            seen.add((ds, thresh))

    return results


# ---------------------------------------------------------------------------
# Core: assign + write symlinks from a pre-scanned ClusterInfo list
# ---------------------------------------------------------------------------

def write_distribution(
    clusters: list[ClusterInfo],
    out_dir: Path,
    inter: str,
    intra: str,
    num_locales: int,
    num_cores: int,
    use_symlinks: bool,
    skip_existing: bool,
    fast: bool = False):
    """
    Apply one (inter, intra) strategy to `clusters` and write locale_N/ dirs.
    When fast=True, clusters were scanned with fast=True so n=0/m=0 and
    file_bytes is used as the weight proxy throughout.
    """
    if skip_existing and (out_dir / "locale_0").is_dir():
        print(f"    SKIP — locale_0/ already exists in {out_dir.name}/")
        return

    # Intra weight.
    _, intra_fn = WEIGHT_FUNCTIONS[intra]
    intra_w = _weight_for_strategy(intra, intra_fn, fast=fast)

    # Inter assignment — three families:
    if inter == "round_robin":
        assignment = round_robin_by_position(clusters, num_locales)
        # Use n+m (or bytes in fast mode) for the imbalance display only.
        _, _w = WEIGHT_FUNCTIONS["n+m"]
        inter_w = _weight_for_strategy("n+m", _w, fast=fast)
    elif inter in _SORTED_RR_WEIGHT:
        wkey = _SORTED_RR_WEIGHT[inter]
        _, _w = WEIGHT_FUNCTIONS[wkey]
        inter_w = _weight_for_strategy(wkey, _w, fast=fast)
        assignment = sorted_round_robin(clusters, num_locales, inter_w)
    else:
        _, inter_fn = WEIGHT_FUNCTIONS[inter]
        inter_w = _weight_for_strategy(inter, inter_fn, fast=fast)
        assignment = greedy_lpt(clusters, num_locales, inter_w)

    for loc_id in range(num_locales):
        locale_dir = out_dir / f"locale_{loc_id}"
        locale_dir.mkdir(parents=True, exist_ok=True)
        lc = assignment.get(loc_id, [])
        ordered = order_lpt_interleaved(lc, intra_w, num_cores)

        for seq, c in enumerate(ordered):
            seq_name = f"seq_{seq:07d}_cluster_{c.cluster_id}.tsv"
            target = locale_dir / seq_name
            if target.exists() or target.is_symlink():
                target.unlink()
            if use_symlinks:
                target.symlink_to(c.filepath)
            else:
                shutil.copy2(c.filepath, str(target))

    # Print per-locale weight summary
    w_totals = [sum(inter_w(c) for c in assignment.get(i, [])) for i in range(num_locales)]
    mx = max(w_totals)
    avg = sum(w_totals) / num_locales
    imb = (mx - avg) / avg if avg > 0 else 0.0
    counts = [len(assignment.get(i, [])) for i in range(num_locales)]
    print(f"    inter imbalance: {imb:.2%}  |  "
          f"clusters per locale: {min(counts):,}–{max(counts):,}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def resolve_strategies(args, ap) -> list[tuple[str, Strategy]]:
    strategy_items: list[tuple[str, Strategy]] = []
    if args.strategies_raw:
        for i, entry in enumerate(args.strategies_raw.split(",")):
            parts = entry.strip().split(":")
            if len(parts) != 2:
                ap.error(f"Bad --strategies_raw entry '{entry}': expected inter:intra")
            inter, intra = parts[0].strip(), parts[1].strip()
            if inter not in WEIGHT_FUNCTIONS:
                ap.error(f"Unknown inter strategy '{inter}'")
            if intra not in WEIGHT_FUNCTIONS:
                ap.error(f"Unknown intra strategy '{intra}'")
            strategy_items.append((f"custom{i+1}",
                                   Strategy(inter, intra, f"custom: inter={inter} intra={intra}")))
    elif args.strategies:
        for n in args.strategies.split(","):
            n = n.strip()
            if n not in REGISTRY:
                ap.error(f"Unknown strategy '{n}'. Run --list_strategies to see options.")
            strategy_items.append((n, REGISTRY[n]))
    else:
        strategy_items = [(n, s) for n, s in REGISTRY.items()]
    return strategy_items


def process_one(flat_dir: Path, output_base: Path,
                strategy_items: list[tuple[str, Strategy]],
                num_locales: int, num_cores: int,
                use_symlinks: bool, skip_existing: bool, dry_run: bool,
                fast: bool = False) -> None:
    """Scan flat_dir once and write all strategy distributions."""
    print(f"\n  {'Name':<14} {'Inter':<14} {'Intra':<14} Output dir")
    print(f"  {'─'*14} {'─'*14} {'─'*14} {'─'*40}")
    for n, s in strategy_items:
        star = "★" if s.recommended else " "
        print(f"  {n:<14} {s.inter:<14} {s.intra:<14} {star} {output_base.name}/{n}/")

    if dry_run:
        for name, strat in strategy_items:
            out_dir = output_base / name
            print(f"\n    [{name}]  inter={strat.inter}  intra={strat.intra}")
            print(f"    [dry_run] would write to {out_dir}/")
        return

    if skip_existing:
        pending = [(n, s) for n, s in strategy_items
                   if not (output_base / n / "locale_0").is_dir()]
        skipped = len(strategy_items) - len(pending)
        if skipped:
            print(f"\n  Skipping {skipped} already-done strategy/strategies (locale_0/ exists).")
        if not pending:
            print("  All strategies already distributed — nothing to do.")
            return
        strategy_items = pending

    if fast:
        print(f"\n  Scanning {flat_dir.name}/ — fast mode (file bytes as weight proxy) ...")
    else:
        print(f"\n  Scanning {flat_dir.name}/ — reads every file for exact n and m ...")
    t0 = time.perf_counter()
    clusters = scan_cluster_stats(str(flat_dir), fast=fast, verbose=True)
    scan_elapsed = time.perf_counter() - t0

    if not clusters:
        print("  No cluster_*.tsv files found — skipping.")
        return

    if fast:
        total_bytes = sum(c.file_bytes for c in clusters)
        print(f"\n  Scan done in {scan_elapsed:.1f}s — "
              f"{len(clusters):,} clusters | {total_bytes/1e9:.2f} GB total")
    else:
        total_n = sum(c.n for c in clusters)
        total_m = sum(c.m for c in clusters)
        print(f"\n  Scan done in {scan_elapsed:.1f}s — "
              f"{len(clusters):,} clusters | {total_n:,} vertices | {total_m:,} edges")
    print(f"  Distributing (all {len(strategy_items)} strategies share this scan):")

    for name, strat in strategy_items:
        out_dir = output_base / name
        print(f"\n    [{name}]  inter={strat.inter}  intra={strat.intra}")
        t1 = time.perf_counter()
        write_distribution(clusters, out_dir, strat.inter, strat.intra,
                           num_locales, num_cores, use_symlinks, skip_existing, fast=fast)
        elapsed = time.perf_counter() - t1
        print(f"    done in {elapsed:.1f}s  →  {out_dir}/")


def main():
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("flat_dir",   nargs="?", default=None,
        help="(Single-dir mode) Directory containing cluster_*.tsv files. "
             "Omit to run in batch mode scanning --dst_base.")
    ap.add_argument("output_base", nargs="?", default=None,
        help="(Single-dir mode) Base output dir; one subdir per strategy created here.")
    ap.add_argument("--dst_base", default=None,
        help="(Batch mode) Root directory containing <dataset>/<thresh>_flat/ dirs. "
             "Required when running in batch mode (no positional args).")
    ap.add_argument("--num_locales", type=int, default=4)
    ap.add_argument("--num_cores",   type=int, default=32)
    ap.add_argument("--only", default=None,
        help="(Batch mode) Comma-separated dataset names, e.g. bitcoin,hyves")
    ap.add_argument("--strategies", default=None,
        help="Comma-separated short names from registry, e.g. mlogn_m2n,n_n")
    ap.add_argument("--strategies_raw", default=None,
        help="Comma-separated inter:intra pairs, e.g. m_log_n:m2_over_n,n:n")
    ap.add_argument("--list_strategies", action="store_true",
        help="Print strategy table and exit.")
    ap.add_argument("--skip_existing", action="store_true",
        help="Skip strategy if its locale_0/ dir already exists.")
    ap.add_argument("--fast", action="store_true",
        help="Use file byte size as weight proxy instead of reading file content. "
             "10-100× faster on GPFS. Recommended for rr/rr_npm where ordering "
             "is approximate anyway. Not suitable for exact n/m-dependent strategies "
             "like mlogn_m2n that need precise vertex/edge counts.")
    ap.add_argument("--copy", action="store_true",
        help="Copy files instead of symlinking.")
    ap.add_argument("--dry_run", action="store_true")
    args = ap.parse_args()

    if args.list_strategies:
        print(f"\n  {'Name':<14} {'Inter':<14} {'Intra':<14} Description")
        print(f"  {'─'*14} {'─'*14} {'─'*14} {'─'*55}")
        for n, s in REGISTRY.items():
            star = "★ " if s.recommended else "  "
            print(f"  {n:<14} {s.inter:<14} {s.intra:<14} {star}{s.description}")
        print()
        return

    strategy_items = resolve_strategies(args, ap)
    use_symlinks   = not args.copy

    # Single-dir mode
    if args.flat_dir:
        if not args.output_base:
            ap.error("output_base is required in single-dir mode.")
        flat_dir    = Path(args.flat_dir)
        output_base = Path(args.output_base)
        if not flat_dir.is_dir():
            print(f"ERROR: flat_dir not found: {flat_dir}")
            sys.exit(1)
        print(f"\nSingle-dir mode")
        print(f"Locales: {args.num_locales}   Cores/locale: {args.num_cores}")
        process_one(flat_dir, output_base, strategy_items,
                    args.num_locales, args.num_cores,
                    use_symlinks, args.skip_existing, args.dry_run,
                    fast=args.fast)
        print(f"\n{'='*60}")
        print("DONE — set Chapel inputFolderPath to one of:")
        for name, strat in strategy_items:
            rec = "  ← recommended" if strat.recommended else ""
            print(f"  {output_base / name}/{rec}")
        print(f"{'='*60}\n")
        return

    # Batch mode
    if not args.dst_base:
        ap.error("--dst_base is required in batch mode (omit flat_dir/output_base).")
    global DST_BASE
    DST_BASE = Path(args.dst_base)
    only = {s.strip() for s in args.only.split(",")} if args.only else None
    jobs = find_flat_dirs(only)

    if not jobs:
        print(f"No flat dirs found in {DST_BASE}.")
        return

    print(f"\nBatch mode — {len(jobs)} flat dir(s)  ×  {len(strategy_items)} strategies "
          f"= {len(jobs) * len(strategy_items)} distributions")
    print(f"Locales: {args.num_locales}   Cores/locale: {args.num_cores}")
    print(f"Output pattern: {DST_BASE}/<dataset>/<thresh>_precise/<strategy>/locale_N/\n")

    for ds, thresh, flat_dir, output_base in jobs:
        print(f"\n{'─'*65}")
        print(f"[{ds} / {thresh}]  {flat_dir.name}/  →  {output_base.name}/")
        process_one(flat_dir, output_base, strategy_items,
                    args.num_locales, args.num_cores,
                    use_symlinks, args.skip_existing, args.dry_run,
                    fast=args.fast)

    print(f"\n{'='*65}")
    print("ALL DONE")
    print(f"{'='*65}\n")


if __name__ == "__main__":
    main()