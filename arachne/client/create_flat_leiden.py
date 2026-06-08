#!/usr/bin/env python3
"""
create_flat_leiden.py — build cluster_*.tsv flat directories from
Leiden clustering files + network.tsv.

Source structure:
  <SRC_BASE>/<dataset>/
    network.tsv              — tab-separated: src  dst  (header row)
    leiden_0_001.clustering  — tab-separated: vertex_id  cluster_id  (header row)
    leiden_0_01.clustering
    leiden_mod.clustering

Output (one flat dir per clustering file):
  <DST_BASE>/<dataset>/leiden_0_001_flat/
    cluster_0.tsv
    cluster_1.tsv
    ...   (only clusters that have at least one intra-cluster edge)

Each cluster_N.tsv contains directed edges (src<TAB>dst) of the induced
subgraph — i.e. only edges where both endpoints are in that cluster.

Usage:
    python create_flat_leiden.py --src_base /data/datasets --dst_base /out/preprocess
    python create_flat_leiden.py --src_base /data/datasets --dst_base /out \\
        --only bitcoin,hyves
    python create_flat_leiden.py --src_base /data/datasets --dst_base /out \\
        --only cit_patents --clustering leiden_0_001
    python create_flat_leiden.py --src_base /data/datasets --dst_base /out \\
        --skip_existing
    python create_flat_leiden.py --src_base /data/datasets --dst_base /out \\
        --analyze
    python create_flat_leiden.py --src_base /data/datasets --dst_base /out \\
        --dry_run
"""
from __future__ import annotations

import re
import sys
import argparse
import subprocess
from collections import defaultdict
from pathlib import Path

# ---------------------------------------------------------------------------
# Paths — set from CLI args in main(); no hardcoded paths.
# ---------------------------------------------------------------------------
SRC_BASE: Path | None = None
DST_BASE: Path | None = None
ANALYZE_SCRIPT = Path(__file__).parent / "extract_subgraphs_with_distribution.py"

# ---------------------------------------------------------------------------
# Extra datasets — non-standard directory layouts handled explicitly.
# Each entry:
#   name          str   — dataset name (used in --only filter and output dir)
#   src_dir       Path  — directory containing the edge and clustering files
#   network_file  str   — name of the edge file (tab-separated src dst)
#   clusterings   list  — [(clustering_filename, thresh_name), ...]
#                         thresh_name becomes the flat dir prefix, e.g. "0001"
#                         produces DST_BASE/<name>/0001_flat/
# Populate via --extra_datasets JSON arg or extend this list programmatically.
# ---------------------------------------------------------------------------
EXTRA_DATASETS: list[dict] = []


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def flat_dir_name(clustering_filename: str) -> str:
    """leiden_0_001.clustering  ->  leiden_0_001_flat"""
    return clustering_filename.replace(".clustering", "") + "_flat"


def has_header(path: Path) -> bool:
    """Return True if the first line of path is a text header (not digits)."""
    with open(path) as f:
        first = f.readline().strip()
    if not first:
        return False
    return not first.split()[0].lstrip("-").isdigit()


def read_clustering(path: Path) -> dict[int, int]:
    """Return {vertex_id: cluster_id} from a Leiden clustering file."""
    vertex_cluster: dict[int, int] = {}
    skip_first = has_header(path)
    with open(path) as f:
        for i, line in enumerate(f):
            if i == 0 and skip_first:
                continue
            parts = line.split()
            if len(parts) < 2:
                continue
            try:
                vertex_cluster[int(parts[0])] = int(parts[1])
            except ValueError:
                continue
    return vertex_cluster


def build_flat(network_path: Path,
               clustering_path: Path,
               flat_dir: Path,
               skip_existing: bool,
               dry_run: bool) -> tuple[int, int]:
    """
    Build cluster_*.tsv files in flat_dir.
    Each file contains the induced subgraph edges for one cluster.
    Skips singleton clusters (no intra-cluster edges) — they are
    trivially well-connected and need no WCC computation.

    Returns (num_cluster_files_written, total_intra_edges).
    """
    if dry_run:
        print(f"    [dry_run] would write to {flat_dir}")
        return 0, 0

    existing = list(flat_dir.glob("cluster_*.tsv")) if flat_dir.exists() else []
    if existing and skip_existing:
        print(f"    skipping: {len(existing):,} cluster files already present")
        return len(existing), 0

    # 1. Read clustering
    print(f"    reading clustering ...", end=" ", flush=True)
    vertex_cluster = read_clustering(clustering_path)
    print(f"{len(vertex_cluster):,} vertices assigned to "
          f"{len(set(vertex_cluster.values())):,} clusters")

    # 2. Stream network.tsv — keep only intra-cluster edges
    print(f"    reading network ...", end=" ", flush=True)
    cluster_edges: dict[int, list[tuple[int, int]]] = defaultdict(list)
    cross_cluster = 0
    missing_vertex = 0
    skip_net_header = has_header(network_path)

    with open(network_path) as f:
        for i, line in enumerate(f):
            if i == 0 and skip_net_header:
                continue
            parts = line.split()
            if len(parts) < 2:
                continue
            try:
                src, dst = int(parts[0]), int(parts[1])
            except ValueError:
                continue
            c_src = vertex_cluster.get(src)
            c_dst = vertex_cluster.get(dst)
            if c_src is None or c_dst is None:
                missing_vertex += 1
            elif c_src == c_dst:
                cluster_edges[c_src].append((src, dst))
            else:
                cross_cluster += 1

    total_intra = sum(len(e) for e in cluster_edges.values())
    print(f"{total_intra:,} intra-cluster edges | "
          f"{cross_cluster:,} cross-cluster skipped | "
          f"{missing_vertex:,} unknown-vertex skipped")

    # 3. Write cluster files
    flat_dir.mkdir(parents=True, exist_ok=True)
    print(f"    writing {len(cluster_edges):,} cluster files ...", end=" ", flush=True)
    for cid, edges in cluster_edges.items():
        with open(flat_dir / f"cluster_{cid}.tsv", "w") as f:
            for src, dst in edges:
                f.write(f"{src}\t{dst}\n")
    print("done")

    total_clusters_in_clustering = len(set(vertex_cluster.values()))
    singletons = total_clusters_in_clustering - len(cluster_edges)
    if singletons > 0:
        print(f"    note: {singletons:,} singleton clusters (0 intra-edges) skipped — "
              f"trivially well-connected, no file needed")

    return len(cluster_edges), total_intra


def run_analyze(flat_dir: Path, num_locales: int, num_cores: int) -> str | None:
    """Run analyze --strategies n,m,n+m and save result. Returns best combo or None."""
    out_file = flat_dir.parent / (flat_dir.name.replace("_flat", "_analysis.txt"))
    print(f"    analyzing ...", end=" ", flush=True)
    result = subprocess.run(
        [sys.executable, str(ANALYZE_SCRIPT), "analyze", str(flat_dir) + "/",
         "--num_locales", str(num_locales),
         "--num_cores",   str(num_cores),
         "--strategies",  "n,m,n+m"],
        capture_output=True, text=True,
    )
    out_file.write_text(result.stdout)
    m = re.search(
        r"Best cross-combination\s*:\s*inter='([^']+)'\s*\+\s*intra='([^']+)'",
        result.stdout,
    )
    if m:
        combo = f"inter={m.group(1)}  intra={m.group(2)}"
        print(combo)
        return f"{m.group(1)},{m.group(2)}"
    print(f"done (saved to {out_file.name})")
    return None


# ---------------------------------------------------------------------------
# Extra-dataset processing
# ---------------------------------------------------------------------------

def process_extra_datasets(
    only: set[str] | None,
    only_cl: str | None,
    skip_existing: bool,
    dry_run: bool,
    do_analyze: bool,
    num_locales: int,
    num_cores: int,
    summary: list,
) -> None:
    """Process datasets listed in EXTRA_DATASETS that don't follow SRC_BASE layout."""
    for cfg in EXTRA_DATASETS:
        ds = cfg["name"]
        if only and ds not in only:
            continue

        src_dir: Path = cfg["src_dir"]
        network = src_dir / cfg["network_file"]

        if not src_dir.is_dir():
            print(f"[{ds}] src_dir not found: {src_dir} — skipping")
            continue
        if not network.exists():
            print(f"[{ds}] edge file not found: {network} — skipping")
            continue

        print(f"\n{'─'*60}")
        print(f"[{ds}]  network: {network}  |  {len(cfg['clusterings'])} clustering file(s)")

        for cl_filename, thresh_name in cfg["clusterings"]:
            if only_cl and thresh_name != only_cl:
                continue

            cl_path = src_dir / cl_filename
            if not cl_path.exists():
                print(f"  {cl_filename} not found — skipping")
                continue

            flat_dir = DST_BASE / ds / f"{thresh_name}_flat"
            print(f"\n  {cl_filename}  →  {flat_dir}")

            n_written, _ = build_flat(
                network, cl_path, flat_dir,
                skip_existing=skip_existing,
                dry_run=dry_run,
            )

            best = None
            if do_analyze and not dry_run and n_written > 0:
                best = run_analyze(flat_dir, num_locales, num_cores)

            summary.append((ds, thresh_name, best or "—"))


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> None:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument("--src_base", required=True,
        help="Root source directory containing <dataset>/ subdirectories, each with "
             "network.tsv and *.clustering files.")
    ap.add_argument("--dst_base", required=True,
        help="Root output directory; flat cluster dirs are written to "
             "<dst_base>/<dataset>/<clustering>_flat/")
    ap.add_argument("--only", default=None,
        help="Comma-separated dataset names to process, e.g. bitcoin,hyves")
    ap.add_argument("--clustering", default=None,
        help="Process only this clustering stem (without .clustering), e.g. leiden_0_001")
    ap.add_argument("--skip_existing", action="store_true",
        help="Skip flat dirs that already contain cluster files.")
    ap.add_argument("--analyze", action="store_true",
        help="Run analyze --strategies n,m,n+m on each flat dir after building.")
    ap.add_argument("--num_locales", type=int, default=4)
    ap.add_argument("--num_cores",   type=int, default=32)
    ap.add_argument("--dry_run", action="store_true",
        help="Print what would be done without writing any files.")
    args = ap.parse_args()

    global SRC_BASE, DST_BASE
    SRC_BASE = Path(args.src_base)
    DST_BASE = Path(args.dst_base)

    if not SRC_BASE.is_dir():
        ap.error(f"--src_base not found: {SRC_BASE}")

    only    = {s.strip() for s in args.only.split(",")}       if args.only       else None
    only_cl = args.clustering.strip()                          if args.clustering else None

    datasets = sorted(p for p in SRC_BASE.iterdir() if p.is_dir())
    summary: list[tuple[str, str, str]] = []   # (dataset, clustering, best_combo)

    for ds_dir in datasets:
        ds = ds_dir.name
        if only and ds not in only:
            continue

        network = ds_dir / "network.tsv"
        if not network.exists():
            print(f"[{ds}] no network.tsv — skipping")
            continue

        clusterings = sorted(ds_dir.glob("*.clustering"))
        if not clusterings:
            print(f"[{ds}] no .clustering files — skipping")
            continue

        print(f"\n{'─'*60}")
        print(f"[{ds}]  network: {network}  |  {len(clusterings)} clustering file(s)")

        for cl_path in clusterings:
            if only_cl and cl_path.stem != only_cl:
                continue

            flat_dir = DST_BASE / ds / flat_dir_name(cl_path.name)
            print(f"\n  {cl_path.name}  →  {flat_dir}")

            n_written, n_edges = build_flat(
                network, cl_path, flat_dir,
                skip_existing=args.skip_existing,
                dry_run=args.dry_run,
            )

            best = None
            if args.analyze and not args.dry_run and n_written > 0:
                best = run_analyze(flat_dir, args.num_locales, args.num_cores)

            summary.append((ds, cl_path.stem, best or "—"))

    # Extra datasets (non-standard layout)
    process_extra_datasets(
        only=only,
        only_cl=only_cl,
        skip_existing=args.skip_existing,
        dry_run=args.dry_run,
        do_analyze=args.analyze,
        num_locales=args.num_locales,
        num_cores=args.num_cores,
        summary=summary,
    )

    # Final summary
    if summary:
        print(f"\n{'='*60}")
        print("SUMMARY")
        print(f"  {'Dataset':<16} {'Clustering':<18} {'Best (inter, intra)'}")
        print(f"  {'-'*16} {'-'*18} {'-'*24}")
        for ds, cl, best in summary:
            print(f"  {ds:<16} {cl:<18} {best}")
    print("\nDone.")


if __name__ == "__main__":
    main()