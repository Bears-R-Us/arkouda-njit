# Python Tools for WellConnectedness Subgraph Distribution

These tools help you prepare cluster subgraph files for the Chapel
`WellConnectedness.chpl` executors.

**Two ways to produce the `cluster_N.tsv` files:**

| Method | When to use |
|---|---|
| `extract_cluster_subgraphs()` (Arkouda client function) | You have the graph loaded in Arkouda (`SegGraph`). Fastest — extraction runs server-side in Chapel. |
| Python scripts below | You have Leiden clustering files or a combined TSV but no loaded graph. |

---

## `extract_cluster_subgraphs` — extract subgraphs via Arkouda (recommended)

```python
import arkouda as ak
from arachne import methods

ak.connect("localhost", 5555)
G = methods.read_graph("my_graph.tsv")

# Writes cluster_0.tsv, cluster_1.tsv, ... to the output folder.
# Each file contains the induced subgraph edge list for that cluster.
n = methods.extract_cluster_subgraphs(
    G,
    file_path="/abs/path/to/clusters.tsv",        # vertex_id  cluster_id  (tab-separated)
    output_folder_path="/abs/path/to/flat_dir/",  # must be absolute path, trailing / required
)
print(f"Wrote {n} cluster files")
```

**What it does:** Calls `ExtractClusterSubgraphs.chpl` on the Arkouda server.
The server reads the clusters file, extracts each cluster's induced subgraph
edge list from the loaded `SegGraph`, and writes one `cluster_N.tsv` per cluster.
Works for both single-locale and multi-locale deployments.

**Output files** (ready to pass directly to `well_connected_components_from_files`
or `connectivity_modifier_from_files`, or to use with the Python distribution tools):
```
/abs/path/to/flat_dir/
    cluster_0.tsv
    cluster_1.tsv
    ...
```

---

## 1. `create_flat_leiden.py` — extract subgraph files from Leiden clusterings

Reads a network edge file and Leiden `.clustering` files, then writes one
`cluster_N.tsv` per cluster (induced subgraph edges only).

```bash
python create_flat_leiden.py \
    --src_base /path/to/datasets \
    --dst_base /path/to/output

# Process only specific datasets
python create_flat_leiden.py \
    --src_base /path/to/datasets \
    --dst_base /path/to/output \
    --only bitcoin,hyves

# Skip already-built flat dirs
python create_flat_leiden.py \
    --src_base /path/to/datasets \
    --dst_base /path/to/output \
    --skip_existing

# Preview without writing
python create_flat_leiden.py \
    --src_base /path/to/datasets \
    --dst_base /path/to/output \
    --dry_run
```

**Source layout expected:**
```
<src_base>/<dataset>/
    network.tsv               # tab-separated: src  dst
    leiden_0_001.clustering   # tab-separated: vertex_id  cluster_id
    leiden_0_01.clustering
    leiden_mod.clustering
```

**Output:**
```
<dst_base>/<dataset>/leiden_0_001_flat/
    cluster_0.tsv
    cluster_1.tsv
    ...
```

Each `cluster_N.tsv` is a tab-separated edge list of the induced subgraph
(only edges where both endpoints belong to that cluster).

---

## 2. `extract_subgraphs_with_distribution.py` — split, analyze, and distribute

Three subcommands:

### `split` — split a combined TSV into per-cluster files

```bash
python extract_subgraphs_with_distribution.py split combined.tsv \
    --output_dir /path/to/flat_dir
```

Clusters in the combined file must be separated by lines containing only `-`.

### `analyze` — report inter- and intra-locale load balance for all strategies

```bash
python extract_subgraphs_with_distribution.py analyze /path/to/flat_dir \
    --num_locales 4 \
    --num_cores 64

# Fast mode — uses file size as proxy (seconds vs minutes for large datasets)
python extract_subgraphs_with_distribution.py analyze /path/to/flat_dir \
    --num_locales 4 \
    --num_cores 64 \
    --fast
```

Reports inter-locale imbalance, intra-locale core imbalance, cross-combination
rankings, and a recommended `distribute` command.

### `distribute` — write `locale_0/`, `locale_1/`, ... subfolders

```bash
python extract_subgraphs_with_distribution.py distribute \
    /path/to/flat_dir /path/to/output \
    --num_locales 4 \
    --num_cores 64 \
    --strategy n

# Independent inter/intra strategies
python extract_subgraphs_with_distribution.py distribute \
    /path/to/flat_dir /path/to/output \
    --num_locales 4 --num_cores 64 \
    --inter_strategy m_log_n \
    --intra_strategy m2_over_n
```

Available strategies: `round_robin`, `bytes`, `n`, `m`, `n+m`, `n+2m`,
`m*n`, `sqrt_nm`, `m2_over_n`, `n_log_n`, `m_log_n`, `n_log_n_m`.

Point Chapel's `inputFolderPath` to the output directory.

---

## 3. `precise_distribute.py` — scan once, apply all strategies fairly

Scans each flat directory **once** for exact vertex/edge counts, then applies
every registered strategy to the same data. Guarantees a fair comparison
(differences come from strategy logic, not I/O timing variation).

### Single-dir mode

```bash
python precise_distribute.py /path/to/flat_dir /path/to/output \
    --num_locales 4 \
    --num_cores 32

# Specific strategies only
python precise_distribute.py /path/to/flat_dir /path/to/output \
    --num_locales 4 --num_cores 32 \
    --strategies mlogn_m2n,n_n

# Preview without writing
python precise_distribute.py /path/to/flat_dir /path/to/output \
    --dry_run

# List available strategies
python precise_distribute.py --list_strategies
```

### Batch mode — process multiple datasets

```bash
python precise_distribute.py \
    --dst_base /path/to/preprocess_root \
    --num_locales 4 \
    --num_cores 32

# Resume interrupted run
python precise_distribute.py \
    --dst_base /path/to/preprocess_root \
    --skip_existing
```

Batch mode scans `<dst_base>` for all `*_flat/` subdirectories and distributes
each with every registered strategy.

**Registered strategies:**

| Name        | Inter      | Intra       | Notes                              |
|-------------|------------|-------------|------------------------------------|
| `mlogn_m2n` | `m_log_n`  | `m2_over_n` | ★ recommended                     |
| `n_n`       | `n`        | `n`         | best simple                        |
| `m_m`       | `m`        | `m`         | simple — good on edge-dense graphs |
| `npm_npm`   | `n+m`      | `n+m`       | symmetric                          |
| `m_m2n`     | `m`        | `m2_over_n` | mixed                              |
| `rr`        | round_robin| `n+m`       | replicates Chapel default          |
| `rr_npm`    | sorted RR  | `n+m`       | sorted round-robin                 |

---

## Typical workflow

### Path A — graph already loaded in Arkouda

```python
import arkouda as ak
from arachne import methods

ak.connect("localhost", 5555)
G = methods.read_graph("my_graph.tsv")

# 1. Extract flat subgraph files server-side (fastest)
n = methods.extract_cluster_subgraphs(
    G,
    file_path="/abs/path/to/clusters.tsv",
    output_folder_path="/abs/path/to/flat_dir/",
)

# 2. (Optional) Distribute for load-balanced multi-locale run — do this in shell:
#    python precise_distribute.py /abs/path/to/flat_dir /abs/path/to/precise_dir \
#        --num_locales 4 --num_cores 64

# 3. Run WCC directly on files
methods.well_connected_components_from_files(
    input_folder="/abs/path/to/flat_dir/",     # or precise_dir/mlogn_m2n/
    output_path="/abs/path/to/output.tsv",
)
```

### Path B — starting from Leiden clustering files

```bash
# 1. Extract flat subgraph files
python create_flat_leiden.py \
    --src_base /data/datasets \
    --dst_base /scratch/preprocess

# 2. Analyze balance (optional but recommended)
python extract_subgraphs_with_distribution.py analyze \
    /scratch/preprocess/bitcoin/leiden_0_001_flat \
    --num_locales 4 --num_cores 64

# 3. Distribute across locales
python precise_distribute.py \
    /scratch/preprocess/bitcoin/leiden_0_001_flat \
    /scratch/preprocess/bitcoin/leiden_0_001_precise \
    --num_locales 4 --num_cores 64

# 4. Run Chapel — point inputFolderPath at the chosen strategy dir
#    e.g. /scratch/preprocess/bitcoin/leiden_0_001_precise/mlogn_m2n/
```