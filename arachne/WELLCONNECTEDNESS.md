# WellConnectedness — Usage Guide

`WellConnectedness.chpl` provides four executors for the Well-Connected
Components (WCC) and Connectivity Modifier (CM) algorithms. Choose the
executor that matches your data source and hardware setup.

---

## Overview of executors

| Executor | Input | Hardware |
|---|---|---|
| `sharedMemoryExecutor` | SegGraph + clusters file | Single locale (1 node) |
| `distributedMemoryExecutor` | SegGraph + clusters file | Multiple locales (multi-node) |
| `fromFilesSharedMemoryExecutor` | Pre-extracted cluster TSV files | Single locale (1 node) |
| `fromFilesDistributedMemoryExecutor` | Pre-extracted cluster TSV files | Multiple locales (multi-node) |

The correct executor is chosen automatically:
- `runWellConnectedness()` → shared or distributed depending on `CHPL_COMM`
- `runWellConnectednessFromFiles()` → same auto-selection for fromFiles path

---

## 1. `sharedMemoryExecutor` — SegGraph, single locale

**When to use:** You loaded the full graph into Arkouda (`SegGraph`) and have
a clusters file mapping vertices to cluster IDs. Running on a single node.

**Input:**
- `G`: `SegGraph` object (graph loaded in Arkouda)
- `inputClustersFilePath`: tab-separated file with columns `vertex_id  cluster_id`

**Execution flow:**
1. Read the clusters file → build `vertex → cluster` mapping
2. Extract induced subgraph edge lists (`getEdgeList`) from the `SegGraph`
3. Run connected components to split disconnected clusters
4. Run `wellconnectednessRecursiveChecker` on each connected sub-cluster
5. Write output: `vertex_id  well_connected_cluster_id`

**How to invoke (Python/Arkouda client):**
```python
import arkouda as ak
from arachne import methods

ak.connect("localhost", 5555)
G = methods.read_graph("my_graph.tsv")
methods.run_well_connectedness(
    G,
    input_clusters_file="clusters.tsv",
    output_path="output_wcc.tsv",
    criterion="log10",
    analysis_type="WCC",
    max_depth=10,
)
```

**Compile (single locale, no distributed runtime):**
```bash
chpl --fast WellConnectedness.chpl  # CHPL_COMM=none
```

---

## 2. `distributedMemoryExecutor` — SegGraph, multiple locales

**When to use:** Same as above but running across multiple compute nodes.

**Input:** Same as `sharedMemoryExecutor`.

**Execution flow:**
1. Read the clusters file on every locale simultaneously (`coforall`);
   each locale keeps only clusters where `clusterID % numLocales == here.id`
2. Each locale extracts induced subgraph edges from its local replica of the `SegGraph`
3. Each locale runs CC + `wellconnectednessRecursiveChecker` independently (no cross-locale communication)
4. Each locale writes its own output file: `output_LOCALE_00000.tsv`, `output_LOCALE_00001.tsv`, ...

**How to run:**
```bash
# Launch Chapel with N locales
./arkouda_server -nl 4
```

**Note:** The SegGraph is replicated to every locale at startup (broadcast step),
so all graph data is available locally without network round-trips during processing.

---

## 3. `fromFilesSharedMemoryExecutor` — pre-extracted TSV files, single locale

**When to use:** You have already extracted cluster subgraphs into individual
`cluster_N.tsv` files (using `create_flat_leiden.py` or
`extract_subgraphs_with_distribution.py`). Running on a single node.

**Input directory layout (flat directory only — no subfolders):**
```
inputFolderPath/
    cluster_0.tsv
    cluster_1.tsv
    ...
    cluster_N.tsv
```

Each `cluster_N.tsv` is a tab-separated edge list (`src  dst`) of the induced
subgraph for that cluster.

**Execution flow:**
1. List all `cluster_*.tsv` files in `inputFolderPath`
2. `forall` over files: load each file → run `wellconnectednessRecursiveCheckerF`
3. Write output: `output_LOCALE_00000.tsv`

**How to generate the input:**

**Option A — `extract_cluster_subgraphs` (recommended if you have the graph loaded in Arkouda):**

```python
import arkouda as ak
from arachne import methods

ak.connect("localhost", 5555)
G = methods.read_graph("my_graph.tsv")

# Writes cluster_0.tsv, cluster_1.tsv, ... to the output folder.
# Each file is the induced subgraph edge list for that cluster.
n = methods.extract_cluster_subgraphs(
    G,
    file_path="/abs/path/to/clusters.tsv",       # vertex → cluster_id mapping
    output_folder_path="/abs/path/to/flat_dir/",  # must be absolute
)
print(f"Wrote {n} cluster files")
```

This calls the Chapel server (`ExtractClusterSubgraphs.chpl`) which reads the clusters
file, extracts each induced subgraph from the loaded `SegGraph`, and writes one
`cluster_N.tsv` per cluster — no separate Python preprocessing step needed.

**Option B — Python tools (if you have Leiden clustering files):**
```bash
python create_flat_leiden.py \
    --src_base /data/datasets --dst_base /scratch/preprocess
# or from a combined TSV
python extract_subgraphs_with_distribution.py split combined.tsv \
    --output_dir /path/to/flat_dir
```

**How to compile and run (single locale):**
```bash
chpl --fast WellConnectedness.chpl  # CHPL_COMM=none
./arkouda_server -nl 1
```

---

## 4. `fromFilesDistributedMemoryExecutor` — pre-extracted TSV files, multiple locales

**When to use:** Pre-extracted cluster files, running across multiple compute nodes.

**Supports two input layouts, auto-detected:**

### Mode A — Flat directory (round-robin assignment)

```
inputFolderPath/
    cluster_0.tsv
    cluster_1.tsv
    ...
```

Files are sorted lexicographically then distributed round-robin across locales:
locale L processes files at positions L, L+numLocales, L+2×numLocales, ...

Simple to set up. Load balance depends on how evenly cluster sizes are distributed.

**Generate with:**

```python
# Option A — from a loaded graph (recommended)
n = methods.extract_cluster_subgraphs(G, "/abs/clusters.tsv", "/abs/flat_dir/")
```
```bash
# Option B — from a combined TSV
python extract_subgraphs_with_distribution.py split combined.tsv \
    --output_dir /path/to/flat_dir
```

**Run:**
```bash
./arkouda_server -nl 4  # inputFolderPath = /path/to/flat_dir
```

---

### Mode B — Pre-distributed locale subfolders (load-balanced, recommended)

```
inputFolderPath/
    locale_0/
        seq_0000000_cluster_42.tsv   # heaviest cluster
        seq_0000001_cluster_7.tsv
        ...
    locale_1/
        seq_0000000_cluster_5.tsv
        ...
    locale_2/
        ...
    locale_3/
        ...
```

Detected automatically when `locale_0/` subfolder is present.

**Why faster:**
- Files are pre-assigned with LPT (Longest Processing Time) which minimises the
  makespan (wall time of the slowest locale).
- Within each locale the `seq_NNNNNNN_` prefix enforces LPT-interleaved order:
  Chapel's static `forall` blocking then gives each core a balanced mix of
  heavy and light clusters, reducing intra-locale imbalance.
- Combined effect: less wasted time waiting for the slowest locale/core.

**Why the locale count must match the number of subfolders exactly:**
Each locale N reads only from `locale_N/`. If you distributed into 4 subfolders
(`locale_0`–`locale_3`) but run with 6 locales, locales 4 and 5 find no
`locale_4/` or `locale_5/` directory and receive 0 files. They sit completely
idle while the other 4 locales do all the work — 2 out of 6 nodes are wasted
and wall time does not improve. Always re-distribute when changing locale count.

**Generate with:**
```bash
# Analyze first to find the best strategy
python extract_subgraphs_with_distribution.py analyze /path/to/flat_dir \
    --num_locales 4 --num_cores 64

# Distribute (example using recommended strategy)
python precise_distribute.py /path/to/flat_dir /path/to/output \
    --num_locales 4 --num_cores 64 --strategies mlogn_m2n
```

**Run:**
```bash
./arkouda_server -nl 4  # inputFolderPath = /path/to/output/mlogn_m2n/
```

---

## Test examples

`arachne/tests/WellConnectedness/` contains small example datasets:

```
flat_subgraphs/                      ← use with Mode A or fromFilesSharedMemory
    cluster_0.tsv ... cluster_7.tsv

distributed_subgraphs/               ← use with Mode B (4 locales)
    locale_0/
        seq_0000000_cluster_4.tsv
        seq_0000001_cluster_0.tsv
    locale_1/
        seq_0000000_cluster_2.tsv
        seq_0000001_cluster_7.tsv
    locale_2/
        seq_0000000_cluster_5.tsv
        seq_0000001_cluster_1.tsv
    locale_3/
        seq_0000000_cluster_6.tsv
        seq_0000001_cluster_3.tsv
```

---

## Parameters reference

| Parameter | Description | Example values |
|---|---|---|
| `connectednessCriterion` | Threshold function | `"log10"`, `"log2"`, `"sqrt"`, `"mult"` |
| `connectednessCriterionMultValue` | Multiplier for `"mult"` criterion | `1.0` |
| `preFilterMinSize` | Skip clusters smaller than this before CC | `5` |
| `postFilterMinSize` | Skip sub-clusters smaller than this after split | `3` |
| `analysisType` | Algorithm mode | `"WCC"` or `"CM"` |
| `maxDepth` | Maximum recursion depth | `20` |

**`analysisType` modes:**
- `"WCC"` — Well-Connected Components: recursively split until each component
  satisfies the connectivity criterion.
- `"CM"` — Connectivity Modifier: same as WCC but after each split runs Leiden
  community detection and recurses per community. Uses `c_computeLeiden` (libleidenalg).