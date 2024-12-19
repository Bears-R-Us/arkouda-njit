Starting motif counting with k=3 on a graph of 5 vertices.
Maximum degree: 4
Enumerate: starting enumeration over all vertices
Root = 0 (1/5)
===== Explore called =====
Current root: 0 level: 1 remainder: 2
Visited Array: true false false false false
Current partial subgraph:
Level 0 (count=1): 0 
==========================
====== initChildSet called for level 1 and root 0 ======
initChildSet: Found 2 valid children at level 1
Children: 1 2 
Exploring with initial selection of size 1 at level 1
Selected vertices: 1 
===== Explore called =====
Current root: 0 level: 2 remainder: 1
Visited Array: true true true false false
Current partial subgraph:
Level 0 (count=1): 0 
Level 1 (count=1): 1 
==========================
====== initChildSet called for level 2 and root 0 ======
initChildSet: Found 0 valid children at level 2
Children: 
Not enough children (0) to select 1 vertices at level 2
GEN called with n=2 k=1 level=1 remainder=2 m=1
GEN called with n=1 k=1 level=1 remainder=2 m=1
GEN: k=1 case, calling swap(n, n-1) => swap(2, 1)
swap called: swapping indices 2 and 1 at level 1
Before swap: indexMap[level,i] = 0 indexMap[level,j] = 1
After swap: subgraph[level,indexMap[level,i]] = childSet[level,i] = 2
Now calling Explore after swap
===== Explore called =====
Current root: 0 level: 2 remainder: 1
Visited Array: true true true false false
Current partial subgraph:
Level 0 (count=1): 0 
Level 1 (count=1): 2 
==========================
====== initChildSet called for level 2 and root 0 ======
initChildSet: Found 2 valid children at level 2
Children: 4 3 
Exploring with initial selection of size 1 at level 2
Selected vertices: 4 
===== Explore called =====
Current root: 0 level: 3 remainder: 0
Visited Array: true true true true true
Current partial subgraph:
Level 0 (count=1): 0 
Level 1 (count=1): 2 
Level 2 (count=1): 4 
==========================
subgraphVerts= 0 2 4
encodePattern called and pattern= 136
Found complete subgraph #1
Level 0: 0 
Level 1: 2 
Level 2: 4 
pattern generated: 136
GEN called with n=2 k=1 level=2 remainder=1 m=1
GEN called with n=1 k=1 level=2 remainder=1 m=1
GEN: k=1 case, calling swap(n, n-1) => swap(2, 1)
swap called: swapping indices 2 and 1 at level 2
Before swap: indexMap[level,i] = 0 indexMap[level,j] = 1
After swap: subgraph[level,indexMap[level,i]] = childSet[level,i] = 3
Now calling Explore after swap
===== Explore called =====
Current root: 0 level: 3 remainder: 0
Visited Array: true true true true true
Current partial subgraph:
Level 0 (count=1): 0 
Level 1 (count=1): 2 
Level 2 (count=1): 3 
==========================
subgraphVerts= 0 2 3
encodePattern called and pattern= 40
Found complete subgraph #2
Level 0: 0 
Level 1: 2 
Level 2: 3 
pattern generated: 40
NEG called with n=1 k=0 level=2 remainder=1 m=1
NEG called with n=1 k=0 level=1 remainder=2 m=1
Exploring with initial selection of size 2 at level 1
Selected vertices: 1 2 
===== Explore called =====
Current root: 0 level: 2 remainder: 0
Visited Array: true true true false false
Current partial subgraph:
Level 0 (count=1): 0 
Level 1 (count=2): 1 2 
==========================
subgraphVerts= 0 1 2
encodePattern called and pattern= 98
Found complete subgraph #3
Level 0: 0 
Level 1: 1 2 
Level 2: 
pattern generated: 98
GEN called with n=2 k=2 level=1 remainder=2 m=2
Root = 1 (2/5)
===== Explore called =====
Current root: 1 level: 1 remainder: 2
Visited Array: false true false false false
Current partial subgraph:
Level 0 (count=1): 1 
==========================
====== initChildSet called for level 1 and root 1 ======
initChildSet: Found 1 valid children at level 1
Children: 2 
Exploring with initial selection of size 1 at level 1
Selected vertices: 2 
===== Explore called =====
Current root: 1 level: 2 remainder: 1
Visited Array: false true true false false
Current partial subgraph:
Level 0 (count=1): 1 
Level 1 (count=1): 2 
==========================
====== initChildSet called for level 2 and root 1 ======
initChildSet: Found 2 valid children at level 2
Children: 4 3 
Exploring with initial selection of size 1 at level 2
Selected vertices: 4 
===== Explore called =====
Current root: 1 level: 3 remainder: 0
Visited Array: false true true true true
Current partial subgraph:
Level 0 (count=1): 1 
Level 1 (count=1): 2 
Level 2 (count=1): 4 
==========================
subgraphVerts= 1 2 4
encodePattern called and pattern= 130
Found complete subgraph #4
Level 0: 1 
Level 1: 2 
Level 2: 4 
pattern generated: 130
GEN called with n=2 k=1 level=2 remainder=1 m=1
GEN called with n=1 k=1 level=2 remainder=1 m=1
GEN: k=1 case, calling swap(n, n-1) => swap(2, 1)
swap called: swapping indices 2 and 1 at level 2
Before swap: indexMap[level,i] = 1 indexMap[level,j] = 1
After swap: subgraph[level,indexMap[level,i]] = childSet[level,i] = 3
Now calling Explore after swap
===== Explore called =====
Current root: 1 level: 3 remainder: 0
Visited Array: false true true true true
Current partial subgraph:
Level 0 (count=1): 1 
Level 1 (count=1): 2 
Level 2 (count=1): 3 
==========================
subgraphVerts= 1 2 3
encodePattern called and pattern= 34
Found complete subgraph #5
Level 0: 1 
Level 1: 2 
Level 2: 3 
pattern generated: 34
NEG called with n=1 k=0 level=2 remainder=1 m=1
GEN called with n=1 k=1 level=1 remainder=2 m=1
Not enough children (1) to select 2 vertices at level 1
Root = 2 (3/5)
===== Explore called =====
Current root: 2 level: 1 remainder: 2
Visited Array: false false true false false
Current partial subgraph:
Level 0 (count=1): 2 
==========================
====== initChildSet called for level 1 and root 2 ======
initChildSet: Found 2 valid children at level 1
Children: 4 3 
Exploring with initial selection of size 1 at level 1
Selected vertices: 4 
===== Explore called =====
Current root: 2 level: 2 remainder: 1
Visited Array: false false true true true
Current partial subgraph:
Level 0 (count=1): 2 
Level 1 (count=1): 4 
==========================
====== initChildSet called for level 2 and root 2 ======
initChildSet: Found 0 valid children at level 2
Children: 
Not enough children (0) to select 1 vertices at level 2
GEN called with n=2 k=1 level=1 remainder=2 m=1
GEN called with n=1 k=1 level=1 remainder=2 m=1
GEN: k=1 case, calling swap(n, n-1) => swap(2, 1)
swap called: swapping indices 2 and 1 at level 1
Before swap: indexMap[level,i] = 2 indexMap[level,j] = 1
After swap: subgraph[level,indexMap[level,i]] = childSet[level,i] = 3
Now calling Explore after swap
===== Explore called =====
Current root: 2 level: 2 remainder: 1
Visited Array: false false true true true
Current partial subgraph:
Level 0 (count=1): 2 
Level 1 (count=1): 3 
==========================
====== initChildSet called for level 2 and root 2 ======
initChildSet: Found 0 valid children at level 2
Children: 
Not enough children (0) to select 1 vertices at level 2
NEG called with n=1 k=0 level=1 remainder=2 m=1
Exploring with initial selection of size 2 at level 1
Selected vertices: 4 3 
===== Explore called =====
Current root: 2 level: 2 remainder: 0
Visited Array: false false true true true
Current partial subgraph:
Level 0 (count=1): 2 
Level 1 (count=2): 4 3 
==========================
subgraphVerts= 2 3 4
encodePattern called and pattern= 98
Found complete subgraph #6
Level 0: 2 
Level 1: 4 3 
Level 2: 
pattern generated: 98
GEN called with n=2 k=2 level=1 remainder=2 m=2
Root = 3 (4/5)
===== Explore called =====
Current root: 3 level: 1 remainder: 2
Visited Array: false false false true false
Current partial subgraph:
Level 0 (count=1): 3 
==========================
====== initChildSet called for level 1 and root 3 ======
initChildSet: Found 1 valid children at level 1
Children: 4 
Exploring with initial selection of size 1 at level 1
Selected vertices: 4 
===== Explore called =====
Current root: 3 level: 2 remainder: 1
Visited Array: false false false true true
Current partial subgraph:
Level 0 (count=1): 3 
Level 1 (count=1): 4 
==========================
====== initChildSet called for level 2 and root 3 ======
initChildSet: Found 0 valid children at level 2
Children: 
Not enough children (0) to select 1 vertices at level 2
GEN called with n=1 k=1 level=1 remainder=2 m=1
Not enough children (1) to select 2 vertices at level 1
Root = 4 (5/5)
===== Explore called =====
Current root: 4 level: 1 remainder: 2
Visited Array: false false false false true
Current partial subgraph:
Level 0 (count=1): 4 
==========================
====== initChildSet called for level 1 and root 4 ======
initChildSet: Found 0 valid children at level 1
Children: 
Not enough children (0) to select 1 vertices at level 1
Enumerate: finished enumeration over all vertices

Total motif found: 6
