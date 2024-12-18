Input graph edges:
0 -> 1
1 -> 2
2 -> 0
2 -> 3
3 -> 4
4 -> 2
Starting motif counting for k=3
Graph has 5 vertices and 6 edges
Maximum degree: 4
+++ Root is 0 (1/5)
------- State Debug: Before starting enumeration from root 0 -------
Subgraph count: 0

Visited vertices: true false false false false

Subgraph structure:
Level 0 (count=1): 0 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=0): 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 
Level 2: 
-----------------End of State Debug -----------------------
********enumerateVertex Called***************
  Current level: 1
  Root vertex: 0
  Remainder: 2
*******initChildSet started*****************
------- State Debug: Before initChildSet -------
Subgraph count: 0

Visited vertices: true false false false false

Subgraph structure:
Level 0 (count=1): 0 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=0): 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 
Level 2: 
-----------------End of State Debug -----------------------
Found 2 valid vertices at level 1
------- State Debug: After initChildSet -------
Subgraph count: 0

Visited vertices: true false false false false

Subgraph structure:
Level 0 (count=1): 0 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 1 2 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 0 0 
Level 2: 
-----------------End of State Debug -----------------------
Selecting 1 vertices at level 1
********enumerateVertex Called***************
  Current level: 2
  Root vertex: 0
  Remainder: 1
*******initChildSet started*****************
------- State Debug: Before initChildSet -------
Subgraph count: 0

Visited vertices: true true false false false

Subgraph structure:
Level 0 (count=1): 0 
Level 1 (count=1): 1 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 1 2 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 1 0 
Level 2: 
-----------------End of State Debug -----------------------
Found 1 valid vertices at level 2
------- State Debug: After initChildSet -------
Subgraph count: 0

Visited vertices: true true false false false

Subgraph structure:
Level 0 (count=1): 0 
Level 1 (count=1): 1 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 1 2 
Level 2 (count=1): 2 

Index mapping:
Level 0: 
Level 1: 1 0 
Level 2: 0 
-----------------End of State Debug -----------------------
Selecting 1 vertices at level 2
********enumerateVertex Called***************
  Current level: 3
  Root vertex: 0
  Remainder: 0
Found subgraph #1
------- State Debug: Complete subgraph found -------
Subgraph count: 1

Visited vertices: true true true false false

Subgraph structure:
Level 0 (count=1): 0 
Level 1 (count=1): 1 
Level 2 (count=1): 2 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 1 2 
Level 2 (count=1): 2 

Index mapping:
Level 0: 
Level 1: 1 0 
Level 2: 1 
-----------------End of State Debug -----------------------
*******GEN started*****************
n=2 k=1 level=1
*******GEN started*****************
n=1 k=1 level=1
*******swap started*****************
Swapping indices 2 and 1 at level 1
********enumerateVertex Called***************
  Current level: 2
  Root vertex: 0
  Remainder: 1
*******initChildSet started*****************
------- State Debug: Before initChildSet -------
Subgraph count: 1

Visited vertices: true true false false false

Subgraph structure:
Level 0 (count=1): 0 
Level 1 (count=1): 2 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 1 2 
Level 2 (count=1): 2 

Index mapping:
Level 0: 
Level 1: 1 1 
Level 2: 1 
-----------------End of State Debug -----------------------
Found 2 valid vertices at level 2
------- State Debug: After initChildSet -------
Subgraph count: 1

Visited vertices: true true false false false

Subgraph structure:
Level 0 (count=1): 0 
Level 1 (count=1): 2 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 1 2 
Level 2 (count=2): 4 3 

Index mapping:
Level 0: 
Level 1: 1 1 
Level 2: 1 0 
-----------------End of State Debug -----------------------
Selecting 1 vertices at level 2
********enumerateVertex Called***************
  Current level: 3
  Root vertex: 0
  Remainder: 0
Found subgraph #2
------- State Debug: Complete subgraph found -------
Subgraph count: 2

Visited vertices: true true false false true

Subgraph structure:
Level 0 (count=1): 0 
Level 1 (count=1): 2 
Level 2 (count=1): 4 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 1 2 
Level 2 (count=2): 4 3 

Index mapping:
Level 0: 
Level 1: 1 1 
Level 2: 1 0 
-----------------End of State Debug -----------------------
*******GEN started*****************
n=2 k=1 level=2
*******GEN started*****************
n=1 k=1 level=2
*******swap started*****************
Swapping indices 2 and 1 at level 2
********enumerateVertex Called***************
  Current level: 3
  Root vertex: 0
  Remainder: 0
Found subgraph #3
------- State Debug: Complete subgraph found -------
Subgraph count: 3

Visited vertices: true true false false true

Subgraph structure:
Level 0 (count=1): 0 
Level 1 (count=1): 2 
Level 2 (count=1): 3 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 1 2 
Level 2 (count=2): 4 3 

Index mapping:
Level 0: 
Level 1: 1 1 
Level 2: 1 1 
-----------------End of State Debug -----------------------
*******NEG started*****************
n=1 k=0 level=2
*******NEG started*****************
n=1 k=0 level=1
Selecting 2 vertices at level 1
********enumerateVertex Called***************
  Current level: 2
  Root vertex: 0
  Remainder: 0
Found subgraph #4
------- State Debug: Complete subgraph found -------
Subgraph count: 4

Visited vertices: true true true false false

Subgraph structure:
Level 0 (count=1): 0 
Level 1 (count=2): 1 2 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 1 2 
Level 2 (count=2): 4 3 

Index mapping:
Level 0: 
Level 1: 1 2 
Level 2: 1 1 
-----------------End of State Debug -----------------------
------- State Debug: After completing enumeration from root 0 -------
Subgraph count: 4

Visited vertices: false false false false false

Subgraph structure:
Level 0 (count=1): 0 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 1 2 
Level 2 (count=2): 4 3 

Index mapping:
Level 0: 
Level 1: 1 2 
Level 2: 1 1 
-----------------End of State Debug -----------------------
+++ Root is 1 (2/5)
------- State Debug: Before starting enumeration from root 1 -------
Subgraph count: 4

Visited vertices: false true false false false

Subgraph structure:
Level 0 (count=1): 1 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=0): 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 
Level 2: 
-----------------End of State Debug -----------------------
********enumerateVertex Called***************
  Current level: 1
  Root vertex: 1
  Remainder: 2
*******initChildSet started*****************
------- State Debug: Before initChildSet -------
Subgraph count: 4

Visited vertices: false true false false false

Subgraph structure:
Level 0 (count=1): 1 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=0): 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 
Level 2: 
-----------------End of State Debug -----------------------
Found 1 valid vertices at level 1
------- State Debug: After initChildSet -------
Subgraph count: 4

Visited vertices: false true false false false

Subgraph structure:
Level 0 (count=1): 1 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=1): 2 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 0 
Level 2: 
-----------------End of State Debug -----------------------
Selecting 1 vertices at level 1
********enumerateVertex Called***************
  Current level: 2
  Root vertex: 1
  Remainder: 1
*******initChildSet started*****************
------- State Debug: Before initChildSet -------
Subgraph count: 4

Visited vertices: false true true false false

Subgraph structure:
Level 0 (count=1): 1 
Level 1 (count=1): 2 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=1): 2 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 1 
Level 2: 
-----------------End of State Debug -----------------------
Found 2 valid vertices at level 2
------- State Debug: After initChildSet -------
Subgraph count: 4

Visited vertices: false true true false false

Subgraph structure:
Level 0 (count=1): 1 
Level 1 (count=1): 2 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=1): 2 
Level 2 (count=2): 4 3 

Index mapping:
Level 0: 
Level 1: 1 
Level 2: 0 0 
-----------------End of State Debug -----------------------
Selecting 1 vertices at level 2
********enumerateVertex Called***************
  Current level: 3
  Root vertex: 1
  Remainder: 0
Found subgraph #5
------- State Debug: Complete subgraph found -------
Subgraph count: 5

Visited vertices: false true true false true

Subgraph structure:
Level 0 (count=1): 1 
Level 1 (count=1): 2 
Level 2 (count=1): 4 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=1): 2 
Level 2 (count=2): 4 3 

Index mapping:
Level 0: 
Level 1: 1 
Level 2: 1 0 
-----------------End of State Debug -----------------------
*******GEN started*****************
n=2 k=1 level=2
*******GEN started*****************
n=1 k=1 level=2
*******swap started*****************
Swapping indices 2 and 1 at level 2
********enumerateVertex Called***************
  Current level: 3
  Root vertex: 1
  Remainder: 0
Found subgraph #6
------- State Debug: Complete subgraph found -------
Subgraph count: 6

Visited vertices: false true true false true

Subgraph structure:
Level 0 (count=1): 1 
Level 1 (count=1): 2 
Level 2 (count=1): 3 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=1): 2 
Level 2 (count=2): 4 3 

Index mapping:
Level 0: 
Level 1: 1 
Level 2: 1 1 
-----------------End of State Debug -----------------------
*******NEG started*****************
n=1 k=0 level=2
------- State Debug: After completing enumeration from root 1 -------
Subgraph count: 6

Visited vertices: false false false false false

Subgraph structure:
Level 0 (count=1): 1 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=1): 2 
Level 2 (count=2): 4 3 

Index mapping:
Level 0: 
Level 1: 1 
Level 2: 1 1 
-----------------End of State Debug -----------------------
+++ Root is 2 (3/5)
------- State Debug: Before starting enumeration from root 2 -------
Subgraph count: 6

Visited vertices: false false true false false

Subgraph structure:
Level 0 (count=1): 2 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=0): 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 
Level 2: 
-----------------End of State Debug -----------------------
********enumerateVertex Called***************
  Current level: 1
  Root vertex: 2
  Remainder: 2
*******initChildSet started*****************
------- State Debug: Before initChildSet -------
Subgraph count: 6

Visited vertices: false false true false false

Subgraph structure:
Level 0 (count=1): 2 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=0): 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 
Level 2: 
-----------------End of State Debug -----------------------
Found 2 valid vertices at level 1
------- State Debug: After initChildSet -------
Subgraph count: 6

Visited vertices: false false true false false

Subgraph structure:
Level 0 (count=1): 2 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 4 3 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 0 0 
Level 2: 
-----------------End of State Debug -----------------------
Selecting 1 vertices at level 1
********enumerateVertex Called***************
  Current level: 2
  Root vertex: 2
  Remainder: 1
*******initChildSet started*****************
------- State Debug: Before initChildSet -------
Subgraph count: 6

Visited vertices: false false true false true

Subgraph structure:
Level 0 (count=1): 2 
Level 1 (count=1): 4 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 4 3 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 1 0 
Level 2: 
-----------------End of State Debug -----------------------
Found 1 valid vertices at level 2
------- State Debug: After initChildSet -------
Subgraph count: 6

Visited vertices: false false true false true

Subgraph structure:
Level 0 (count=1): 2 
Level 1 (count=1): 4 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 4 3 
Level 2 (count=1): 3 

Index mapping:
Level 0: 
Level 1: 1 0 
Level 2: 0 
-----------------End of State Debug -----------------------
Selecting 1 vertices at level 2
********enumerateVertex Called***************
  Current level: 3
  Root vertex: 2
  Remainder: 0
Found subgraph #7
------- State Debug: Complete subgraph found -------
Subgraph count: 7

Visited vertices: false false true true true

Subgraph structure:
Level 0 (count=1): 2 
Level 1 (count=1): 4 
Level 2 (count=1): 3 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 4 3 
Level 2 (count=1): 3 

Index mapping:
Level 0: 
Level 1: 1 0 
Level 2: 1 
-----------------End of State Debug -----------------------
*******GEN started*****************
n=2 k=1 level=1
*******GEN started*****************
n=1 k=1 level=1
*******swap started*****************
Swapping indices 2 and 1 at level 1
********enumerateVertex Called***************
  Current level: 2
  Root vertex: 2
  Remainder: 1
*******initChildSet started*****************
------- State Debug: Before initChildSet -------
Subgraph count: 7

Visited vertices: false false true false true

Subgraph structure:
Level 0 (count=1): 2 
Level 1 (count=1): 3 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 4 3 
Level 2 (count=1): 3 

Index mapping:
Level 0: 
Level 1: 1 1 
Level 2: 1 
-----------------End of State Debug -----------------------
Found 0 valid vertices at level 2
------- State Debug: After initChildSet -------
Subgraph count: 7

Visited vertices: false false true false true

Subgraph structure:
Level 0 (count=1): 2 
Level 1 (count=1): 3 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 4 3 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 1 1 
Level 2: 
-----------------End of State Debug -----------------------
*******NEG started*****************
n=1 k=0 level=1
Selecting 2 vertices at level 1
********enumerateVertex Called***************
  Current level: 2
  Root vertex: 2
  Remainder: 0
Found subgraph #8
------- State Debug: Complete subgraph found -------
Subgraph count: 8

Visited vertices: false false true true true

Subgraph structure:
Level 0 (count=1): 2 
Level 1 (count=2): 4 3 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 4 3 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 1 2 
Level 2: 
-----------------End of State Debug -----------------------
------- State Debug: After completing enumeration from root 2 -------
Subgraph count: 8

Visited vertices: false false false false false

Subgraph structure:
Level 0 (count=1): 2 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=2): 4 3 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 1 2 
Level 2: 
-----------------End of State Debug -----------------------
+++ Root is 3 (4/5)
------- State Debug: Before starting enumeration from root 3 -------
Subgraph count: 8

Visited vertices: false false false true false

Subgraph structure:
Level 0 (count=1): 3 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=0): 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 
Level 2: 
-----------------End of State Debug -----------------------
********enumerateVertex Called***************
  Current level: 1
  Root vertex: 3
  Remainder: 2
*******initChildSet started*****************
------- State Debug: Before initChildSet -------
Subgraph count: 8

Visited vertices: false false false true false

Subgraph structure:
Level 0 (count=1): 3 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=0): 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 
Level 2: 
-----------------End of State Debug -----------------------
Found 1 valid vertices at level 1
------- State Debug: After initChildSet -------
Subgraph count: 8

Visited vertices: false false false true false

Subgraph structure:
Level 0 (count=1): 3 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=1): 4 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 0 
Level 2: 
-----------------End of State Debug -----------------------
Selecting 1 vertices at level 1
********enumerateVertex Called***************
  Current level: 2
  Root vertex: 3
  Remainder: 1
*******initChildSet started*****************
------- State Debug: Before initChildSet -------
Subgraph count: 8

Visited vertices: false false false true true

Subgraph structure:
Level 0 (count=1): 3 
Level 1 (count=1): 4 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=1): 4 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 1 
Level 2: 
-----------------End of State Debug -----------------------
Found 0 valid vertices at level 2
------- State Debug: After initChildSet -------
Subgraph count: 8

Visited vertices: false false false true true

Subgraph structure:
Level 0 (count=1): 3 
Level 1 (count=1): 4 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=1): 4 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 1 
Level 2: 
-----------------End of State Debug -----------------------
------- State Debug: After completing enumeration from root 3 -------
Subgraph count: 8

Visited vertices: false false false false false

Subgraph structure:
Level 0 (count=1): 3 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=1): 4 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 1 
Level 2: 
-----------------End of State Debug -----------------------
+++ Root is 4 (5/5)
------- State Debug: Before starting enumeration from root 4 -------
Subgraph count: 8

Visited vertices: false false false false true

Subgraph structure:
Level 0 (count=1): 4 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=0): 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 
Level 2: 
-----------------End of State Debug -----------------------
********enumerateVertex Called***************
  Current level: 1
  Root vertex: 4
  Remainder: 2
*******initChildSet started*****************
------- State Debug: Before initChildSet -------
Subgraph count: 8

Visited vertices: false false false false true

Subgraph structure:
Level 0 (count=1): 4 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=0): 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 
Level 2: 
-----------------End of State Debug -----------------------
Found 0 valid vertices at level 1
------- State Debug: After initChildSet -------
Subgraph count: 8

Visited vertices: false false false false true

Subgraph structure:
Level 0 (count=1): 4 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=0): 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 
Level 2: 
-----------------End of State Debug -----------------------
------- State Debug: After completing enumeration from root 4 -------
Subgraph count: 8

Visited vertices: false false false false false

Subgraph structure:
Level 0 (count=1): 4 
Level 1 (count=0): 
Level 2 (count=0): 

ChildSet structure:
Level 0 (count=0): 
Level 1 (count=0): 
Level 2 (count=0): 

Index mapping:
Level 0: 
Level 1: 
Level 2: 
-----------------End of State Debug -----------------------
Total subgraphs found: 8
