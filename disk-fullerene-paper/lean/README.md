# Three-connected disk-fullerenes

This directory archives the Lean proof of Theorem 1 of *The Smallest Three-Connected Disk-Fullerenes with a Prescribed Boundary Length*. For every integer $h \ge 12$, a three-connected $h$-disk-fullerene has at least six hexagons. For each $h$, exactly one graph up to isomorphism attains this bound. It has $h+6$ pentagons and $2h+22$ vertices.

## Statement and proof

The formal statement is `DiskFullerene.MainStatement`. The embedding is represented by cyclic neighbor lists and oriented face boundaries. The faces cover each directed edge once and give Euler characteristic two. Three-connectivity is expressed by reachability after deletion of at most two vertices. Uniqueness uses isomorphism of the underlying graphs, allowing relabeling and reflection. The interpretation as a plane embedding uses the standard correspondence between rotation systems and cellular embeddings in orientable surfaces. A separate formalization of that topological correspondence is outside the scope of this archive. [Definitions and statement](DiskFullerene/Map.lean)

| Result | Lean declaration |
| --- | --- |
| Lower bound of six hexagons | [`six_lower`](DiskFullerene/Minimum.lean) |
| Construction attaining six for every boundary length $h \ge 12$ | [`PrimalSplice.upperBound`](DiskFullerene/ConstructionUpper.lean) |
| Uniqueness at equality and the complete theorem | [`equality_iso` and `main_theorem`](DiskFullerene/Main.lean) |
| Pentagon and vertex counts | [`eulerCounts`](DiskFullerene/Map.lean) |

One local classification enumerates the 32,768 simple graphs on six labeled vertices. Its cases are checked by kernel reduction. The boundary length in the main theorem remains an arbitrary parameter. [Finite classification](DiskFullerene/SixTable.lean)

## Reproduce the checks

The project uses Lean 4.34.1 and the standard library bundled with Lean. From this directory run

```sh
lake build
lake env lean Audit.lean
LEAN_NUM_THREADS=3 lake env leanchecker -v DiskFullerene
```

The audit checks that `main_theorem` has exactly the declared type and prints its axiom dependencies. The final command rechecks the compiled project modules in the Lean kernel. The axiom output for the main theorem is

```text
'DiskFullerene.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```
