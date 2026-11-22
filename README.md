# Potentially planar degree sequences

This repository contains the Lean 4 proofs for two papers on degree sequences of finite simple planar graphs. Both developments use Lean 4.34.1 and share the graph library in [`lean/`](lean/).

| Paper | What the proofs cover | Start here |
| --- | --- | --- |
| *Obstructions to planar realizations of sparse graphic sequences* | Two sharp degree-sum classifications and their exceptional sequences | [Theorems and build instructions](#obstructions-to-planar-realizations-of-sparse-graphic-sequences) · [Version cited in the sparse paper](https://github.com/Myyura/sparse-planar-degree-sequences/tree/d7c9d0d15e1361f143fb2fae0ae3a383131c308f) |
| *The complexity of recognizing potentially planar degree sequences* | Hardness at the Euler bound, a constructive recognition algorithm, and structural criteria | [Theorem index and build instructions](recognition-complexity-paper/README.md) · [Source checksums](recognition-complexity-paper/verification/lean-sources.sha256) |

The sparse paper uses the original `lean/`, `lean-eg/`, and `verification/` directories. The recognition paper has its own [Lean projects and verification records](recognition-complexity-paper/). Its lockfiles refer to `sparse-boundary-paper/lean`, a relative symbolic link to the shared `lean/` directory. Clone with symbolic links enabled to reproduce both builds from the same checkout.

## Obstructions to planar realizations of sparse graphic sequences

Lean 4 formalization accompanying the paper *Obstructions to planar realizations of sparse graphic sequences*.

A degree sequence is *planaric* if some finite simple planar graph realizes it. Let $d$ be a positive graphic sequence of length $n$ and sum $S$, with $\ell$ entries equal to one. Theorem 1 shows that when $S \le 4n-2-2\ell$, the only exception to planar realizability is $(4^5,2)$ (five fours and a two). Theorem 2 classifies all exceptions at the next even sum, $S=4n-2\ell$.

## Main results

Write $p$ for the number of entries at least three and $t$ for the number of twos. Both corollaries concern the upper boundary $S=4n-2\ell$.

| Paper | Result | Lean declaration | File |
| --- | --- | --- | --- |
| Theorem 1 | Unique exception for $S \le 4n-2-2\ell$ | `SparseBoundary.first_boundary` | [FullBoundary.lean](lean-eg/FullBoundary.lean#L88) |
| Theorem 2 | All exceptions at $S=4n-2\ell$ | `SparseBoundary.second_boundary` | [FullBoundary.lean](lean-eg/FullBoundary.lean#L91) |
| Corollary 3 | $p \ge 8$ guarantees a planar realization for every $\ell$ | `SparseBoundary.upper_eight_core` | [BoundaryCorollaries.lean](lean-eg/BoundaryCorollaries.lean#L61) |
| Corollary 4 | For $t \ge 3$, the exceptions are exactly the sequences with $p=5$, or with $p=6$ and exactly three entries equal to three | `SparseBoundary.upper_with_three_twos` | [BoundaryCorollaries.lean](lean-eg/BoundaryCorollaries.lean#L7) |

For each $\ell$, [`seven_core_obstruction`](lean-eg/BoundaryCorollaries.lean#L82) gives an exception with $p=7$. The example [`two_twos_sharp`](lean-eg/BoundaryCorollaries.lean#L31) shows why Corollary 4 needs at least three twos.

## Building and verifying

The proofs are split into two Lake projects. [`lean/`](lean/) develops the graph constructions and obstruction proofs using Lean's standard library. Its [definition of planarity](lean/SparseBoundary/Graph.lean) uses Wagner's characterization by the exclusion of $K_5$ and $K_{3,3}$ as minors. [`lean-eg/`](lean-eg/) imports this development and uses the Erdős–Gallai theorem in mathlib's language of simple graphs to finish the classification.

### Quick check

With Git and [Elan](https://github.com/leanprover/elan) installed, start at the repository root. Elan picks up Lean 4.34.1 from the toolchain files. On the first build, Lake fetches the dependencies pinned in [the manifest](lean-eg/lake-manifest.json).

```sh
cd lean-eg
lake build BoundaryCorollaries
lake env lean ../verification/AuditEG.lean
```

[AuditEG.lean](verification/AuditEG.lean) spells out the hypotheses and the full exception list, then checks the two main theorems against those statements. The [axiom report](verification/axioms-main.log) lists `propext`, `Classical.choice`, and `Quot.sound` for both proofs.

### Full verification

The full check also uses Python 3.9 or later. Run this command from the repository root.

```sh
sh verification/verify.sh
```

This builds both projects, runs the audits, and rechecks the compiled declarations with the Lean kernel. The finite contraction certificates take the longest to replay. The [primary replay log](verification/kernel-primary.log) records the 147 modules checked by [replay.py](verification/replay.py). The [bridge replay log](verification/kernel-bridge.log) covers the five modules in `lean-eg/`.

### Finite check through ten vertices

With NetworkX installed, the following command tests all 4,356 positive graphic degree sequences through order ten in the range of the two theorems.

```sh
python3 verification/check_sequences.py --max-order 10
```

For each sequence, the script searches for a planar realization before consulting the classification. Through order ten it finds one exception among 3,290 sequences below the upper boundary and 200 among 1,066 sequences on it.

## Third-party code

[AtlasEG.lean](lean-eg/AtlasEG.lean) contains the [ATLAS proof of the Erdős–Gallai theorem](https://github.com/Deicyde/atlas-lean/blob/ced12319d64032bfe32565b312632d28eaf04e3c/MathlibExt/Combinatorics/SimpleGraph/ErdosGallai.lean) at commit `ced12319d64032bfe32565b312632d28eaf04e3c`. It retains the original copyright notice and [upstream license](lean-eg/LICENSE.atlas).
