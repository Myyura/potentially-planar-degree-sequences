# Planar realizations of graphic sequences at the sparse boundary

This repository contains the Lean 4 proofs accompanying the paper of the same title. For a positive graphic sequence with length $n$, degree sum $S$, and $\ell$ entries equal to one, the first theorem proves that $(4,4,4,4,4,2)$ is the unique sequence without a planar realization when $S\le 4n-2-2\ell$. The second theorem classifies all exceptions when $S=4n-2\ell$.

| Result | Lean declaration |
| --- | --- |
| Lower boundary and the entire range below it | `SparseBoundary.first_boundary` |
| Complete classification on the upper boundary | `SparseBoundary.second_boundary` |
| Upper boundary with at least eight core vertices | `SparseBoundary.upper_eight_core` |
| Upper boundary with at least three degree-two vertices | `SparseBoundary.upper_with_three_twos` |

The main theorems and corollaries are proved for finite simple graphs. Planarity is expressed using Wagner's characterization by the two excluded minors. The audit independently restates the hypotheses and exception list and type-checks the two main proofs against those statements. [Main theorems](lean-eg/FullBoundary.lean) · [Corollaries and sharpness examples](lean-eg/BoundaryCorollaries.lean) · [Theorem statements and axiom audit](verification/AuditEG.lean) · [Graph definitions](lean/SparseBoundary/Graph.lean)

## Reproducing the proofs

Install Git, the Elan toolchain manager and Python 3.9 or later. From the repository root, run the following in a POSIX shell.

```sh
sh verification/verify.sh
```

Elan selects Lean 4.34.1 from the toolchain files. On a first build, allow network access to fetch the toolchain and the dependencies pinned in the Lake manifest. The script builds both projects, checks the theorem statements and axiom dependencies, and replays their compiled declarations through the Lean kernel. Replaying the finite contraction certificates can take substantial time. [Dependency manifest](lean-eg/lake-manifest.json) · [Kernel replay script](verification/replay.py)

For the two classification theorems and the corollaries alone, run the following from the repository root.

```sh
cd lean-eg
lake build BoundaryCorollaries
lake env lean ../verification/AuditEG.lean
```

The recorded audits list `propext`, `Classical.choice` and `Quot.sound` as the axiom dependencies of the two main theorems. The kernel replay covers 147 modules in the primary project and five in the second project. [Axiom report](verification/axioms-main.log) · [Primary replay](verification/kernel-primary.log) · [Second project replay](verification/kernel-bridge.log)

## Third-party source

`lean-eg/AtlasEG.lean` is the ATLAS formalization of the Erdős–Gallai theorem at commit `ced12319d64032bfe32565b312632d28eaf04e3c`. The source retains its copyright notice and is distributed with its upstream license. [Upstream source](https://github.com/Deicyde/atlas-lean/blob/ced12319d64032bfe32565b312632d28eaf04e3c/MathlibExt/Combinatorics/SimpleGraph/ErdosGallai.lean) · [License for AtlasEG.lean](lean-eg/LICENSE.atlas)
