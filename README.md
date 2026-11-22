# Potentially planar degree sequences

A degree sequence is *potentially planar* if some finite simple planar graph has those vertex degrees. This repository contains Lean 4 proofs for two papers. The first classifies the obstructions at two sparse degree-sum bounds. The second studies recognition for arbitrary degree lists.

| Paper | Proofs and reproduction | Version cited in the paper |
| --- | --- | --- |
| *Obstructions to planar realizations of sparse graphic sequences* | [Theorem statements and build guide](sparse-boundary-paper/README.md) | [`d7c9d0d15e13`](https://github.com/Myyura/potentially-planar-degree-sequences/tree/d7c9d0d15e1361f143fb2fae0ae3a383131c308f) |
| *The complexity of recognizing potentially planar degree sequences* | [Theorem statements and build guide](recognition-complexity-paper/README.md) | [`491655549ad0`](https://github.com/Myyura/potentially-planar-degree-sequences/tree/491655549ad01b4058436be445733945655da14b/recognition-complexity-paper) |

<a id="main-results"></a>

## Obstructions to planar realizations of sparse graphic sequences

Let $d$ be a nonempty positive graphic sequence of length $n$ and sum $S$, with $\ell$ entries equal to one.

- **Theorems 1–2.** If $S\le 4n-2-2\ell$, every such sequence has a planar realization except $(4,4,4,4,4,2)$. At the next even sum, $S=4n-2\ell$, Theorem 2 gives the complete list of obstructions. [Classification](lean-eg/FullBoundary.lean) · [Full exception list](verification/AuditEG.lean)
- **Corollaries 3–4.** At $S=4n-2\ell$, write $p$ for the number of entries at least three. Every sequence with $p\ge8$ admits a planar realization, and for each leaf count $\ell$ there is an exception with $p=7$. If at least three entries equal two, the obstructions are exactly the sequences with $p=5$, or with $p=6$ and precisely three entries equal to three. [Corollaries and sharpness examples](lean-eg/BoundaryCorollaries.lean)

## The complexity of recognizing potentially planar degree sequences

- **Theorem 1.** Recognition is strongly NP-complete even when $n\ge4$, every degree is at least three, and the sum is $6n-12$. Every output of the reduction admits a 3-connected simple realization. Each positive output has a stacked triangulation realization. Corollaries 6–7 extend hardness to recognition for maximal planar graphs, planar 3-trees and complete face-size lists of simple convex 3-polytopes. [Reduction](recognition-complexity-paper/lean-wagner/HardnessResult.lean) · [Unary encoding](recognition-complexity-paper/lean-wagner/UnaryHardness.lean)
- **Theorem 2 and Corollary 10.** For an explicitly listed input of $n$ degrees and bit length $L$, a deterministic algorithm decides realizability in $O(L)+2^{O(\sqrt n)}$ time. On a positive input it constructs a planar realization on the input labels within the same bound. All realizable degree multisets of order $n$ can be listed once each in $2^{O(\sqrt n)}$ total time. Their number, $2^{\Theta(\sqrt n)}$, gives a matching lower bound for enumeration. A matching lower bound for deciding one list remains open. [Labelled construction](recognition-complexity-paper/lean-wagner/WireOutput.lean) · [Enumeration](recognition-complexity-paper/lean-wagner/ListingResult.lean)
- **Theorems 11–13.** A list has a planar realization exactly when ordered interval moves can consume its positive entries and leave an empty row. For stacked triangulations, a recurrence distributes the entries among the four faces of a tetrahedron and gives a polynomial-time test when the number of distinct degrees is fixed. The appendix gives an arithmetic criterion using a finite difference of a determinant polynomial. [Interval moves](recognition-complexity-paper/lean-wagner/RowRecognition.lean) · [Stacked triangulations](recognition-complexity-paper/lean-wagner/StackedTableResult.lean) · [Arithmetic criterion](recognition-complexity-paper/lean-wagner/TraceDeterminant.lean)

## Building and verifying

Both developments use Lean 4.34.1 and share the graph library in [lean/](lean/). Install [elan](https://github.com/leanprover/elan) and start at the repository root. Preserve the symbolic link `sparse-boundary-paper/lean` when cloning. Lake uses the toolchain and dependency revisions recorded in each project.

<a id="quick-check"></a>

**Sparse classification.** To build the classification and check the formal statements against the paper, run

```sh
(cd lean-eg && lake build BoundaryCorollaries && lake env lean ../verification/AuditEG.lean)
```

<a id="full-verification"></a>
<a id="finite-check-through-ten-vertices"></a>

The full verification uses `sh verification/verify.sh`. An independent finite search covers all 4,356 positive graphic degree multisets through order ten in the two stated ranges. [Build, kernel replay and finite search](sparse-boundary-paper/README.md#building-and-verifying) · [Scope of the sparse proofs](verification/STATUS.md)

**General recognition.** To build both projects and reproduce the declaration audits, run

```sh
(cd recognition-complexity-paper/lean && lake build && lake env lean Audit.lean)
(cd recognition-complexity-paper/lean-wagner && lake exe cache get && lake build && lake env lean Audit.lean)
```

The recorded run audits 467 declarations and replays 29 compiled modules. The theorem index identifies external inputs, including the cost-weight separator for completeness of the search, canonical ordering for the interval criterion, and the weighted matrix-tree theorem for the determinant criterion. [Verification and source checksums](recognition-complexity-paper/README.md#reproduce-the-verification) · [Scope of the recognition proofs](recognition-complexity-paper/README.md#imported-results-and-hypotheses)

## Third-party code

The sparse project includes the ATLAS proof of the Erdős–Gallai theorem. The recognition project includes the Wagner formalization by Juan Pablo Traverso Gianini and the hardness reductions by Dominik Peters. [ATLAS source and license](sparse-boundary-paper/README.md#third-party-code) · [Recognition dependencies and licenses](recognition-complexity-paper/THIRD_PARTY.md)
