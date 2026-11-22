# The complexity of recognizing potentially planar degree sequences

Lean 4 sources for the paper of the same title. A degree list is potentially planar if some simple planar graph realizes it. The paper proves NP-completeness at degree sum $6n-12$ and gives a deterministic algorithm that constructs a labelled realization in $O(L)+2^{O(\sqrt n)}$ time for an explicit input of $L$ bits and $n$ entries.

[Overview of both papers](../README.md)

## Reproduce the verification

Run the commands below from the Git repository root. Install [elan](https://github.com/leanprover/elan) to obtain the pinned Lean 4.34.1 toolchain and Lake. The first bridge build needs internet access for the mathlib revision and its recorded dependencies, or a local copy of those dependencies. The core package uses the included sparse-boundary package through a relative Lake dependency. Keep the three source directories in their recorded positions.

```sh
shasum -a 256 -c recognition-complexity-paper/verification/lean-sources.sha256

(
  cd recognition-complexity-paper/lean &&
  lake build &&
  lake env lean Audit.lean
)
(
  cd recognition-complexity-paper/lean-wagner &&
  lake exe cache get &&
  lake build &&
  lake env lean Audit.lean
)
```

On Linux, `sha256sum -c` also verifies the manifest. The [manifest](verification/lean-sources.sha256) covers 423 Lean source files and nine toolchain, Lake configuration and dependency files. Its SHA-256 digest is `a82b3e13a563b56c426afa50ab2818db4cacccff57cfc5f73202655e565d7cab`.

The [recorded kernel audit](verification/results/lean-kernel-audit.txt) gives the output for 24 core declarations and 443 bridge declarations. Across these 467 declarations Lean reports only `propext`, `Classical.choice` and `Quot.sound`. To replay the recorded 29 compiled modules after building, run the following in `recognition-complexity-paper/lean-wagner`.

```sh
lake env leanchecker --verbose \
  HardnessResult StellationResult EliminationResult PrescriptionCost UnaryHardness \
  TargetLanguagesResult TargetLanguagesWire TargetStackedBridge WireOutput \
  ListingResult CatalogueResult CompactBoundaryPrefix RowRecognition IntervalCosts \
  IntervalExamples FixedTypeLanguage StackedTableResult StackedCensus MidpointResult \
  WorkedMidpoint TraceDeterminant KirchhoffInput DiamondDeterminant EncodingExamples \
  FiniteRowChecksAtlas QuadraticTransfer CompactBoundaryMarks RawVerifierResult RawVerifierOrbit
```

## Where to find the results

| Paper result | Lean entry points |
| --- | --- |
| Theorem 1. NP-completeness at Euler equality, stacked positive witnesses and 3-connected realizations | [Hardness reduction](lean-wagner/HardnessResult.lean), [SAT reduction cost](lean-wagner/SATCost.lean), [certificate verifier](lean-wagner/RawVerifierResult.lean), [unary input](lean-wagner/UnaryHardness.lean) |
| Theorem 2. Subexponential decision and construction of a labelled realization | [Output graph and acceptance](lean-wagner/WireOutput.lean), [cost of the elementary algorithm](lean-wagner/ElementaryCost.lean) |
| Lemma 3. Encoding 3-PARTITION by prescribed edges | [Construction](lean/SourceMap.lean), [recovery of a partition](lean/SourceConverse.lean) |
| Lemmas 4–5. Inverting a stellation and eliminating bounded-degree edge prescriptions | [Single layer](lean-wagner/StellationResult.lean), [edge elimination](lean-wagner/EliminationResult.lean), [encoding cost](lean-wagner/PrescriptionCost.lean) |
| Corollaries 6–7. Maximal planar graphs, planar 3-trees and complete face-size lists | [Target languages](lean-wagner/TargetLanguagesResult.lean), [stacked witnesses](lean-wagner/TargetStackedBridge.lean), [polytope duality](lean-wagner/PolytopeDual.lean) |
| Lemmas 8–9. Face transitions and a catalogue of boundaries for each order | [Face search](lean-wagner/FaceSearch.lean), [boundary catalogue](lean-wagner/CatalogueResult.lean) |
| Corollary 10. Listing every realizable degree multiset of a given order | [Enumeration, runtime and output size](lean-wagner/ListingResult.lean) |
| Theorem 11. Ordered interval moves | [Equivalence and prescribed last entry](lean-wagner/RowRecognition.lean), [search cost](lean-wagner/IntervalCosts.lean) |
| Theorem 12. Disk quotas for stacked triangulations | [Quota rule](lean-wagner/StackedQuota.lean), [sequential stacking](lean-wagner/StackedHistory.lean), [decision table and cost](lean-wagner/StackedTableResult.lean) |
| Theorem 13. Arithmetic criterion from the spherical term | [Determinant criterion](lean-wagner/TraceDeterminant.lean), [matrix-tree input](lean-wagner/KirchhoffInput.lean), [worked example](lean-wagner/DiamondDeterminant.lean) |

Further statements cover the [13-vertex midpoint obstruction](lean-wagner/MidpointResult.lean) and [sparsity at fixed numbers of degree values](lean-wagner/FixedTypeLanguage.lean). The [finite comparison](lean-wagner/FiniteRowChecksAtlas.lean) records the bit encodings used to compare the interval rule through order seven with the [accompanying graph-atlas data](verification/data/atlas_summary.json).

## Imported results and hypotheses

The planar-embedding equivalence and the SAT source reductions use upstream Lean proofs. The algorithm takes the [cost-weight planar separator theorem](lean-wagner/SeparatorInput.lean) as an explicit hypothesis for completeness. Its cost bound and the soundness of a returned graph are unconditional. The implication from a realization to an interval run uses a [canonical ordering](lean-wagner/CanonicalRow.lean). The arithmetic criterion takes the [weighted matrix-tree theorem](lean-wagner/KirchhoffInput.lean) as an input. These hypotheses appear in the statement types.

The geometric corollaries use the paper's [Steinitz and polarity interface](lean-wagner/TargetLanguagesPolarity.lean). The planar 3-tree corollary uses the classical relation between planar 3-trees and sequential face insertion. The conventional complexity-class consequences use CNF-SAT completeness, standard machine simulation for the cost models and, for the fixed-type consequence, Mahaney's theorem. [Third-party sources and licenses](THIRD_PARTY.md)
