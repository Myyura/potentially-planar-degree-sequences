# Recognizing potentially planar degree sequences

**Zhe Zhang and Renwen Tian**

A list is potentially planar if it is the degree sequence of a finite simple planar graph. The Lean development covers the hardness reduction, recognition and construction, degree criteria, sparse obstructions and subdivision budgets.

## Theorem index

| Paper | Lean declarations and sources |
| --- | --- |
| Theorem 1.1. Strong NP-completeness at sum $6n-12$ | [Reduction and promises](planarity/HardnessResult.lean), [unary reduction](planarity/UnaryHardness.lean), [certificate verifier](planarity/RawVerifierResult.lean) |
| Theorem 1.2. Subexponential recognition and labelled construction | [Acceptance, labelled edges and running time](planarity/WireOutput.lean) |
| Theorem 2.1. Ordered interval criterion | [Equivalence with a successful run](planarity/RowRecognition.lean) |
| Proposition 2.2. Thirteen-vertex midpoint obstruction | [No family of simultaneous affine inequalities suffices](planarity/MidpointResult.lean), [endpoint witnesses](planarity/MidpointWitnesses.lean), [minimum repair budget of one](RecognizingPotentiallyPlanarDegreeSequences/MidpointRepair.lean) (`MidpointRepair.minimum_is_one`) |
| Theorem 2.3. Arithmetic criterion in the degrees | [Finite difference of a determinant](planarity/TraceDeterminant.lean) |
| Lemma 3.1. Exact minimum subdivision budget | [Attainment and equality with the support formula](RecognizingPotentiallyPlanarDegreeSequences/Support.lean), [suppression](RecognizingPotentiallyPlanarDegreeSequences/SupportSuppress.lean), [expansion](RecognizingPotentiallyPlanarDegreeSequences/SupportExpand.lean) |
| Theorems 3.2–3.3. The first two sparse layers beyond the Bar-Noy bound | [Full classification](sparse/FullBoundary.lean), [quantifiers and exception list](verification/AuditEG.lean) |
| Corollary 3.4. Eight core vertices suffice at the upper layer | [Threshold and seven-core examples](sparse/BoundaryCorollaries.lean), [the $p-6$ budget for maximal-sum lists](RecognizingPotentiallyPlanarDegreeSequences/Budget.lean) |
| Proposition 3.5 and Section 5. The fixed-order spectrum and extremal budget | [Lists attaining prescribed budgets](RecognizingPotentiallyPlanarDegreeSequences/Spectrum.lean), [the two bounds on the maximum](RecognizingPotentiallyPlanarDegreeSequences/Extremal.lean) |
| Lemmas 4.1–4.3. Encoding and eliminating prescribed edges | [Encoding](recognition/SourceMap.lean), [converse](recognition/SourceConverse.lean), [inverting a stellation](planarity/StellationResult.lean), [edge elimination](planarity/EliminationResult.lean) |
| Corollary A.1 and Appendix A.1. Maximal planar graphs and planar 3-trees | [Hardness and certificates](planarity/TargetLanguagesResult.lean), [stacked realizations](planarity/TargetStackedBridge.lean), [decision table and fixed-type cost](planarity/StackedTableResult.lean) |
| Theorem A.2. Hardness for each fixed positive budget and for $p/29-1$ when $29$ divides $p$ | [Both reductions and their promises](RecognizingPotentiallyPlanarDegreeSequences/FixedComplexity.lean), [geometric correctness](RecognizingPotentiallyPlanarDegreeSequences/FixedResult.lean), [NP verifier](RecognizingPotentiallyPlanarDegreeSequences/FixedVerifier.lean) |
| Lemmas D.1–D.2. Partial triangulations and the boundary catalogue | [Face transitions](planarity/FaceSearch.lean), [catalogue](planarity/CatalogueResult.lean) |
| Corollary D.3. Listing the degree multisets once each in subexponential total time | [Output specification, count bounds and running time](planarity/ListingResult.lean) |

## Scope

The proofs use a common [finite simple graph model](graphs/SparseBoundary/Graph.lean). The [Wagner bridge](planarity/EmbeddingBridge.lean) relates forbidden minors to the embedding model. Three statement types expose the classical inputs used in the paper. Completeness of the interval rule assumes a [canonical ordering](planarity/CanonicalRow.lean), completeness of the search assumes a [cost-weight planar separator](planarity/SeparatorInput.lean), and the determinant criterion assumes the [weighted matrix-tree expansion](planarity/KirchhoffInput.lean). Lean checks each implication with its input as a hypothesis.

The hardness statements provide explicit polynomial reductions from SAT and polynomially bounded bit certificates. Running-time declarations charge elementary operations in the recognition library. The paper uses SAT completeness and the simulation of these operations to state the conventional complexity consequences. The [planar 3-tree application](planarity/TargetLanguagesThreeTree.lean) invokes the classical equivalence with sequential face insertion. The sparse proof checks the classification on all orders. Section 3 gives the word-RAM time bound for its histogram algorithm. [Third-party sources and licenses](THIRD_PARTY.md)

## Build and verify

Run these commands from the **repository root**. [Elan](https://github.com/leanprover/elan) selects Lean 4.34.1. The [Lake manifest](../lake-manifest.json) fixes mathlib and its transitive dependencies.

```sh
paper=recognizing-potentially-planar-degree-sequences
lake exe cache get
lake build
lake env lean "$paper/Audit.lean"
shasum -a 256 -c "$paper/verification/lean-sources.sha256"
```

The public import is `RecognizingPotentiallyPlanarDegreeSequences`. The [principal declaration audit](Audit.lean) prints transitive axiom dependencies. The checksum list covers local Lean sources, configurations, lockfiles, third-party licenses, verification programs and their input data. Linux users may use `sha256sum -c`.

The full check also runs the detailed declaration audits, replays the recognition and budget modules with Lean's kernel checker, and checks the import closure of the graph library. It requires Python 3.9 or later. The graph replay writes its log to `.lake/kernel-primary.log`. [Replay procedure](verification/REPLAY.md)

```sh
sh "$paper/verification/verify.sh"
```

## Computational checks

The sparse check searches for a planar realization of each positive graphic degree multiset in the two ranges through ten vertices. It needs Python and NetworkX. The interval test uses the bundled graph-atlas data through seven vertices. An independent check of the two equality layers enumerates spanning subgraphs of triangulations using a C++17 compiler. It and the midpoint census require a [plantri executable](https://users.cecs.anu.edu.au/~bdm/plantri/).

```sh
python3 "$paper/verification/check_sequences.py" --max-order 10
python3 "$paper/verification/scripts/interval_degree_balances.py" --atlas
python3 "$paper/verification/scripts/midpoint_census.py" --plantri /path/to/plantri
python3 "$paper/verification/scripts/sparse_subgraphs.py" --plantri /path/to/plantri
```

The sparse search finds one obstruction among 3,290 lists below the upper layer and 200 among 1,066 on it. On the two equality layers the spanning-subgraph check examines 1,968 positive graphic degree multisets through ten vertices and finds 201 obstructions. The midpoint search finds no missing integer midpoint of two triangulation degree lists on four through twelve vertices. At thirteen vertices it finds five missing midpoints among 947 distinct profiles of 49,566 triangulations. [Verification scripts](verification/scripts/)
