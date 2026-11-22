# Third-party sources

The following paths are relative to `recognition-complexity-paper/lean-wagner/`. Each license applies to its respective upstream sources.

## Wagner’s theorem

The files under `LeanPool/` are the 33 transitive source dependencies of the formal Wagner theorem by Juan Pablo Traverso Gianini. The sources are vendored at commit `5b262124ae6c99661cf1e75bd0351cc7faab80c5`, dated 2 November 2026, under the Apache License 2.0. The original headers and the license are included. [Upstream snapshot](https://github.com/jtraverso/planar-list-colouring/tree/5b262124ae6c99661cf1e75bd0351cc7faab80c5) · [License](lean-wagner/LeanPool/LICENSE)

This upstream snapshot targets Lean 4.35.0-rc3. The bundled version uses the project's Lean 4.34.1 and mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. The local modifications affect import declarations in five upstream modules. The theorem statements and proof terms in their sources are preserved.

| Upstream module | Change for the pinned build |
| --- | --- |
| `Planar.Orbits` | Name the permutation-cycle, degree-sum and tactic imports individually. |
| `Reach` and `Wagner.CyclicWord` | Name the required mathlib imports individually. |
| `Planar.Examples` and `Wagner.Separation` | Import the finite-vector literal notation used by the original proofs. |

Lake obtains mathlib and its transitive dependencies at the revisions recorded in `lake-manifest.json`. A fresh checkout requires network access for these dependencies.

## Hardness reductions

The 33 dependencies under `HardnessReductions/` come from Dominik Peters's *Hardness Reductions in Lean*, at commit `786ea48cdea8513c00d935d4058bdde039af2dff` of 6 November 2026, distributed under the MIT License. Its original toolchain is Lean 4.32.0. The local port replaces a renamed mathlib import in `Core`, gives explicit unfolding in three proof steps of `Numbers.Partition3.FromPartition4`, spells out a Boolean case split in `Logic.OneInThree3Sat`, and closes a definitional equality explicitly in `Logic.Sat.Encoding`. The definitions of the source programs, predicates and reduction theorems are preserved. Upstream proofs using older tactic lemma names may emit deprecation notices on Lean 4.34.1. [Upstream snapshot](https://github.com/DominikPeters/HardnessReductionsLean/tree/786ea48cdea8513c00d935d4058bdde039af2dff) · [License](lean-wagner/HardnessReductions/LICENSE)
