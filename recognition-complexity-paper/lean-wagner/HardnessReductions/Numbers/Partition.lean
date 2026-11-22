import Mathlib.Algebra.BigOperators.Fin
import HardnessReductions.Core

/-!
# PARTITION

Can a list of numbers be split into two halves of equal sum? The instance
carries an explicit list, in keeping with the size-model discipline (every
item is represented, and duplicates are distinct items), so selections are
formulated as finsets of *indices*.

Hardness proof (in `Partition/`): from SUBSET SUM (`FromSubsetSum.lean`,
padding; certified in `FromSubsetSum/Certified.lean`, using the
aggregate combinator `Code.listSum`).
-/

namespace Hardness

/-- An instance of PARTITION: a list of natural numbers to be split into two
halves of equal sum. Duplicate entries of `nums` are distinct items. -/
structure PartitionInstance : Type where
  /-- The numbers to be split. -/
  nums : List ℕ

/-- PARTITION: can the indices be split into two parts of equal sum?
Formulated as: is there a set of indices whose entries sum to half the
total (the complementary set then sums to the other half)? -/
def PARTITION : Problem PartitionInstance :=
  fun x ↦ ∃ s : Finset (Fin x.nums.length), 2 * ∑ i ∈ s, x.nums[i.1] = x.nums.sum

end Hardness
