import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.SuccPred
import HardnessReductions.Core
import HardnessReductions.Numbers.Defs

/-!
# SUBSET SUM

Is there a subset of the given numbers summing to the target? The instance
type is the domain's shared `NumberTargetInstance` (`Numbers/Defs.lean`):
an explicit list of numbers plus a target, of which this entry asks the
subset-sum question. Selections are formulated as finsets of *indices* into
the list, never as sublists or subsets of values.

Hardness proof (in `SubsetSum/`): from VERTEX COVER (`FromVertexCover.lean`,
the base-4 digit construction; certified in `FromVertexCover/Code.lean` and
`FromVertexCover/Adequacy.lean`). The concrete encoding of SUBSET SUM
instances lives in `Numbers/Encoding.lean`.
-/

namespace Hardness

/-- SUBSET SUM: is there a set of indices whose entries sum to the target? -/
def SUBSET_SUM : Problem NumberTargetInstance :=
  fun x ↦ ∃ s : Finset (Fin x.nums.length), ∑ i ∈ s, x.nums[i.1] = x.target

/-- An index-selected sum is at most the sum of the whole list. -/
theorem sum_getElem_le_sum (l : List ℕ) (s : Finset (Fin l.length)) :
    ∑ i ∈ s, l[i.1] ≤ l.sum :=
  le_of_le_of_eq (Finset.sum_le_sum_of_subset (Finset.subset_univ s))
    (Fin.sum_univ_getElem l)

/-! ### Transport of subset-sum solvability across reindexings -/

/-- Subset-sum solvability transports along an equivalence of index types. -/
theorem exists_finsetSum_eq_iff_map {α β : Type} (e : α ≃ β) (f : α → ℕ) (t : ℕ) :
    (∃ s : Finset α, ∑ a ∈ s, f a = t) ↔ ∃ s : Finset β, ∑ b ∈ s, f (e.symm b) = t := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.map e.toEmbedding, ?_⟩
    rw [Finset.sum_map, ← hs]
    exact Finset.sum_congr rfl fun a _ ↦ congrArg f (e.symm_apply_apply a)
  · rintro ⟨s, hs⟩
    refine ⟨s.map e.symm.toEmbedding, ?_⟩
    rw [Finset.sum_map]
    exact hs

/-- Selecting positions of the list `List.ofFn g` is the same as selecting
indices of `g`: the passage from an indexed family of numbers to its explicit
listing preserves the subset sums. -/
theorem exists_subsetSum_ofFn_iff {n : ℕ} (g : Fin n → ℕ) (t : ℕ) :
    (∃ s : Finset (Fin (List.ofFn g).length), ∑ i ∈ s, (List.ofFn g)[i.1] = t) ↔
      ∃ s : Finset (Fin n), ∑ i ∈ s, g i = t := by
  have hlen : (List.ofFn g).length = n := List.length_ofFn
  have hget : ∀ i : Fin (List.ofFn g).length, (List.ofFn g)[i.1] = g (finCongr hlen i) :=
    fun i ↦ by rw [List.getElem_ofFn]; rfl
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.map (finCongr hlen).toEmbedding, ?_⟩
    rw [Finset.sum_map, ← hs]
    exact Finset.sum_congr rfl fun i _ ↦ (hget i).symm
  · rintro ⟨s, hs⟩
    refine ⟨s.map (finCongr hlen).symm.toEmbedding, ?_⟩
    rw [Finset.sum_map, ← hs]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hget ((finCongr hlen).symm.toEmbedding i)]
    exact congrArg g ((finCongr hlen).apply_symm_apply i)

end Hardness
