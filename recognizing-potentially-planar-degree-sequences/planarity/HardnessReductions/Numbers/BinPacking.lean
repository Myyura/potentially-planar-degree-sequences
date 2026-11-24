import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import HardnessReductions.Core

/-!
# BIN PACKING

Do the items fit into the given number of bins of the given capacity?
Garey–Johnson's [SR1] — filed in this domain rather than in a folder of its
own for their storage-and-retrieval section, because the instance is a list of
numbers and two numbers, and the question is a sum bound on each part of a
partition: the domain's encoding and its aggregate combinator serve it
unchanged.

The instance is *not* the domain's shared `NumberTargetInstance`: two
distinguished numbers are needed, the capacity and the number of bins, and
they are read differently — one bounds a sum, the other counts the parts.

A packing is an **assignment of items to bins**, `Fin sizes.length → Fin bins`,
which is exactly Garey–Johnson's indexed partition `U₁, …, U_K` (their sets may
be empty, and so may a fibre here). It degenerates correctly at the edges: with
`bins = 0` and an item present there is no assignment at all, hence a
no-instance, while the empty item list packs into no bins.

Hardness proofs (in `BinPacking/`): from PARTITION (`FromPartition.lean`, two
bins and doubled sizes; certified in `FromPartition/Certified.lean`), and from
3-PARTITION inside its window (`FromPartition3.lean`, the numbers unchanged and
`n/3` bins; certified in `FromPartition3/Code.lean` and
`FromPartition3/Adequacy.lean`, unary at both ends, which is the entry's
*strong* hardness).
-/

namespace Hardness

/-- An instance of BIN PACKING: the item sizes, the capacity of a bin, and the
number of bins available. Duplicate entries of `sizes` are distinct items. -/
structure BinPackingInstance : Type where
  /-- The sizes of the items. -/
  sizes : List ℕ
  /-- The capacity of each bin. -/
  capacity : ℕ
  /-- The number of bins available. -/
  bins : ℕ

/-! ## Packings

The predicate, stated over an arbitrary indexed family `f : α → ℕ` so that
gadget constructions can work with tagged index types and transport to list
positions afterwards, as `IsSizedPartition` (`Numbers/Defs.lean`) is. -/

/-- `a` packs the items of `α` into `k` bins of capacity `cap`: no bin's items
have sizes totalling more than `cap`. -/
def IsPacking {α : Type} [Fintype α] (f : α → ℕ) (cap k : ℕ) (a : α → Fin k) : Prop :=
  ∀ b : Fin k, ∑ i ∈ Finset.univ.filter (fun i ↦ a i = b), f i ≤ cap

/-- BIN PACKING: can the items be assigned to the bins without exceeding any
bin's capacity? -/
def BIN_PACKING : Problem BinPackingInstance := fun x ↦
  ∃ a : Fin x.sizes.length → Fin x.bins,
    IsPacking (fun i ↦ x.sizes[i.1]) x.capacity x.bins a

/-! ### Exactly-full bins

The counting behind every reduction *from* BIN PACKING: what a packing must look
like when the items fill the available capacity exactly. -/

namespace IsPacking

variable {α : Type} [Fintype α] {f : α → ℕ} {cap k : ℕ} {a : α → Fin k}

/-- **The capacity bound**: everything packed fits in the total capacity. -/
theorem sum_le (h : IsPacking f cap k a) : ∑ i, f i ≤ k * cap := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ a f]
  calc ∑ b : Fin k, ∑ i ∈ Finset.univ.filter fun i ↦ a i = b, f i
      ≤ ∑ _b : Fin k, cap := Finset.sum_le_sum fun b _ ↦ h b
    _ = k * cap := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Rigidity**: if the items exactly exhaust the available capacity, every bin
is exactly full — no bin can be short, because the others cannot make up for
it. -/
theorem sum_fiber_eq (h : IsPacking f cap k a) (htotal : ∑ i, f i = k * cap)
    (b : Fin k) : ∑ i ∈ Finset.univ.filter (fun i ↦ a i = b), f i = cap := by
  classical
  have heq : ∑ b : Fin k, ∑ i ∈ Finset.univ.filter (fun i ↦ a i = b), f i
      = ∑ _b : Fin k, cap := by
    rw [Finset.sum_fiberwise Finset.univ a f, htotal, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact (Finset.sum_eq_sum_iff_of_le fun b _ ↦ h b).mp heq b (Finset.mem_univ b)

end IsPacking

/-- With no bins, packing is possible only when there is nothing to pack. -/
theorem exists_isPacking_zero_iff {n : ℕ} (l : Fin n → ℕ) (cap : ℕ) :
    (∃ a : Fin n → Fin 0, IsPacking l cap 0 a) ↔ n = 0 := by
  constructor
  · rintro ⟨a, -⟩
    by_contra hn
    exact (a ⟨0, Nat.pos_of_ne_zero hn⟩).elim0
  · rintro rfl
    exact ⟨id, fun b ↦ b.elim0⟩

/-! ### Transport of packings across reindexings

The renaming-invariance lemmas the entry owes its future gadgets, in the two
forms the library uses them: along an equivalence of index types, and for the
passage from an indexed family to its explicit listing. -/

/-- A fibre sum is unchanged by renaming the index type. -/
theorem sum_fiber_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β)
    (f : α → ℕ) {k : ℕ} (a : α → Fin k) (b : Fin k) :
    ∑ i ∈ Finset.univ.filter (fun i : α ↦ a i = b), f i
      = ∑ j ∈ Finset.univ.filter (fun j : β ↦ a (e.symm j) = b), f (e.symm j) := by
  refine Finset.sum_equiv e (fun i ↦ ?_) (fun i _ ↦ ?_) <;>
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]

/-- Packability transports along an equivalence of index types — the
renaming-invariance lemma gadget constructions and the representation pair
both consume. -/
theorem exists_isPacking_iff_map {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β)
    (f : α → ℕ) (cap k : ℕ) :
    (∃ a, IsPacking f cap k a) ↔ ∃ a, IsPacking (fun b ↦ f (e.symm b)) cap k a := by
  classical
  constructor
  · rintro ⟨a, h⟩
    exact ⟨fun b ↦ a (e.symm b), fun b ↦ (sum_fiber_equiv e f a b) ▸ h b⟩
  · rintro ⟨a, h⟩
    refine ⟨fun i ↦ a (e i), fun b ↦ ?_⟩
    rw [sum_fiber_equiv e f (fun i ↦ a (e i)) b]
    simpa only [Equiv.apply_symm_apply] using h b

/-- Packability only depends on the *number* of bins — the bookkeeping step for
a construction that produces its bins with one count and must deliver them with
another. -/
theorem exists_isPacking_congr_bins {α : Type} [Fintype α] (f : α → ℕ) (cap : ℕ)
    {k k' : ℕ} (hk : k = k') :
    (∃ a : α → Fin k, IsPacking f cap k a) ↔ ∃ a : α → Fin k', IsPacking f cap k' a := by
  subst hk; rfl

/-- Packing the positions of a *mapped* list is the same as packing the
positions of the original with the mapped sizes. The form a reduction whose
instance map rescales every size needs. -/
theorem exists_isPacking_map_iff (g : ℕ → ℕ) (l : List ℕ) (cap k : ℕ) :
    (∃ a, IsPacking (fun i : Fin (l.map g).length ↦ (l.map g)[i.1]) cap k a) ↔
      ∃ a, IsPacking (fun i : Fin l.length ↦ g l[i.1]) cap k a := by
  have hlen : (l.map g).length = l.length := List.length_map g
  rw [exists_isPacking_iff_map (finCongr hlen)]
  refine exists_congr fun a ↦ ?_
  have : (fun i : Fin l.length ↦ (l.map g)[((finCongr hlen).symm i).1])
      = fun i : Fin l.length ↦ g l[i.1] := by
    funext i
    exact List.getElem_map g
  rw [this]

end Hardness
