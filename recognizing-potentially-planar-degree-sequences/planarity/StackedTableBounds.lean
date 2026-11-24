import Listing
import Mathlib.Data.Multiset.Interval
import Mathlib.Data.Multiset.Sort

/-! The number of submultisets available to the three-coordinate disk table.
Padding by zeros gives an injection into the same partition tree as in the
fixed-order enumeration theorem. -/
namespace Recognition.StackedTable

def profileCount (d : List Nat) : Nat := (Finset.Iic (d : Multiset Nat)).card

theorem profileCount_product (d : List Nat) :
    profileCount d = ∏ x ∈ d.toFinset, (d.count x+1) := by
  simpa [profileCount] using Multiset.card_Iic (d : Multiset Nat)

theorem profileCount_fixed (d : List Nat) : profileCount d ≤ (d.length+1)^d.toFinset.card := by
  rw [profileCount_product]
  calc
    _ ≤ ∏ _x ∈ d.toFinset, (d.length+1) := Finset.prod_le_prod' fun x _ =>
      Nat.add_le_add_right (by simpa using Multiset.count_le_card x (d : Multiset Nat)) 1
    _ = _ := by simp

private def pad (n : Nat) (s : Multiset Nat) : List Nat :=
  (s + Multiset.replicate (n-s.card) 0).sort (·≥·)

private theorem pad_mem (d : List Nat) (mass : d.sum≤6*d.length) (s : Multiset Nat)
    (sub : s≤(d : Multiset Nat)) : pad d.length s ∈ Listing.candidates d.length := by
  rw [Listing.candidates_spec]
  obtain ⟨t,ht⟩ := Multiset.le_iff_exists_add.mp sub
  have card := congrArg Multiset.card ht
  have weight := congrArg Multiset.sum ht
  simp at card weight
  refine ⟨by simp [pad]; omega,Multiset.pairwise_sort ..,?_⟩
  have w := congrArg Multiset.sum (Multiset.sort_eq
    (s + Multiset.replicate (d.length-s.card) 0) (·≥·))
  change (pad d.length s).sum = (s + Multiset.replicate (d.length-s.card) 0).sum at w
  have sums : (pad d.length s).sum = s.sum := by simpa using w
  omega

private theorem pad_recover (d : List Nat) (positive : ∀ x∈d, 0<x)
    (s : Multiset Nat) (sub : s≤(d : Multiset Nat)) :
    ((pad d.length s : List Nat) : Multiset Nat).filter (0<·) = s := by
  have pos : ∀ x∈s, 0<x := fun x hx => positive x (Multiset.mem_of_le sub hx)
  simp only [pad,Multiset.sort_eq,Multiset.filter_add,Multiset.filter_eq_self.mpr pos]
  simp [Multiset.filter_eq_nil.mpr (show ∀ x∈Multiset.replicate (d.length-s.card) 0, ¬ 0<x from
    fun x hx => by have e : x=0 := Multiset.eq_of_mem_replicate hx; omega)]

theorem profileCount_sqrt (d : List Nat) (positive : ∀ x∈d, 0<x) (mass : d.sum≤6*d.length) :
    profileCount d ≤ 2^(18*(d.length.sqrt+1)) := by
  calc
    _ ≤ (Listing.candidates d.length).toFinset.card :=
      Finset.card_le_card_of_injOn (pad d.length)
        (fun s hs => List.mem_toFinset.mpr (pad_mem d mass s (Finset.mem_Iic.mp hs)))
        (fun a ha b hb h => by
          rw [← pad_recover d positive a (Finset.mem_Iic.mp ha),
            ← pad_recover d positive b (Finset.mem_Iic.mp hb)]
          rw [h])
    _ ≤ (Listing.candidates d.length).length := List.toFinset_card_le _
    _ ≤ _ := Listing.candidate_power _

end Recognition.StackedTable
