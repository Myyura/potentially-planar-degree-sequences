import SparseBoundary.SevenBoundary
import SparseBoundary.ExactSmall

namespace SparseBoundary

/-- Both exact boundary classifications, including arbitrary leaves and
    arbitrary label orders, for at most seven entries of degree at least three. -/
theorem exact_at_most_seven {d : List Nat} {j : Nat} (hj : j≤1)
    (ne : d≠[]) (pos : ∀ x∈d,1≤x) (hg : Graphic d)
    (sum : d.sum+2*j+2*d.count 1=4*d.length) (few : highCount d≤7) :
    Planaric d ↔ ¬exactBad j d := by
  have leafless (L : List Nat) (ln : L≠[]) (lm : ∀ x∈L,2≤x) (gr : Graphic L)
      (budget : L.sum+2*j=4*L.length) (small : highCount L≤7) (none : ¬exactBad j L) : Planaric L := by
    have p : ∀ x∈L,1≤x := fun x hx => Nat.le_trans (by decide) (lm x hx)
    have l0 : L.count 1=0 := List.count_eq_zero.mpr (fun h => by have := lm 1 h; omega)
    by_cases h6 : highCount L≤6
    · exact (exact_at_most_six hj ln p gr (by omega) h6).mpr none
    obtain ⟨h,t,core,pm⟩ := normalize_positive L p
    rw [l0] at pm
    have sl : h.length=7 := by
      have eq := pm.countP_eq (fun x => decide (3≤x))
      have fil : h.filter (fun x => decide (3≤x))=h := List.filter_eq_self.mpr (by simpa using core.2)
      have cap : highCount L=7 := by omega
      simpa [highCount,eq,profile,List.countP_eq_length_filter,fil] using cap
    have gp := (graphic_perm pm).mp gr
    rw [pm.sum_nat,pm.length_eq] at budget
    apply (planaric_perm pm).mpr
    by_cases top : j=0
    · exact (upper_seven_classified core sl gp (by simpa [top] using budget)).mpr
        (fun bad => none (by simpa [exactBad,top] using (exceptional_profile core pm).mpr bad))
    · have lo : j=1 := by omega
      exact lower_seven_classified core sl gp (by simpa [lo] using budget)
  refine ⟨?_, exact_leaf_reduction 7 j hj leafless d ne pos hg sum few⟩
  intro hp
  by_cases top : j=0
  · obtain ⟨h,t,core,pm⟩ := normalize_positive d pos
    intro bad
    exact upper_obstructions_nonplanar pm (by simpa [top] using sum)
      ((exceptional_profile core pm).mp (by simpa [exactBad,top] using bad)) hp
  · simpa [exactBad,top] using lower_necessary hp

end SparseBoundary
