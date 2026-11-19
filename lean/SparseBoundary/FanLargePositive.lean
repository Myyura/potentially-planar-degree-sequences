import SparseBoundary.FanSingleThree
import SparseBoundary.FourSingleton
import SparseBoundary.GraphSmallBudget

namespace SparseBoundary.Fan.Three

/-- All upper-boundary cores of order at least eight with at least two
subdivision vertices admit a planar realization. -/
theorem upper_two {h : List Nat} {t : Nat} (size : 8≤h.length)
    (two : 2≤t) (input : Input h t) : Planaric (List.replicate t 2++h) :=
  upper_of_minimum_four (fun _ _ => FourCore.upper_fours) size two input

/-- At one subdivision vertex, only the profiles with at most one three
must be supplied separately. -/
theorem upper_positive_from_one
    (one : ∀ h : List Nat, 8≤h.length → Input h 1 → h.count 3≤1 → Planaric (2::h))
    {h : List Nat} {t : Nat} (size : 8≤h.length) (pos : 1≤t) (input : Input h t) :
    Planaric (List.replicate t 2++h) := by
  apply upper_of_at_most_one _ size pos input
  intro r s sz ps data few
  by_cases two : 2≤s
  · exact upper_two sz two data
  · have eq : s=1 := by omega
    subst s
    exact one r sz data few

/-- Every upper-boundary core of order at least eight with positive
subdivision budget has a planar realization. -/
theorem upper_positive {h : List Nat} {t : Nat} (size : 8≤h.length) (pos : 1≤t)
    (input : Input h t) : Planaric (List.replicate t 2++h) := by
  apply upper_positive_from_one _ size pos input
  intro r large data few
  obtain ⟨⟨so,lo⟩,vol,cap⟩ := data
  by_cases single : r.count 3=1
  · exact FourCore.small_budget_one_three large (by decide : 1≤1) so lo single vol
  · apply FourCore.small_budget_min_four large (by decide : 1≤1) ⟨so,?_,vol,cap⟩
    intro i hi
    have low := lo i hi
    have ne : i≠3 := by
      rintro rfl
      have nz := List.count_pos_iff.mpr hi
      omega
    omega

end SparseBoundary.Fan.Three
