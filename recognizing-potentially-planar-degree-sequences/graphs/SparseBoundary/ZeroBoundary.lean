import SparseBoundary.ZeroTypes
import SparseBoundary.ZeroMany
import SparseBoundary.ZeroSeeds0
import SparseBoundary.ZeroSeeds1
import SparseBoundary.ZeroSeeds2

namespace SparseBoundary.ZeroCore

private theorem seeds (p : Nat) (size : 8≤p) : TwoThreeProfiles p := by
  have six := repeat_six [6,3,3] (by decide) ZeroSeeds1.two p size
  have fives := repeat_six [5,5,3,3] (by decide) ZeroSeeds2.two p size
  have fours := repeat_six [3,3] (by decide) ZeroSeeds0.two p size
  refine ⟨(planaric_perm ?_).mp six,(planaric_perm ?_).mp fives,(planaric_perm ?_).mp fours⟩ <;>
    apply List.perm_iff_count.mpr <;> intro i <;>
    simp only [List.length_cons,List.length_nil,Nat.reduceAdd,List.count_append,List.count_cons,List.count_nil] <;> omega

/-- For at most two threes, the four nonconstant families reduce to
    finitely many sizes by adjoining disjoint octahedra. -/
theorem few (j : Nat) (hj : j≤1) (h : List Nat) (size : 8≤h.length)
    (core : Core h) (vol : h.sum+2*j=4*h.length) (_cap : ∀ x∈h,x+1≤h.length)
    (threes : h.count 3≤2) (four : h.count 3=0 → Planaric h) : Planaric h := by
  by_cases empty : h.count 3=0
  · exact four empty
  by_cases one : h.count 3=1
  · apply one_from_profile h j hj core size vol one
    exact repeat_six [5,3] (by decide) ZeroSeeds0.one h.length size
  exact two_from_profiles h j hj core size vol (by omega) (seeds _ size)

/-- Zero-subdivision reduction for either equality layer. -/
theorem zero (j : Nat) (hj : j≤1) (h : List Nat) (size : 8≤h.length)
    (core : Core h) (vol : h.sum+2*j=4*h.length) (cap : ∀ x∈h,x+1≤h.length)
    (four : h.count 3=0 → Planaric h)
    (smaller : ∀ r : List Nat, 8≤r.length → r.length+2=h.length → Core r →
      r.sum+2*j=4*r.length+2 → (∀ x∈r,x≤r.length) → Planaric (2::r)) : Planaric h := by
  by_cases low : h.count 3≤2
  · exact few j hj h size core vol cap low four
  exact many j hj h size core vol cap (by omega) smaller

end SparseBoundary.ZeroCore
