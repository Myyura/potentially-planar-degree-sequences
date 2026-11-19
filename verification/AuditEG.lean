import BoundaryCorollaries
open SparseBoundary

/-- These type ascriptions check both quantifier domains and the directions
of the two implications against the manuscript's formulations. -/
example : ∀ d : List Nat, d≠[] → (∀ v∈d,1≤v) → Graphic d →
    d.sum+2+2*d.count 1≤4*d.length → (Planaric d ↔ ¬d.Perm [4,4,4,4,4,2]) :=
  first_boundary

example : ∀ (d h : List Nat) (t l : Nat), d≠[] → Core h →
    d.Perm (profile h t l) → Graphic d → d.sum+2*l=4*d.length →
    (¬Planaric d ↔
      h.length=5 ∨ (∃a b c,4≤c ∧ h=[a,b,c,3,3,3]) ∨
      profile h t l=(5+l)::([4,4,4,4,3]++List.replicate l 1) ∨
      profile h t l=(6+l)::([4,4,4,4,4,2]++List.replicate l 1) ∨
      profile h t l=(6+l)::([5,5,3,3,3,3]++List.replicate l 1) ∨
      profile h t l=[5,5,5,5,5,3,2,2] ∨ profile h t l=[4,4,4,4,4,4,4] ∨
      profile h t l=[6,6,6,3,3,3,3,2]) := second_boundary

example (d : List Nat) (pos : ∀ v ∈ d, 1 ≤ v) (hg : Graphic d)
    (sum : d.sum + 2*d.count 1 = 4*d.length) (hp : 8 ≤ highCount d) :
    Planaric d := upper_eight_core d pos hg sum hp

example (d : List Nat) (pos : ∀ v ∈ d, 1 ≤ v) (hg : Graphic d)
    (sum : d.sum + 2*d.count 1 = 4*d.length) (ht : 3 ≤ d.count 2) :
    ¬Planaric d ↔ highCount d = 5 ∨ (highCount d = 6 ∧ d.count 3 = 3) :=
  upper_with_three_twos d pos hg sum ht

#print axioms first_boundary
#print axioms second_boundary
#print axioms large_exact_verified
#print axioms full_iff_large
#print axioms ErdosGallai.graphic_boundary_criterion
#print axioms ErdosGallai.graphic_sparse_criterion
#print axioms ErdosGallai.graphic_sparse_iff_degree_cap
#print axioms MathlibExt.Combinatorics.SimpleGraph.ErdosGallaiWanted.erdos_gallai

#print axioms second_boundary_invariant
#print axioms first_with_isolates
#print axioms second_with_isolates

#print axioms upper_eight_core
#print axioms seven_core_obstruction
#print axioms seven_core_companion
#print axioms seven_core_same_statistics
#print axioms upper_with_three_twos
#print axioms two_twos_sharp
