import MidpointResult
import TracePlanarity

/-! A spherical triangular host for the thirteen-vertex midpoint after
appending a single degree two. -/
namespace RecognizingPotentiallyPlanarDegreeSequences.MidpointRepair
open SparseBoundary Recognition

/-- In the upper endpoint witness, labels 3, 0 and 1 have degrees
12, 9 and 5. Insert label 13 into face (1, 2, 3). The desired spanning
subgraph omits the old edge (0, 3) and the new edge (2, 13). -/
private def face (a b c : Nat) : TraceCheck.Record (PlanarDegrees.Frontier.cost 13) :=
  let keep (x y : Nat) := !((x == 0 && y == 3) || (x == 2 && y == 13))
  ⟨BitVec.ofNat _ a, BitVec.ofNat _ b, BitVec.ofNat _ c,
    keep a b, keep a c, keep b c⟩

private def host : TraceCheck.Records 13 23 :=
  #v[face 0 1 2, face 0 1 4, face 0 2 3, face 0 3 12,
     face 0 4 6, face 0 6 7, face 0 7 9, face 0 9 10,
     face 0 10 12, face 1 2 13, face 1 3 5, face 1 3 13,
     face 1 4 5, face 2 3 13, face 3 4 5, face 3 4 6,
     face 3 6 8, face 3 7 8, face 3 7 9, face 3 9 11,
     face 3 10 11, face 3 10 12, face 6 7 8, face 9 10 11]

/-- The least number of appended twos for the missing integer midpoint is one. -/
theorem one_two_suffices : Planaric (MidpointResult.middle ++ [2]) := by
  apply TracePlanarity.verify_planaric (r := host)
  decide +kernel

theorem minimum_is_one : ¬ Planaric MidpointResult.middle ∧
    Planaric (MidpointResult.middle ++ [2]) :=
  ⟨MidpointResult.middle_nonplanaric, one_two_suffices⟩

end RecognizingPotentiallyPlanarDegreeSequences.MidpointRepair
