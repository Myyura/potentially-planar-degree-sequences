import SparseBoundary.Repair1
import SparseBoundary.Repair2
import SparseBoundary.Repair3
import SparseBoundary.Repair4
import SparseBoundary.Repair5
import SparseBoundary.Repair6
import SparseBoundary.Repair7

namespace SparseBoundary

/-- The seven planar realizations in the rotation-system table.
    Each property is stated for the ordinary simple graph and the
    forbidden-minor definition of planarity. -/
theorem finite_repairs_planaric {d : List Nat}
    (hd : d ∈ [[6,4,4,4,4,4,4,2], [6,5,5,5,5,3,3,2,2],
      [5,5,4,4,4,3,3], [5,4,4,4,4,4,4,3], [7,5,5,3,3,3,3,3],
      [6,6,5,3,3,3,3,3], [7,6,6,3,3,3,3,3,2]]) : Planaric d := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Repair1.planaric_repair
  · exact Repair2.planaric_repair
  · exact Repair3.planaric_repair
  · exact Repair4.planaric_repair
  · exact Repair5.planaric_repair
  · exact Repair6.planaric_repair
  · exact Repair7.planaric_repair

end SparseBoundary
