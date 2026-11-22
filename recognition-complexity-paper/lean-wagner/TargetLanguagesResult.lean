import TargetLanguagesThreeTree
import TargetLanguagesPolarity
import UnaryHardness

/-! One computed output and its three graph-class consequences. -/
namespace Recognition.TargetLanguages
open SparseBoundary

theorem planar_three_tree_reduction (structural : ThreeTreeClass.KratochvilVaner) :
    (∃ C k : Nat,∀ bs : List Bool,(SATCost.run bs).2≤C*(bs.length+1)^k) ∧
    (∀ bs,SATBridge.SATLanguage bs ↔ Wire.degreeLanguage ThreeTreeClass.Row (SATCost.run bs).1) ∧
    ∀ ds : List Nat,ThreeTreeClass.Row ds ↔ ∃ w : List Bool,w.length≤3*ds.length ∧
      ThreeTreeClass.ordinaryCheck ds w=true :=
  ⟨SATCost.run_work,ThreeTreeClass.sat_reduction structural,ThreeTreeClass.full_certificate structural⟩

theorem polytope_reduction {P} (S : SteinitzPolarity P) (bs : List Bool) :
    SATBridge.SATLanguage bs ↔ Wire.degreeLanguage (FaceList S) (SATCost.run bs).1 := by
  simpa only [Wire.degreeLanguage,geometric_face_list S] using (reductions bs).2.2

theorem truncated_positive_outputs {P} (C : CornerPolarity P) (bs : List Bool)
    (yes : SATBridge.SATLanguage bs) : ∃ ds,Wire.readDegrees (SATCost.run bs).1=some ds ∧
      ∃ a b,C.isTetrahedron a ∧ Relation.ReflTransGen C.cut a b ∧ C.profile b=(ds : Multiset Nat) := by
  obtain ⟨ds,read,_,hs⟩ := (reductions bs).2.1.mp yes
  exact ⟨ds,read,truncated_realization C ((TargetStackedBridge.sequential_iff ds).mp hs)⟩

end Recognition.TargetLanguages
