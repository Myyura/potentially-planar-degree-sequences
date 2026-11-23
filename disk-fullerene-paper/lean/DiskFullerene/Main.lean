import DiskFullerene.PlaceGraph
import DiskFullerene.OrderedTrace
import DiskFullerene.LabelDisjoint
import DiskFullerene.TerminalCap
import DiskFullerene.CoreChord
import DiskFullerene.Minimum

namespace DiskFullerene
open Dual EndEuler EndFans StripFresh CanonicalIso

/-- Extract the canonical dual labeling from an arbitrary equality map. -/
theorem equality_labeling {M n} (G : IsDiskFullerene M (n+12)) (six : M.hexagons=6) :
    Nonempty (Labeling G) := by
  have hh : 3≤n+12 := by omega
  have cut := chord_small G (by omega) (by omega)
  obtain ⟨O⟩ := MiddlePath.extract G hh cut six
  obtain ⟨C⟩ := of_six (by omega) O.leftEnd O.leftSize
  obtain ⟨D⟩ := of_six (by omega) O.rightEnd O.rightSize
  obtain ⟨P,px,py,beginEdge,firstSide,load⟩ := start_seam hh C
  obtain ⟨Q,moves,path,_,_,marks,opp⟩ := MiddlePath.actual_trace G hh cut six O P beginEdge
    (by rw [firstSide]; exact O.leftRoot.2)
  have ends : (Q.x=D.weak ∧ Q.y=D.strong) ∨ (Q.y=D.weak ∧ Q.x=D.strong) := by
    have m := D.marks; grind
  obtain ⟨right,qx,qy⟩ := normalized_trace hh D path load (funext opp) ends
  have leftMarks : MarkedBy C P.x P.y := Or.inr ⟨px,py⟩
  have rightMarks : MarkedBy D Q.y Q.x := Or.inr ⟨qy,qx⟩
  have after (u) (hu : vertexSide O.rightEnd.seam O.rightEnd.side u=true) : sideOf Q u=false := by
    have a := (opp u).trans hu
    change vertexSide Q.cut Q.side u=false
    have flip (x y : Bool) : (x == !y) = true → (x == y) = false := by
      cases x <;> cases y <;> decide
    exact flip _ _ a
  obtain ⟨B⟩ := labeled_boundary C D hh path leftMarks rightMarks
    (fun u hit => (congrFun firstSide u).trans hit) after
  obtain ⟨nd,away,sep⟩ := chart_disjoint hh B leftMarks rightMarks O.apart
  exact place C D B right ⟨px,py⟩ ⟨qx,qy⟩ nd sep away

/-- The original cubic graphs, including arbitrary relabelings and
reflection, are isomorphic at equality. -/
theorem equality_iso {M N h} (hh : 12≤h) (G : IsDiskFullerene M h) (H : IsDiskFullerene N h)
    (sixM : M.hexagons=6) (sixN : N.hexagons=6) : GraphIso M N := by
  obtain ⟨n,eq⟩ : ∃ n, h=n+12 := ⟨h-12,by omega⟩
  subst h
  obtain ⟨C⟩ := equality_labeling G sixM
  obtain ⟨D⟩ := equality_labeling H sixN
  exact same_graph C D sixM sixN

/-- The full statement of Theorem 1 in the manuscript. -/
theorem main_theorem : MainStatement := by
  intro h hh
  obtain ⟨lower,G,valid,six,pentagons,order⟩ := minimum h hh
  exact ⟨lower,G,valid,six,pentagons,order,fun H other eq => equality_iso hh valid other six eq⟩

end DiskFullerene
