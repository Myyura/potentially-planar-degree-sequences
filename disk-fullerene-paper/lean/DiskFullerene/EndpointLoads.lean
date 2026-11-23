import DiskFullerene.CertifiedCap
import DiskFullerene.StripTrace

namespace DiskFullerene.Dual
open EndFans EndEuler Strip

theorem start_seam {M} {G : IsDiskFullerene M h} (hh : 3≤h) {d : EndPiece M G} (L : Cap d) :
    ∃ P : SeamState G, P.x=L.strong ∧ P.y=L.weak ∧ P.cut.xy=d.seam.xy ∧
      vertexSide P.cut P.side = vertexSide d.seam d.side ∧ P.loads=⟨3,2⟩ := by
  have ⟨lw,ls⟩ := L.seam_loads hh
  rcases L.marks with ⟨wk,st⟩|⟨wk,st⟩
  · refine ⟨⟨_,_,d.seam.swapMarks,d.side⟩,st.symm,wk.symm,rfl,rfl,?_⟩
    change Loads.mk (loadAt d.seam d.side _) (loadAt d.seam d.side _) = _
    rw [st] at ls; rw [wk] at lw
    exact Loads.mk.injEq .. |>.mpr ⟨ls,lw⟩
  · refine ⟨⟨_,_,d.seam,d.side⟩,st.symm,wk.symm,rfl,rfl,?_⟩
    change Loads.mk (loadAt d.seam d.side _) (loadAt d.seam d.side _) = _
    rw [st] at ls; rw [wk] at lw
    exact Loads.mk.injEq .. |>.mpr ⟨ls,lw⟩

theorem load_congr {M} {G : IsDiskFullerene M h} {w x y a c e}
    (S : TriangleSide G w x y) (T : TriangleSide G a c e) {b d}
    (eq : vertexSide S b=vertexSide T d) (f : Face M) : loadAt S b f=loadAt T d f := by
  classical
  apply congrArg (· - 1)
  apply List.countP_congr
  intro v hv
  obtain ⟨i,hi,id⟩ := List.mem_iff_getElem.mp hv
  have m := dart_info G (incident_dart G (sideDart_mem M f ⟨i,hi⟩))
  have src := side_at M.faces[f.val] i hi
  change sideDart M f ⟨i,hi⟩ = _ at src
  rw [src] at m
  have ok : v<M.ord := id ▸ m.1
  let k : Fin M.ord := ⟨v,ok⟩
  have z := congrFun eq k
  have phys {w x y} (R : TriangleSide G w x y) (side) : primalLabelSide R side v = vertexSide R side k := by
    have relation : R.color v ↔ R.part.left k := ⟨fun ⟨_,h⟩ => h,fun h => ⟨ok,h⟩⟩
    simp [primalLabelSide,vertexSide,relation]
  rw [phys S b,phys T d,z]

theorem normalized_trace {M} {G : IsDiskFullerene M h} (hh : 3≤h) {d : EndPiece M G} (R : Cap d)
    {P Q : SeamState G} {moves} (path : ActualTrace P moves Q) (start : P.loads=⟨3,2⟩)
    (opposite : vertexSide Q.cut (!Q.side)=vertexSide d.seam d.side)
    (marks : (Q.x=R.weak ∧ Q.y=R.strong) ∨ (Q.y=R.weak ∧ Q.x=R.strong)) :
    moves=List.replicate moves.length .right ∧ Q.x=R.weak ∧ Q.y=R.strong := by
  have lw := R.seam_loads hh
  have fit (i) := load_congr Q.cut d.seam opposite i
  rcases marks with ⟨x,y⟩|⟨y,x⟩
  · have ok := trace_complete hh path (g:=.twoThree) (by
      rw [fit,fit,x,y,lw.1,lw.2]; rfl)
    rw [start] at ok
    exact ⟨((complete_iff _ _).mp ok).2.1,x,y⟩
  · have ok := trace_complete hh path (g:=.threeTwo) (by
      rw [fit,fit,x,y,lw.1,lw.2]; rfl)
    rw [start] at ok
    have impossible := ((complete_iff _ _).mp ok).2.2
    contradiction

end DiskFullerene.Dual
