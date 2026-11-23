import DiskFullerene.Terminal
import DiskFullerene.EndCoreEuler

namespace DiskFullerene.Dual
open Separation Dissection EndEuler

private theorem acrossAdj {M} (G : IsDiskFullerene M h) {e : Edge M} {x y}
    (H : Across (dual G) e x y) : y ∈ dualRow G x := by
  have neighbors : (dual G e).2 ∈ dualRow G (dual G e).1 :=
    (mem_row_iff _ _ _).mpr ⟨endpoints e,left_incident G (endpoints_mem e),
      left_incident G (dart_reverse G (endpoints_mem e))⟩
  rcases H with h|h <;> rw [h] at neighbors
  · exact neighbors
  · exact (dual_adj_symmetric G y x).mp neighbors

/-- The edge crossing any chord of the outer link cannot have both its
endpoints in a terminal component, even for chords sharing an end. -/
theorem TerminalHalf.chord_not_inside {M} {G : IsDiskFullerene M h} (hh : 3≤h)
    {p} (P : TerminalHalf G p) {x y} (hx : IsBoundary G x) (hy : IsBoundary G y)
    {e : Edge M} (E : Across (dual G) e x y) (nc : ¬OnCycle (dualRow G (apex M)) x y) :
    ¬(p (primal G e).1=true ∧ p (primal G e).2=true) := by
  classical
  let N := atSide G (apex M)
  obtain ⟨i,j,C,dir⟩ := indexed_chord G hh hx hy (acrossAdj G E)
    (fun m => nc (Or.inl m)) (fun m => nc (Or.inr m))
  have ordered : Across (dual G) e (N i) (N j) := by
    rcases dir with ⟨a,b⟩|⟨a,b⟩
    · simpa [N,a,b] using E
    · simpa [N,a,b] using (show Across (dual G) e y x from Or.symm E)
  have adj (k) : N k ∈ dualRow G (apex M) := by
    dsimp [N]; rw [atSide_eq]; exact List.getElem_mem _
  obtain ⟨S⟩ := hasSides G hh (adj i) (acrossAdj G ordered) ((dual_adj_symmetric G _ _).mp (adj j))
  have em := uniqueAcross G hh ordered S.middle
  let q := fun v => decide (S.part.left v)
  have Q : ChordHalf G q := ⟨⟨i.val,j.val⟩,C,i,j,rfl,rfl,S,true,by simp [q]⟩
  obtain ⟨b,qs⟩ := P.2 q Q
  rintro ⟨l,r⟩
  have eq := (qs _ l).trans (qs _ r).symm
  have no := (S.part.crosses e).mp (Or.inr (Or.inl em))
  exact no (by simpa [q] using eq)

private theorem rawSide {M} {G : IsDiskFullerene M h} {w x y} (S : TriangleSide G w x y)
    (b : Bool) (v : Fin M.ord) : (vertexSide S b v=true) ↔ (S.part.left v ↔ b=true) := by
  classical
  cases b <;> simp [vertexSide]

theorem TerminalHalf.seam_or_cycle {M} {G : IsDiskFullerene M h} (hh : 3≤h) {x y}
    (S : TriangleSide G (apex M) x y) (b : Bool) (P : TerminalHalf G (vertexSide S b))
    {r t} (hr : IsBoundary G r) (ht : IsBoundary G t) {e : Edge M} (E : Across (dual G) e r t)
    (inside : vertexSide S b (primal G e).1=true ∨ vertexSide S b (primal G e).2=true) :
    OnCycle (dualRow G (apex M)) r t ∨ e=S.xy := by
  classical
  by_cases cr : OnCycle (dualRow G (apex M)) r t
  · exact Or.inl cr
  right
  have drop := P.chord_not_inside hh hr ht E cr
  have cut : ThreeEdges S.wx S.xy S.yw e := by
    apply (S.part.crosses e).mpr
    intro eq
    have same : vertexSide S b (primal G e).1=true ↔ vertexSide S b (primal G e).2=true := by
      rw [rawSide,rawSide,eq]
    rcases inside with l|r
    · exact drop ⟨l,same.mp l⟩
    · exact drop ⟨same.mpr r,r⟩
  have away (z) (H : IsBoundary G z) : z≠apex M := fun eq => row_no_loop G hh _ (eq ▸ H)
  have a := away _ hr
  have d := away _ ht
  rcases cut with eq|eq|eq
  · exfalso; rw [eq] at E
    rcases E with A|A <;> rcases S.first with B|B <;> rw [A] at B <;> simp_all
  · exact eq
  · exfalso; rw [eq] at E
    rcases E with A|A <;> rcases S.last with B|B <;> rw [A] at B <;> simp_all

end DiskFullerene.Dual
