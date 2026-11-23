import DiskFullerene.SixOpen
import DiskFullerene.SixTable

namespace DiskFullerene.EndSix
open Dual EndEuler Separation EndLabels

/-- A six-vertex set in the actual dual whose complement is connected and
which admits at most one long exterior run contains the full link of a
center. No triangulated-disk representation or planar drawing is input. -/
theorem center {M} (G : IsDiskFullerene M h) (hh : 3≤h) {A : Face M→Bool}
    (six : num A=6) (off : A (apex M)=false)
    (nonisolated : ∀ f, A f=true → ∃ z∈dualRow G f, A z=true)
    (conn : ∀ z, A z=false → Walk (Adj (dual G) (fun t=>sideEdge (dual G) (fun i=> !A i) t=true)) (apex M) z)
    (singleton : ∃ z, ∀ f, A f=true → BoundaryRun G A f → f=z) :
    ∃ c, A c=true ∧ ∀ z∈dualRow G c, A z=true :=
  SixLabels.center_from_table G hh (SixTable.complete _) six off nonisolated conn singleton

/-- The wheel conclusion for an actual terminal half follows from its size
alone. Both closed-center existence and exclusion of every extra rim chord
have already been proved in the original map. -/
theorem terminalWheel {M} (G : IsDiskFullerene M h) (hh : 3≤h) {x y}
    (S : TriangleSide G (apex M) x y) (B : Bool) (P : TerminalHalf G (vertexSide S B))
    (six : num (sectorCore S B)=6) :
    ∃ c : Face M, sectorCore S B c=true ∧ (dualRow G c).length=5 ∧
      (∀ f, sectorCore S B f=true ↔ f=c ∨ f∈dualRow G c) ∧
      ∀ i k : Fin M.faces[c.val].length, i<k →
        (atSide G c k ∈ dualRow G (atSide G c i) ↔ k.val=i.val+1 ∨ (i.val=0 ∧ k.val=4)) := by
  let A := sectorCore S B
  have off : A (apex M)=false := by simp [A,sectorCore,mem_diskInterior]
  have np := sector_complement_connected hh S B
  obtain ⟨c,hc,closed⟩ := center G hh six off (fun _ hu=>terminal_nonisolated hh S B P hu) np (terminal_single_run hh S B P)
  have sz : (items A).length=6 := ((List.countP_eq_length_filter ..).symm : (items A).length=num A).trans six
  obtain ⟨degree,occupies,rim⟩ := wheel G hh (items A) sz (by simp [off]) c (selected.mpr hc)
    (fun _ edge => selected.mpr (closed _ edge)) (SixLabels.outside_walks G np)
  exact ⟨c,hc,degree,fun f=>selected.symm.trans (occupies f),rim⟩

end DiskFullerene.EndSix
