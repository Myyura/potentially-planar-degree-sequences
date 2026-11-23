import DiskFullerene.CapEmbedding
import DiskFullerene.SixOpen

namespace DiskFullerene.EndFans
open Dual EndEuler EndLabels

/-- Assemble all cap labels and actual seam loads from its center and its
six-element interior. The complement walks come from the original map. -/
theorem cap_from_center {M} {G : IsDiskFullerene M h} (hh : 7≤h) (d : EndPiece M G)
    (six : num (sectorCore d.seam d.side)=6)
    (center : ∃ c, sectorCore d.seam d.side c=true ∧ ∀ z∈dualRow G c, sectorCore d.seam d.side z=true) : Nonempty (Cap d) := by
  let A:=sectorCore d.seam d.side
  have pole : A (apex M)=false := by simp [A,sectorCore,mem_diskInterior]
  have conn := SixLabels.outside_walks G (sector_complement_connected (by omega) d.seam d.side)
  obtain ⟨c,inc,cover⟩ := center
  obtain ⟨W⟩ := wheel_of_center G (by omega) A six pole c inc cover conn
  exact ⟨markedCap hh ⟨W,annulus (by omega) pole W⟩⟩

theorem Cap.seam_loads {M} {G : IsDiskFullerene M h} {d : EndPiece M G} (C : Cap d) (hh : 3≤h) :
    loadAt d.seam d.side C.weak=2 ∧ loadAt d.seam d.side C.strong=3 := C.loads hh

end DiskFullerene.EndFans
