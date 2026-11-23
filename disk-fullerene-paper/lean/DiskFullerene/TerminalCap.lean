import DiskFullerene.CertifiedCap
import DiskFullerene.SixCenter

namespace DiskFullerene.EndFans
open Dual EndEuler EndLabels

/-- A six-vertex terminal half of any input map has the complete marked
cap model, with ten distinct nonseam labels and the original seam loads. -/
theorem of_six {M} {G : IsDiskFullerene M h} (hh : 7≤h) (d : EndPiece M G)
    (six : num (sectorCore d.seam d.side)=6) : Nonempty (Cap d) :=
  cap_from_center hh d six (EndSix.center G (by omega) six (by simp [sectorCore,mem_diskInterior])
    (fun _ h=>terminal_nonisolated (by omega) d.seam d.side d.terminal h)
    (sector_complement_connected (by omega) d.seam d.side) (terminal_single_run (by omega) d.seam d.side d.terminal))

end DiskFullerene.EndFans
