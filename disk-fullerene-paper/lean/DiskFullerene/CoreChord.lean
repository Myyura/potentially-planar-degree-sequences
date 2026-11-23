import DiskFullerene.CoreBoundary
import DiskFullerene.SixCenter

namespace DiskFullerene.Dual

/-- Chord existence in the original spherical rotation system, for every
boundary length in the conjecture. -/
theorem chord_small {M} (G : IsDiskFullerene M h) (hh : 12≤h) (s : M.hexagons≤6) : HasChord G :=
  chord_small_of_table SixTable.complete G hh s

end DiskFullerene.Dual
