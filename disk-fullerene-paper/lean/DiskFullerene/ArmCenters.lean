import DiskFullerene.ArmWheels
import DiskFullerene.SixCenter

namespace DiskFullerene.Dual

theorem closed_arm_wheel {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    (D : Branch G) (small : D.members.length=5) (room : 6<(diskInterior G).length) :
    Nonempty (ArmWheel G D) :=
  closed_arm_wheel_of_table SixTable.complete G hh hc D small room

theorem eleven_two_buried {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    {u : Face M} (cut : IsCoreCut G u) (eleven : (diskInterior G).length≤11) :
    ∃ c d : Face M, c≠d ∧ c∈diskInterior G ∧ d∈diskInterior G ∧
      c∉contourWord G hh hc ∧ d∉contourWord G hh hc :=
  eleven_two_buried_of_table SixTable.complete G hh hc cut eleven

end DiskFullerene.Dual
