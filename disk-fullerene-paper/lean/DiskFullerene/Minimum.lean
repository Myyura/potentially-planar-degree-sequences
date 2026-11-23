import DiskFullerene.SmallBoundary
import DiskFullerene.ArmCenters

namespace DiskFullerene
open Dual

/-- Universal six-hexagon lower bound, for the whole range in the paper. -/
theorem six_lower {M} (G : IsDiskFullerene M h) (hh : 12≤h) : 6≤M.hexagons := by
  by_cases small : M.hexagons≤5
  · have hc : ¬HasChord G := fun cut => by have := six_of_chord G (by omega) cut; omega
    obtain ⟨_,_,all⟩ := last_five_case G hh small
    obtain ⟨u,a,b,ui,ai,bi,ua,ub,dis⟩ := chordless_cut_vertex G hh hc (by omega)
    have cut : IsCoreCut G u := ⟨ui,a,b,ai,bi,ua,ub,dis⟩
    have sz := interior_count G (by omega)
    obtain ⟨c,_,_,ci,_,buried,_⟩ := eleven_two_buried G (by omega) hc cut (by omega)
    exact False.elim (buried (all c ci))
  · omega

/-- The minimum equals six and is attained for every h≥12. The
additional isomorphism assertion of MainStatement is a separate goal. -/
theorem minimum (h : Nat) (hh : 12≤h) :
    (∀ M, IsDiskFullerene M h → 6≤M.hexagons) ∧
    ∃ M, IsDiskFullerene M h ∧ M.hexagons=6 ∧ M.pentagons=h+6 ∧ M.ord=2*h+22 :=
  ⟨fun _ G => six_lower G hh,PrimalSplice.upperBound h hh⟩

end DiskFullerene
