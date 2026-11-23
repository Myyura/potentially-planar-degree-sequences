import DiskFullerene.EndRotations
import DiskFullerene.EndBudget
import DiskFullerene.ConstructionUpper

namespace DiskFullerene
open Dual EndEuler

/-- Two actual terminal halves have disjoint induced cores, each of
which has at least six vertices. This proves the lower bound directly
from the presence of a chord in the input graph. -/
theorem six_of_chord {M} (G : IsDiskFullerene M h) (hh : 3≤h) (cut : HasChord G) : 6≤M.hexagons := by
  obtain ⟨d,e,A⟩ := two_pieces G hh cut
  have big (q : EndPiece M G) := EndLabels.terminal_six G hh q.seam q.side q.terminal (q.nonempty hh)
  have := two_core_budget hh d e A
  have := big d
  have := big e
  omega

/-- All boundary lengths at least 20, including the unbounded tail.
A potential counterexample has at most five hexagons, so its boundary
would have length at most 19 in the absence of a chord. -/
theorem six_of_twenty {M} (G : IsDiskFullerene M h) (hh : 20≤h) : 6≤M.hexagons := by
  by_cases chord : HasChord G
  · exact six_of_chord G (by omega) chord
  · have := chordless_boundary_bound G (by omega) chord
    omega

theorem minimum_of_twenty (h : Nat) (hh : 20≤h) :
    (∀ M, IsDiskFullerene M h → 6≤M.hexagons) ∧
    ∃ M, IsDiskFullerene M h ∧ M.hexagons=6 ∧ M.pentagons=h+6 ∧ M.ord=2*h+22 :=
  ⟨fun _ G => six_of_twenty G hh,PrimalSplice.upperBound h (by omega)⟩

theorem equality_ends {M} (G : IsDiskFullerene M h) (hh : 3≤h) (cut : HasChord G) (six : M.hexagons=6) :
    ∃ d e : EndPiece M G, (∀ f, ¬(sectorCore d.seam d.side f=true ∧ sectorCore e.seam e.side f=true)) ∧
      num (sectorCore d.seam d.side)=6 ∧ num (sectorCore e.seam e.side)=6 := by
  obtain ⟨d,e,A⟩ := two_pieces G hh cut
  have big (q : EndPiece M G) := EndLabels.terminal_six G hh q.seam q.side q.terminal (q.nonempty hh)
  exact ⟨d,e,d.disjoint_core hh e A,exact_end_sizes hh d e A (big d) (big e) six⟩

end DiskFullerene
