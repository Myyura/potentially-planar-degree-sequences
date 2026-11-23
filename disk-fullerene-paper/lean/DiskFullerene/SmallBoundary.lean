import DiskFullerene.Perimeter
import DiskFullerene.Extremal

namespace DiskFullerene
open Dual

theorem chordless_small_budget {M} (G : IsDiskFullerene M h) (hh : 12≤h) (hc : ¬ HasChord G)
    (s : M.hexagons≤6) (buried : List (Face M)) (nd : buried.Nodup)
    (inside : buried⊆diskInterior G)
    (off : ∀ v∈buried, v∉contourWord G (by omega) hc) :
    h + (dualRow G (apex M)).countP (fun x => (dualRow G x).length==6) + buried.length ≤ 2+2*M.hexagons := by
  obtain ⟨v,a,b,vi,ai,bi,ea,eb,split⟩ := chordless_cut_vertex G hh hc s
  have cut : IsCoreCut G v := ⟨vi,a,b,ai,bi,ea,eb,split⟩
  have cuts := cut_budget G (by omega) hc cut
  have perim := perimeter_budget G (by omega) hc s buried nd inside off
  have size := interior_count G (by omega)
  rw [contour_length_eq G (by omega),← List.countP_eq_length_filter] at perim
  omega

/-- The full lower bound for all h≥13 (including all orders without
enumeration), before treating the last critical 12-gon. -/
theorem six_of_thirteen {M} (G : IsDiskFullerene M h) (hh : 13≤h) : 6≤M.hexagons := by
  by_cases s : M.hexagons≤5
  · by_cases cut : HasChord G
    · exact six_of_chord G (by omega) cut
    · have bound := chordless_small_budget G (by omega) cut (by omega) [] (by simp) (by simp) (by simp)
      simp only [List.length_nil] at bound; omega
  · omega

theorem minimum_of_thirteen (h : Nat) (hh : 13≤h) :
    (∀ M, IsDiskFullerene M h → 6≤M.hexagons) ∧
    ∃ M, IsDiskFullerene M h ∧ M.hexagons=6 ∧ M.pentagons=h+6 ∧ M.ord=2*h+22 :=
  ⟨fun _ G => six_of_thirteen G hh,PrimalSplice.upperBound h (by omega)⟩

/-- When h≥12, even five hexagons could only occur at h=12 and would
force every strict interior vertex onto the contour. -/
theorem last_five_case {M} (G : IsDiskFullerene M h) (hh : 12≤h) (s : M.hexagons≤5) :
    h=12 ∧ M.hexagons=5 ∧ ∀ u∈diskInterior G, u∈contourWord G (by omega)
      (show ¬HasChord G from fun cut => by have := six_of_chord G (by omega) cut; omega) := by
  have hc : ¬HasChord G := fun cut => by have := six_of_chord G (by omega) cut; omega
  have estimate := chordless_small_budget G hh hc (by omega) [] (by simp) (by simp) (by simp)
  simp only [List.length_nil] at estimate
  refine ⟨by omega,by omega,?_⟩
  intro u mem
  apply Classical.byContradiction; intro no
  have extra := chordless_small_budget G hh hc (by omega) [u] (by simp) (by simpa) (by simpa using no)
  simp only [List.length_cons,List.length_nil] at extra
  omega

end DiskFullerene
