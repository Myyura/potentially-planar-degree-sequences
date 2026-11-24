import RecognizingPotentiallyPlanarDegreeSequences.Budget
import RecognizingPotentiallyPlanarDegreeSequences.FixedLabels
import RecognizingPotentiallyPlanarDegreeSequences.FixedReverse

/-! Geometric correctness and the ordinary graphic promise of the two
fixed-budget reductions. All predicates use simple graphs. -/
namespace RecognizingPotentiallyPlanarDegreeSequences.FixedBudget

open SparseBoundary RecognizingPotentiallyPlanarDegreeSequences.Budget
open Recognition.Reduction (TableValid)

private theorem feasible_iff_suffix (h : List Nat) (s : Nat) :
    Feasible h 0 s ↔ Planaric (h ++ List.replicate s 2) := by
  simpa only [Feasible, List.replicate_zero, List.append_nil] using
    (planaric_perm (List.perm_append_comm (l₁:=List.replicate s 2) (l₂:=h)))

theorem at_budget_iff {d : List Nat} {r : Nat} (valid : TableValid d) (fit : r+3 ≤ d.length) :
    Feasible (core d r) 0 r ↔ Planaric d := by
  rw [feasible_iff_suffix]
  exact ⟨fun yes => (FixedReverse.reverse valid fit yes).2 rfl,
    FixedLabels.apply_planar valid (by omega)⟩

/-- Even if the number of available twos is an upper bound, the reduction
has the same language. No realizing graph can use fewer than r. -/
theorem within_budget_iff {d : List Nat} {r : Nat} (valid : TableValid d) (fit : r+3 ≤ d.length) :
    (∃ s ≤ r, Feasible (core d r) 0 s) ↔ Planaric d := by
  constructor
  · rintro ⟨s, sr, yes⟩
    obtain ⟨rs, recover⟩ := FixedReverse.reverse valid fit ((feasible_iff_suffix _ _).mp yes)
    exact recover (Nat.le_antisymm sr rs)
  · exact fun source => ⟨r, le_rfl, (at_budget_iff valid fit).mpr source⟩

theorem core_valid {d : List Nat} {r : Nat} (valid : TableValid d)
    (fit : r+3 ≤ d.length) (graphic : Graphic d) : TableValid (core d r) := by
  have hlen := core_length r valid
  have hn := valid.1
  have gr := core_graphic valid fit graphic
  refine ⟨by omega, core_euler valid fit, ?_⟩
  intro z hz
  refine ⟨?_, graphic_degree_lt gr z hz⟩
  let a := full (full d)
  have lo := (full_valid (full_valid valid)).2.2
  rcases List.mem_append.mp hz with old | fresh
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp old
    have h := List.mem_range.mp hi
    have deg := lo (full (full d))[i] (by apply List.getElem_mem)
    change 3 ≤ 2 * a[i]?.getD 0 + _
    rw [List.getElem?_eq_getElem h]
    simp only [Option.getD_some]
    omega
  · simp [List.eq_of_mem_replicate fresh]

/-- On a positive source instance the exact minimum is r. -/
theorem yes_minimum {d : List Nat} {r : Nat} (valid : TableValid d)
    (fit : r+3 ≤ d.length) (yes : Planaric d) : IsMinimum (core d r) 0 r := by
  refine ⟨(at_budget_iff valid fit).mpr yes, fun s hs => ?_⟩
  exact (FixedReverse.reverse valid fit ((feasible_iff_suffix _ _).mp hs)).1

end RecognizingPotentiallyPlanarDegreeSequences.FixedBudget
