import MidpointShapes
import CensusEncoding

namespace Recognition.PolygonMidpoint
open CensusEncoding

theorem shape_spectra (n : Nat) : (shapes n).map Shape.signature = spectra n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [shapes,spectra,Shape.signature]
    | succ n =>
      rw [shapes,spectra,List.map_flatMap]
      apply List.flatMap_congr
      intro i _
      rw [←ih i.val i.isLt, List.flatMap_map,List.map_flatMap]
      apply List.flatMap_congr
      intro l _
      rw [←ih (n-i.val) (by omega),List.map_map,List.map_map]
      rfl

private theorem row_size (t : Shape) : t.row.vertices.length = t.size + 2 := by
  have aux (s : Shape) : s.row.inside.length = s.size := by
    induction s with
    | edge => rfl
    | triangle l r hl hr =>
      simp [Shape.row,Shape.size,hl,hr]
      omega
  simp [Row.vertices,aux,Nat.add_assoc]

/-- For twelve vertices each base-16 digit is the full multiplicity of its
degree. Each entry of the spectrum comes from one distinct labelled polygon
triangulation in the enumeration with fixed root edge. -/
private theorem matching_count (target : List Nat) (small : target.length < 16) :
    ((shapes 10).filter (fun t => decide (t.row.vertices.Perm target))).length =
      ((spectra 10).filter (fun s => s.code == code target)).length := by
  rw [←shape_spectra,List.filter_map,List.length_map]
  congr 1
  apply List.filter_congr
  intro t h
  have cardt : t.row.vertices.length < 16 := by rw [row_size,shapes_size h]; decide
  have equiv := code_iff cardt small
  change decide (t.row.vertices.Perm target) = (t.signature.code == code target)
  have val : code t.row.vertices = t.signature.code := inventory t
  rw [←val]
  by_cases e : code t.row.vertices = code target <;> simp [←equiv,e]

theorem degree_profile_census :
    (shapes 10).length = 16796 ∧
    ((shapes 10).filter (fun t => decide (t.row.vertices.Perm lowPolygon))).length = 36 ∧
    ((shapes 10).filter (fun t => decide (t.row.vertices.Perm highPolygon))).length = 12 ∧
    ((shapes 10).filter (fun t => decide (t.row.vertices.Perm midPolygon))).length = 0 := by
  obtain ⟨all,lo,hi,mid⟩ := dodecagon_census
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [←shape_spectra,List.length_map] using all
  · rw [matching_count _ (by decide),show code lowPolygon = lower by decide]
    exact lo
  · rw [matching_count _ (by decide),show code highPolygon = upper by decide]
    exact hi
  · rw [matching_count _ (by decide),show code midPolygon = middle by decide]
    exact mid

end Recognition.PolygonMidpoint
