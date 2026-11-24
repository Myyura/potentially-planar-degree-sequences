import SparseBoundary.FanThreeReduction
import SparseBoundary.GraphFourReduction

namespace SparseBoundary.ZeroCore

/-- At zero subdivision budget these are the three possible profiles with
exactly two threes on the two boundary layers. -/
def TwoThreeProfiles (p : Nat) : Prop :=
  Planaric ([6] ++ List.replicate (p-3) 4 ++ [3,3]) ∧
  Planaric ([5,5] ++ List.replicate (p-4) 4 ++ [3,3]) ∧
  Planaric (List.replicate (p-2) 4 ++ [3,3])

private theorem sum_floor (l : List Nat) (low : ∀i∈l,5≤i) : 5*l.length≤l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := low a (by simp)
    have hh := ih (fun i m => low i (by simp [m]))
    simp; omega

theorem two_from_profiles (h : List Nat) (j : Nat) (hj : j≤1) (core : Core h)
    (size : 8≤h.length) (vol : h.sum+2*j=4*h.length) (two : h.count 3=2)
    (seeds : TwoThreeProfiles h.length) : Planaric h := by
  let k := h.count 4
  obtain ⟨s,sub,pm⟩ := FourCore.erase_copies h 3 2 (by omega)
  have y4 := pm.count_eq 4
  have y3 := pm.count_eq 3
  change h.count 4=([3,3]++s).count 4 at y4
  change h.count 3=([3,3]++s).count 3 at y3
  simp at y4 y3
  obtain ⟨r,sub',pm'⟩ := FourCore.erase_copies s 4 k (by dsimp [k]; omega)
  have l4 := pm'.count_eq 4
  have none : r.count 4=0 := by simp [k] at l4; omega
  have l3 := sub'.count_le 3
  have rm (i) (hi : i∈r) : 5≤i := by
    have low := core.2 i (sub.subset (sub'.subset hi))
    have ne3 : i≠3 := by rintro rfl; have hh := List.count_pos_iff.mpr hi; omega
    have ne4 : i≠4 := by rintro rfl; have hh := List.count_pos_iff.mpr hi; omega
    omega
  have len := pm.length_eq
  have sum := pm.sum_nat
  have len' := pm'.length_eq
  have sum' := pm'.sum_nat
  simp only [List.length_append,List.length_replicate,List.sum_append,List.sum_replicate_nat] at len len' sum sum'
  have lb := sum_floor r rm
  have small : r.length≤2 := by omega
  have rep : h.Perm (r ++ List.replicate k 4 ++ [3,3]) := by
    apply pm.trans
    change ([3,3] ++ s).Perm _
    apply (pm'.append_left _).trans
    apply List.perm_iff_count.mpr; intro i
    simp only [List.count_append]; omega
  apply (planaric_perm rep).mpr
  obtain ⟨p6,p55,p4⟩ := seeds
  match r with
  | [] =>
    have eq : k=h.length-2 := by simp at len'; omega
    simpa [eq] using p4
  | [a] =>
    have eq : k=h.length-3 ∧ a=6 := by
      have ha := rm a (by simp)
      simp at len' sum'; omega
    obtain ⟨e,rfl⟩ := eq
    simpa [e] using p6
  | [a,b] =>
    have eq : k=h.length-4 ∧ a=5 ∧ b=5 := by
      have ha := rm a (by simp); have hb := rm b (by simp)
      simp at len' sum'; omega
    obtain ⟨e,rfl,rfl⟩ := eq
    simpa [e] using p55
  | a::b::c::z => simp at small

end SparseBoundary.ZeroCore
