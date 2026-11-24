import PolygonGraph
import Mathlib.Data.List.Nodup

namespace Recognition.PolygonMidpoint

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem dodecagon_census :
    (spectra 10).length = 16796 ∧
    ((spectra 10).filter (fun s => s.code == lower)).length = 36 ∧
    ((spectra 10).filter (fun s => s.code == upper)).length = 12 ∧
    ((spectra 10).filter (fun s => s.code == middle)).length = 0 := by
  decide +kernel

/-- The recursive split at the root edge enumerates actual triangulation
shapes. Its index is recoverable as the size of the left subpolygon. -/
def shapes : (n : Nat) → List Shape
  | 0 => [.edge]
  | n+1 => (List.finRange (n+1)).flatMap fun i =>
      (shapes i.val).flatMap fun l => (shapes (n-i.val)).map (Shape.triangle l)
termination_by n => n
decreasing_by all_goals have := i.isLt; omega

theorem shapes_size {n : Nat} {t : Shape} (h : t ∈ shapes n) : t.size = n := by
  induction n using Nat.strong_induction_on generalizing t with
  | h n ih =>
    cases n with
    | zero => simp [shapes] at h; subst t; rfl
    | succ n =>
      simp only [shapes,List.mem_flatMap,List.mem_map] at h
      obtain ⟨i,_,l,hl,r,hr,rfl⟩ := h
      have a := ih i.val i.isLt hl
      have b := ih (n-i.val) (by omega) hr
      have := i.isLt
      simp only [Shape.size,a,b]
      omega

theorem shape_occurs (t : Shape) : t ∈ shapes t.size := by
  induction t with
  | edge => simp [Shape.size,shapes]
  | triangle l r hl hr =>
    simp only [Shape.size,shapes,List.mem_flatMap,List.mem_map]
    let i : Fin (l.size+r.size+1) := ⟨l.size,by omega⟩
    exact ⟨i,List.mem_finRange i,l,hl,r,by simpa [i] using hr,rfl⟩

theorem shapes_nodup (n : Nat) : (shapes n).Nodup := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [shapes]
    | succ n =>
      rw [shapes,List.nodup_flatMap]
      constructor
      · intro i _
        rw [List.nodup_flatMap]
        constructor
        · intro l _
          exact (ih (n-i.val) (by omega)).map (fun _ _ eq => (Shape.triangle.inj eq).2)
        · apply (ih i.val i.isLt).imp
          intro x y ne t hx hy
          obtain ⟨r,_,rfl⟩ := List.mem_map.mp hx
          obtain ⟨s,_,eq⟩ := List.mem_map.mp hy
          exact ne (Shape.triangle.inj eq).1.symm
      · apply (List.nodup_finRange (n+1)).imp
        intro i j ne t hi hj
        obtain ⟨l,hl,ht⟩ := List.mem_flatMap.mp hi
        obtain ⟨r,_,rfl⟩ := List.mem_map.mp ht
        obtain ⟨l',hl',ht'⟩ := List.mem_flatMap.mp hj
        obtain ⟨r',_,eq⟩ := List.mem_map.mp ht'
        cases eq
        exact ne (Fin.ext ((shapes_size hl).symm.trans (shapes_size hl')))

end Recognition.PolygonMidpoint
