import SparseBoundary.FanZeroTwo
import SparseBoundary.GraphUnion
import SparseBoundary.GraphSupports

namespace SparseBoundary.ZeroCore
open Graph

/-- Six consecutive base sizes suffice since a disjoint octahedron
    contributes six entries of degree four. -/
theorem repeat_six (s : List Nat) (fits : s.length≤8)
    (base : ∀ i : Fin 6, Planaric (s ++ List.replicate (i.val+(8-s.length)) 4))
    (p : Nat) (size : 8≤p) : Planaric (s ++ List.replicate (p-s.length) 4) := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    by_cases short : p<14
    · have hp := base ⟨p-8,by omega⟩
      simpa only [show p-8+(8-s.length)=p-s.length by omega] using hp
    have prev := ih (p-6) (by omega) (by omega)
    have oct : Planaric (List.replicate 6 4) := Graph.Octahedron.realize 0 0 0 0 0 0 0
      (by decide) (by decide) (by decide) (by decide)
    have hp := planaric_append prev oct
    rw [List.append_assoc,List.replicate_append_replicate] at hp
    simpa only [show p-6-s.length+6=p-s.length by omega] using hp

/-- The sum constraint leaves exactly one five when there is one three. -/
theorem one_from_profile (h : List Nat) (j : Nat) (hj : j≤1) (core : Core h)
    (size : 8≤h.length) (vol : h.sum+2*j=4*h.length) (one : h.count 3=1)
    (seed : Planaric ([5,3] ++ List.replicate (h.length-2) 4)) : Planaric h := by
  let k := h.count 4
  obtain ⟨s,sub,pm⟩ := FourCore.erase_copies h 3 1 (by omega)
  have remain3 := pm.count_eq 3
  have remain4 := pm.count_eq 4
  change h.count 3=([3]++s).count 3 at remain3
  change h.count 4=([3]++s).count 4 at remain4
  simp at remain3 remain4
  obtain ⟨r,sub',qm⟩ := FourCore.erase_copies s 4 k (by dsimp [k]; omega)
  have rem4 := qm.count_eq 4
  have none : r.count 4=0 := by simp [k] at rem4; omega
  have threes := sub'.count_le 3
  have low (x) (hx : x∈r) : 5≤x := by
    have lo := core.2 x (sub.subset (sub'.subset hx))
    have ne3 : x≠3 := by rintro rfl; have := List.count_pos_iff.mpr hx; omega
    have ne4 : x≠4 := by rintro rfl; have := List.count_pos_iff.mpr hx; omega
    omega
  have floor (v : List Nat) (lo : ∀x∈v,5≤x) : 5*v.length≤v.sum := by
    induction v with
    | nil => simp
    | cons a w ih =>
      have ha := lo a (by simp)
      have hw := ih (fun x m => lo x (by simp [m]))
      simp; omega
  have lb := floor r low
  have l1 := pm.length_eq; have l2 := qm.length_eq
  have s1 := pm.sum_nat; have s2 := qm.sum_nat
  simp only [List.length_append,List.length_replicate,List.sum_append,List.sum_replicate_nat] at l1 l2 s1 s2
  have sm : r.length≤1 := by omega
  have perm : h.Perm ([3] ++ (List.replicate k 4 ++ r)) := pm.trans (qm.append_left _)
  match r with
  | [] => simp at l2 s2; omega
  | [a] =>
    have ha := low a (by simp)
    have both : a=5 ∧ k=h.length-2 := by simp at l2 s2; omega
    obtain ⟨rfl,hk⟩ := both
    apply (planaric_perm perm).mpr
    refine (planaric_perm ?_).mp seed
    rw [hk]
    apply List.perm_iff_count.mpr; intro i
    simp only [List.count_append,List.count_cons,List.count_nil]; omega
  | _::_::_ => simp at sm

end SparseBoundary.ZeroCore
