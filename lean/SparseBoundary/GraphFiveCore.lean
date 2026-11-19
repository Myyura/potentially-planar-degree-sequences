import SparseBoundary.GraphSupports
import SparseBoundary.BranchDegree
import SparseBoundary.Boundary

namespace SparseBoundary

/-- On the exact lower boundary every normalized leaf-free graphic
    sequence with five core degrees at least four has a planar realization
    unless all five are four. -/
theorem lower_five_high (a b c d e t : Nat)
    (hab : b≤a) (hbc : c≤b) (hcd : d≤c) (hde : e≤d) (he : 4≤e)
    (boundary : a+b+c+d+e=18+2*t)
    (graphic : Graphic ([a,b,c,d,e] ++ List.replicate t 2))
    (hex : ([a,b,c,d,e] ++ List.replicate t 2) ≠ lowerException) :
    Planaric ([a,b,c,d,e] ++ List.replicate t 2) := by
  obtain ⟨G,real⟩ := graphic
  let v : Fin ([a,b,c,d,e] ++ List.replicate t 2).length := ⟨0, by simp⟩
  have hv : G.degree v = a := real v
  have cap : a ≤ 4+t := by
    have small := List.length_filter_le (G.adj v) (List.finRange _)
    have strict : ((List.finRange _).filter (G.adj v)).length ≠ (List.finRange ([a,b,c,d,e] ++ List.replicate t 2).length).length := by
      intro h
      have h' := List.length_filter_eq_length_iff.mp h v (List.mem_finRange v)
      simp at h'
    simp only [List.length_finRange,List.length_append,List.length_replicate,List.length_cons,
      List.length_nil] at small strict
    unfold Graph.degree at hv
    omega
  have large : 5 ≤ a := by
    apply Classical.byContradiction; intro h
    have ha : a=4 := by omega
    have hb : b=4 := by omega
    have hc : c=4 := by omega
    have hd : d=4 := by omega
    have he' : e=4 := by omega
    have ht : t=1 := by omega
    exact hex (by simp [ha,hb,hc,hd,he',ht,lowerException])
  have pl := Graph.Bipyramid.realize (a-4) (b-4) (c-4) (d-3) (e-3) t
    (by omega) (by omega) (by omega) (by omega) (by omega)
  simpa only [show 4+(a-4)=a by omega,show 4+(b-4)=b by omega,
    show 4+(c-4)=c by omega,show 3+(d-3)=d by omega,show 3+(e-3)=e by omega] using pl

/-- Every normalized leaf-free graphic sequence with at most five
    core vertices is classified on the exact lower boundary. -/
theorem lower_at_most_five {h : List Nat} {t : Nat}
    (core : Core h) (few : h.length ≤ 5) (graphic : Graphic (profile h t 0))
    (boundary : (profile h t 0).sum + 2 = 4*(profile h t 0).length) :
    Planaric (profile h t 0) ↔ profile h t 0 ≠ lowerException := by
  constructor
  · rintro hp e; rw [e] at hp
    exact Graph.exceptional_nonplanar hp
  intro hex
  have norm : profile h t 0 = h ++ List.replicate t 2 := by simp [profile]
  rw [norm] at graphic boundary hex ⊢
  have four : (h.filter (fun a => decide (4≤a))).length ≤ 5 :=
    Nat.le_trans (List.length_filter_le _ h) few
  by_cases low : (h.filter (fun a => decide (4≤a))).length ≤ 4
  · apply planaric_of_small_core graphic <;> simp [List.filter_append]
    · exact Nat.le_trans (List.length_filter_le _ _) few
    · exact low
  · have len : h.length=5 := by have := List.length_filter_le (fun a => decide (4≤a)) h; omega
    have pos : ∀ x ∈ h, 4≤x := by
      intro x hx
      have hh : (h.filter (fun a => decide (4≤a))).length=h.length := by omega
      exact of_decide_eq_true (List.length_filter_eq_length_iff.mp hh x hx)
    have shape {l : List Nat} (hl : l.length=5) : ∃ a b c d e, l=[a,b,c,d,e] := by
      match l with
      | [a,b,c,d,e] => exact ⟨a,b,c,d,e,rfl⟩
      | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | _::_::_::_::_::_::_ => simp at hl
    obtain ⟨a,b,c,d,e,rfl⟩ := shape len
    have sort := core.1
    simp at sort
    simp [List.sum_replicate_nat] at boundary
    exact lower_five_high a b c d e t (by grind) (by grind) (by grind) (by grind)
      (pos e (by simp)) (by omega) graphic hex

end SparseBoundary
