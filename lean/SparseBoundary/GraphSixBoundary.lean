import SparseBoundary.GraphSixClassification
import SparseBoundary.GraphSixLower
import SparseBoundary.Boundary

namespace SparseBoundary

private theorem six_shape {l : List Nat} (hl : l.length=6) : ∃ a b c d e f, l=[a,b,c,d,e,f] := by
  match l with
  | [a,b,c,d,e,f] => exact ⟨a,b,c,d,e,f,rfl⟩
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | _::_::_::_::_::_::_::_ => simp at hl

private theorem first_bound {a : Nat} {tail : List Nat} (graphic : Graphic (a::tail)) : a≤tail.length := by
  obtain ⟨G,real⟩ := graphic
  have hd : G.degree 0=a := real 0
  have small := List.length_filter_le (G.adj 0) (List.finRange _)
  have strict : ((List.finRange _).filter (G.adj 0)).length ≠ (List.finRange (a::tail).length).length := by
    intro h
    have h' := List.length_filter_eq_length_iff.mp h 0 (List.mem_finRange _)
    simp at h'
  simp only [List.length_finRange,List.length_cons] at small strict
  unfold Graph.degree at hd
  simp only [List.length_cons] at hd
  omega

/-- Complete lower-layer classification with six core vertices and no leaves. -/
theorem lower_six_classified {h : List Nat} {t : Nat} (core : Core h) (size : h.length=6)
    (graphic : Graphic (profile h t 0))
    (boundary : (profile h t 0).sum+2=4*(profile h t 0).length) : Planaric (profile h t 0) := by
  obtain ⟨a,b,c,d,e,f,rfl⟩ := six_shape size
  simp [profile,List.sum_replicate_nat] at graphic boundary ⊢
  obtain ⟨ord,minimum⟩ := core
  simp at ord
  have minF : 3≤f := minimum f (by simp)
  have cap : a≤t+5 := by simpa using first_bound graphic
  by_cases mf : 4≤f
  · apply six_min_four a b c d e f (t-1) t (by grind) (by grind) (by grind) (by grind)
      (by grind) mf (by omega) (by omega) cap
    intro ha hb
    have hc : c=4 := by omega
    have hd : d=4 := by omega
    have he : e=4 := by omega
    have hf : f=4 := by omega
    omega
  have ef : f=3 := by omega
  subst f
  by_cases me : 4≤e
  · apply lower_six_one_three a b c d e t (by grind) (by grind) (by grind) (by grind) me (by omega) cap
  have ee : e=3 := by omega
  subst e
  by_cases mc : 4≤c
  · apply lower_six_two_or_three_threes a b c d t (by grind) (by grind) (by grind) mc (by grind) (by omega) cap
  have ec : c=3 := by omega
  have ed : d=3 := by omega
  subst c d
  exact lower_six_four_threes a b t (by grind) (by omega) cap

/-- Complete upper-layer classification with six core vertices and no leaves. -/
theorem upper_six_classified {h : List Nat} {t : Nat} (core : Core h) (size : h.length=6)
    (graphic : Graphic (profile h t 0))
    (boundary : (profile h t 0).sum=4*(profile h t 0).length) :
    Planaric (profile h t 0) ↔ ¬ UpperForbidden h t 0 := by
  constructor
  · intro hp bad
    exact upper_obstructions_nonplanar (List.Perm.refl _) (by simpa using boundary) bad hp
  intro ok
  obtain ⟨a,b,c,d,e,f,rfl⟩ := six_shape size
  simp [profile,List.sum_replicate_nat] at graphic boundary ⊢
  obtain ⟨ord,minimum⟩ := core
  simp at ord
  have minF : 3≤f := minimum f (by simp)
  have cap : a≤t+5 := by simpa using first_bound graphic
  by_cases mf : 4≤f
  · apply six_min_four a b c d e f t t (by grind) (by grind) (by grind) (by grind)
      (by grind) mf (by omega) (by omega) cap
    intro ha hb
    have hc : c=4 := by omega
    have hd : d=4 := by omega
    have he : e=4 := by omega
    have hf : f=4 := by omega
    have ht : t=1 := by omega
    subst a b c d e f t
    exact False.elim (ok (by simp [UpperForbidden,profile]))
  have ef : f=3 := by omega
  subst f
  by_cases me : 4≤e
  · apply upper_six_one_three a b c d e t (by grind) (by grind) (by grind) (by grind) me (by omega) cap
    · rintro ⟨ha,hb⟩
      have hc : c=4 := by omega
      have hd : d=4 := by omega
      have he : e=4 := by omega
      have ht : t=0 := by omega
      subst a b c d e t
      exact ok (by simp [UpperForbidden,profile])
    · rintro ⟨ha,he⟩
      have hb : b=5 := by omega
      have hc : c=5 := by omega
      have hd : d=5 := by omega
      have ht : t=2 := by omega
      subst a b c d e t
      exact ok (by simp [UpperForbidden,profile])
  have ee : e=3 := by omega
  subst e
  by_cases md : 4≤d
  · exact upper_six_two_threes a b c d t (by grind) (by grind) (by grind) md (by omega) cap
  have ed : d=3 := by omega
  subst d
  have hc : 4≤c := by omega
  exact False.elim (ok (Or.inr (Or.inl ⟨a,b,c,hc,rfl⟩)))

end SparseBoundary
