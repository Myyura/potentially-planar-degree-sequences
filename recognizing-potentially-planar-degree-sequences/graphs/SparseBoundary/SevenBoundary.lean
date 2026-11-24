import SparseBoundary.Boundary
import SparseBoundary.FanGraphicNecessity
import SparseBoundary.SevenFour
import SparseBoundary.SevenThree
import SparseBoundary.SevenCores
import SparseBoundary.SevenLowerRepairs

set_option maxHeartbeats 3000000

namespace SparseBoundary

private theorem seven_shape {h : List Nat} (s : h.length = 7) :
    ∃ a b c d e f g, h=[a,b,c,d,e,f,g] := by
  match h with
  | [a,b,c,d,e,f,g] => exact ⟨a,b,c,d,e,f,g,rfl⟩
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | _::_::_::_::_::_::_::_::_ => simp at s

theorem upper_seven_numeric (a b c d e f g t : Nat)
    (ab : b≤a) (bc : c≤b) (cd : d≤c) (de : e≤d) (ef : f≤e) (fg : g≤f)
    (lo : 3≤g) (sum : a+b+c+d+e+f+g=28+2*t) (cap : a≤6+t) (third : 4≤c)
    (ex0 : ¬ (a=4 ∧ t=0))
    (ex1 : ¬ (a=6 ∧ b=5 ∧ c=5 ∧ d=3 ∧ t=0))
    (ex2 : ¬ (a=6 ∧ b=6 ∧ c=6 ∧ d=3 ∧ t=1)) :
    Planaric ([a,b,c,d,e,f,g] ++ List.replicate t 2) := by
  by_cases mg : 4≤g
  · apply SevenFour.min_four a b c d e f g t ab bc cd de ef fg mg sum cap
    omega
  have g3 : g=3 := by omega
  subst g
  by_cases mf : 4≤f
  · exact SevenOne.one_three a b c d e f t ab bc cd de ef mf (by omega) cap
  have f3 : f=3 := by omega
  subst f
  by_cases me : 4≤e
  · exact SevenTwo.two_threes a b c d e t ab bc cd de me (by omega) cap
  have e3 : e=3 := by omega
  subst e
  by_cases md : 4≤d
  · exact SevenThree.three_threes a b c d t ab bc cd md (by omega) cap
  have d3 : d=3 := by omega
  subst d
  apply SevenCore.four_threes a b c t ab bc third (by omega) (by omega) <;>
    simp only [ne_eq,Prod.mk.injEq] <;> omega

private theorem seven_bounds {a b c d e f g t k : Nat} (core : Core [a,b,c,d,e,f,g])
    (graphic : Graphic ([a,b,c,d,e,f,g] ++ List.replicate t 2))
    (vol : a+b+c+d+e+f+g+2*k=28+2*t) :
    a≤6+t ∧ 16≤c+d+e+f+g+2*k := by
  have eg := ErdosGallai.eg_of_graphic graphic
  have bounds := (ErdosGallai.boundary_criterion (a:=a) (b:=b) (p:=7) (t:=t) (k:=k) [c,d,e,f,g]
    rfl (by decide) core.2 (by simp; omega)).mp eg
  simp at bounds
  omega

/-- Complete upper-layer classification with seven core vertices and no leaves. -/
theorem upper_seven_classified {h : List Nat} {t : Nat} (core : Core h) (size : h.length=7)
    (graphic : Graphic (profile h t 0))
    (boundary : (profile h t 0).sum=4*(profile h t 0).length) :
    Planaric (profile h t 0) ↔ ¬ UpperForbidden h t 0 := by
  constructor
  · intro hp bad
    exact upper_obstructions_nonplanar (List.Perm.refl _) (by simpa using boundary) bad hp
  intro no
  obtain ⟨a,b,c,d,e,f,g,rfl⟩ := seven_shape size
  have hg : Graphic ([a,b,c,d,e,f,g] ++ List.replicate t 2) := by simpa [profile] using graphic
  have vol : a+b+c+d+e+f+g=28+2*t := by simp [profile,List.sum_replicate_nat] at boundary; omega
  obtain ⟨mx,tl⟩ := seven_bounds (k:=0) core hg (by omega)
  obtain ⟨order,minimum⟩ := core
  simp at order
  have lo := minimum g (by simp)
  have ab : b≤a := by grind
  have bc : c≤b := by grind
  have cd : d≤c := by grind
  have de : e≤d := by grind
  have ef : f≤e := by grind
  have fg : g≤f := by grind
  simp only [profile,List.replicate_zero,List.append_nil]
  apply upper_seven_numeric a b c d e f g t ab bc cd de ef fg lo vol mx (by omega)
  · rintro ⟨rfl,rfl⟩
    have hh : b=4 ∧ c=4 ∧ d=4 ∧ e=4 ∧ f=4 ∧ g=4 := by omega
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := hh
    exact no (by simp [UpperForbidden,profile])
  · rintro ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hh : e=3 ∧ f=3 ∧ g=3 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := hh
    exact no (by simp [UpperForbidden,profile])
  · rintro ⟨rfl,rfl,rfl,rfl,rfl⟩
    have hh : e=3 ∧ f=3 ∧ g=3 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := hh
    exact no (by simp [UpperForbidden,profile])

/-- Numerical form for seven core vertices on the lower boundary. -/
theorem lower_seven_numeric (a b c d e f g t : Nat)
    (ab : b≤a) (bc : c≤b) (cd : d≤c) (de : e≤d) (ef : f≤e) (fg : g≤f)
    (lo : 3≤g) (vol : a+b+c+d+e+f+g=26+2*t) (mx : a≤6+t) :
    Planaric ([a,b,c,d,e,f,g] ++ List.replicate t 2) := by
  by_cases c3 : c=3
  · have hh : a=6+t ∧ b=5+t ∧ d=3 ∧ e=3 ∧ f=3 ∧ g=3 := by omega
    obtain ⟨A,B,D,E,F,G⟩ := hh; rw [A,B,c3,D,E,F,G]
    exact SevenLower.five_threes t
  by_cases universal : a=6+t
  · rw [universal]
    exact SevenUniversal.lower b c d e f g t (by omega) (by omega) (by omega) (by omega)
      (by omega) lo (by omega)
  by_cases zero : t=0
  · subst t
    have cases :
        (a=5 ∧ b=5 ∧ c=4 ∧ d=3 ∧ e=3 ∧ f=3 ∧ g=3) ∨
        (a=5 ∧ b=4 ∧ c=4 ∧ d=4 ∧ e=3 ∧ f=3 ∧ g=3) ∨
        (a=4 ∧ b=4 ∧ c=4 ∧ d=4 ∧ e=4 ∧ f=3 ∧ g=3) := by
      by_cases p : a=4
      · right; right; omega
      by_cases q : b=4
      · right; left; omega
      · left; omega
    rcases cases with ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩|⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    · exact SevenLower.repair 0
    · exact SevenLower.repair 1
    · exact SevenLower.repair 2
  by_cases ex0 : a=4 ∧ t=1
  · obtain ⟨rfl,rfl⟩ := ex0
    have eq : b=4 ∧ c=4 ∧ d=4 ∧ e=4 ∧ f=4 ∧ g=4 := by omega
    obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := eq
    exact SevenLower.repair 3
  by_cases ex1 : a=6 ∧ b=5 ∧ c=5 ∧ d=3 ∧ t=1
  · obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := ex1
    have eq : e=3 ∧ f=3 ∧ g=3 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := eq
    exact SevenLower.repair 4
  by_cases ex2 : a=6 ∧ b=6 ∧ c=6 ∧ d=3 ∧ t=2
  · obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := ex2
    have eq : e=3 ∧ f=3 ∧ g=3 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := eq
    exact SevenLower.repair 5
  have upper := upper_seven_numeric a b c d e f g (t-1) ab bc cd de ef fg lo
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have up' := (planaric_perm List.perm_append_comm).mp upper
  have lifted := planaric_add_two up' (by
    refine ⟨a,List.mem_append_right _ (by simp),?_⟩; omega)
  apply (planaric_perm List.perm_append_comm).mp
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero zero
  simpa [List.replicate_succ,List.cons_append] using lifted

/-- Every graphic lower-layer sequence with seven core vertices and no leaves is planaric. -/
theorem lower_seven_classified {h : List Nat} {t : Nat} (core : Core h) (size : h.length=7)
    (graphic : Graphic (profile h t 0))
    (boundary : (profile h t 0).sum+2=4*(profile h t 0).length) :
    Planaric (profile h t 0) := by
  obtain ⟨a,b,c,d,e,f,g,rfl⟩ := seven_shape size
  have hg : Graphic ([a,b,c,d,e,f,g] ++ List.replicate t 2) := by simpa [profile] using graphic
  have vol : a+b+c+d+e+f+g=26+2*t := by simp [profile,List.sum_replicate_nat] at boundary; omega
  obtain ⟨mx,_⟩ := seven_bounds (k:=1) core hg (by omega)
  obtain ⟨order,minimum⟩ := core
  simp at order
  have lo := minimum g (by simp)
  have ab : b≤a := by grind
  have bc : c≤b := by grind
  have cd : d≤c := by grind
  have de : e≤d := by grind
  have ef : f≤e := by grind
  have fg : g≤f := by grind
  simp only [profile,List.replicate_zero,List.append_nil]
  exact lower_seven_numeric a b c d e f g t ab bc cd de ef fg lo vol mx

end SparseBoundary
