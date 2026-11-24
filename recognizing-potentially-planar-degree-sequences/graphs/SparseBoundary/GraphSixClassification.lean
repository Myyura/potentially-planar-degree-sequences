import SparseBoundary.GraphHub
import SparseBoundary.FanRealization

namespace SparseBoundary

/-- Realization on the ordered four-vertex path suspended from the two
    poles. The three nonnegative path multiplicities need only bound the
    unused capacity; trimming to the required total is automatic. -/
theorem six_path_completion (a b c d e f x y z m t : Nat)
    (ba : b≤a) (hb : 5≤b) (hc : 3≤c) (hd : 4≤d) (he : 4≤e) (hf : 3≤f)
    (sum : a+b+c+d+e+f=24+2*m) (budget : m≤t) (balance : a≤m+5)
    (cap1 : x+3≤c) (cap2 : x+y+4≤d) (cap3 : y+z+4≤e) (cap4 : z+3≤f)
    (fill : c+d+e+f ≤ a+b+4+2*(x+y+z)) :
    Planaric ([a,b,c,d,e,f] ++ List.replicate t 2) := by
  let cs := [c-3,d-4,e-4,f-3]
  let ds := [c-3-x,d-4-x-y,e-4-y-z,f-3-z]
  have pack : Fan.Packing 0 cs (x+(y+(z+0))) ds :=
    Fan.Packing.cons (o:=x) (by omega) (Fan.Packing.cons (o:=y) (by omega)
      (Fan.Packing.cons (o:=z) (by omega) (Fan.Packing.cons (o:=0) (by omega) Fan.Packing.nil)))
  have filled : Fan.Filled cs (a-5) (b-5) := by
    apply Fan.fill_of_packing pack <;> simp [cs,ds] <;> omega
  obtain ⟨j,s,pl⟩ := Fan.filled_planaric filled
  have pp : Fan.pathProfile cs=[3+(c-3),4+(d-4),4+(e-4),3+(f-3)] := rfl
  rw [pp] at pl
  change Planaric (List.replicate j 2 ++ [5+(a-5),5+(b-5),3+(c-3),4+(d-4),4+(e-4),3+(f-3)]) at pl
  rw [show 5+(a-5)=a by omega,show 5+(b-5)=b by omega,show 3+(c-3)=c by omega,
      show 4+(d-4)=d by omega,show 4+(e-4)=e by omega,show 3+(f-3)=f by omega] at pl
  simp [cs] at s
  have jm : j=m := by omega
  subst j
  have p := planaric_add_twos pl ⟨a,List.mem_append_right _ (by simp),by omega⟩ (t-m)
  have eqn : List.replicate (t-m) 2 ++ List.replicate m 2=List.replicate t 2 := by
    apply List.eq_replicate_iff.mpr; exact ⟨by simp; omega,by simp⟩
  rw [← List.append_assoc,eqn] at p
  exact (planaric_perm List.perm_append_comm).mp p

/-- Six core vertices all of degree at least four. The simple degree bound
    and the exceptional budget at (6,4,4,4,4,4) are the only further costs. -/
theorem six_min_four (a b c d e f m t : Nat)
    (hab : b≤a) (hbc : c≤b) (hcd : d≤c) (hde : e≤d) (hef : f≤e) (hf : 4≤f)
    (sum : a+b+c+d+e+f=24+2*m) (budget : m≤t) (upper : a≤t+5)
    (exc : a=6 → b=4 → 2≤t) :
    Planaric ([a,b,c,d,e,f] ++ List.replicate t 2) := by
  by_cases oct : a+f ≤ m+8
  · exact six_octahedral_range a b c d e f m t hab hbc hcd hde hef hf sum oct budget
  by_cases b4 : b=4
  · have ec : c=4 := by omega
    have ed : d=4 := by omega
    have ee : e=4 := by omega
    have ef : f=4 := by omega
    subst b c d e f
    by_cases a6 : a=6
    · subst a; exact six_exception_budget t (exc rfl rfl)
    · exact six_four_rim a t (by omega) (by omega) upper
  by_cases hub : m+5≤a
  · exact six_high_hub a b c d e f m t hab (by omega) (by omega) (by omega) (by omega)
      (by omega) sum hub upper
  by_cases total : m+10≤a+b
  · exact six_path_completion a b c d e f 0 0 0 m t hab (by omega) (by omega) (by omega)
      (by omega) (by omega) sum budget (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact six_path_completion a b c d e f 1 0 0 m t hab (by omega) (by omega) (by omega)
      (by omega) (by omega) sum budget (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Six core vertices with exactly two threes on the upper boundary. -/
theorem upper_six_two_threes (a b c d t : Nat) (hab : b≤a) (hbc : c≤b)
    (hcd : d≤c) (hd : 4≤d) (sum : a+b+c+d+6=24+2*t) (upper : a≤t+5) :
    Planaric ([a,b,c,d,3,3] ++ List.replicate t 2) := by
  have h := six_path_completion a b 3 c d 3 0 (d-4) 0 t t hab (by omega)
    (by decide) (by omega) hd (by decide) (by omega) (by omega) upper
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have p : [a,b,3,c,d,3].Perm [a,b,c,d,3,3] := by
    apply List.perm_iff_count.mpr
    intro i; simp only [List.count_cons,List.count_nil]; omega
  exact (planaric_perm (p.append_right _)).mp h

/-- Six core vertices with exactly one three on the upper boundary. -/
theorem upper_six_one_three (a b c d e t : Nat) (hab : b≤a) (hbc : c≤b)
    (hcd : d≤c) (hde : e≤d) (he : 4≤e) (sum : a+b+c+d+e+3=24+2*t)
    (upper : a≤t+5) (exc₁ : ¬ (a=5 ∧ b=4)) (exc₂ : ¬ (a=5 ∧ e=5)) :
    Planaric ([a,b,c,d,e,3] ++ List.replicate t 2) := by
  let z := min (e-3) (c-d)
  have h := six_path_completion a b 3 d c e 0 (d-4) z t t hab (by omega)
    (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) upper
    (by omega) (by omega) (by dsimp [z]; omega) (by dsimp [z]; omega) (by dsimp [z]; omega)
  have p : [a,b,3,d,c,e].Perm [a,b,c,d,e,3] := by
    apply List.perm_iff_count.mpr
    intro i; simp only [List.count_cons,List.count_nil]; omega
  exact (planaric_perm (p.append_right _)).mp h

end SparseBoundary
