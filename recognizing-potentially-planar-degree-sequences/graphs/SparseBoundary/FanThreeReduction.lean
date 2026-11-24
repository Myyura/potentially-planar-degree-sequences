import SparseBoundary.FanEightThree
import SparseBoundary.SevenBoundary

namespace SparseBoundary.Fan.Three

/-- Numeric assumptions on a large upper-boundary core. -/
def Input (h : List Nat) (t : Nat) : Prop :=
  Core h ∧ h.sum=4*h.length+2*t ∧ (∀v∈h,v+1≤h.length+t)

private theorem remove_two_threes {h : List Nat} (hh : 2≤h.count 3) :
    ∃r, r.Sublist h ∧ h.Perm (3::3::r) := by
  have h1 : 3∈h := List.count_pos_iff.mp (by omega)
  have h2 : 3∈h.erase 3 := by
    apply List.count_pos_iff.mp; rw [List.count_erase_self]; omega
  exact ⟨_,List.erase_sublist.trans List.erase_sublist,
    (List.perm_cons_erase h1).trans ((List.perm_cons_erase h2).cons 3)⟩

private theorem end_pair (r : List Nat) (t : Nat) (hp : Planaric (List.replicate t 2 ++ (r++[3,3]))) :
    Planaric (List.replicate t 2 ++ 3::3::r) :=
  (planaric_perm ((List.perm_append_comm (l₁:=r) (l₂:=[3,3])).append_left _)).mp hp

private theorem eight {r : List Nat} (t : Nat) (ln : r.length=6) (pos : 1≤t) (so : r.Pairwise (·≥·))
    (lo : ∀v∈r,3≤v) (vol : r.sum+6=32+2*t) (cap : ∀v∈r,v≤t+7) :
    Planaric (List.replicate t 2 ++ 3::3::r) := by
  apply end_pair r t
  match r with
  | [a,b,c,d,e,f] =>
    have hf := lo f (by simp)
    have ha := cap a (by simp)
    simp [List.pairwise_cons] at so
    simp only [List.sum_cons,List.sum_nil] at vol
    apply Eight.two_threes a b c d e f t <;> omega
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | _::_::_::_::_::_::_::_ => simp at ln

private theorem seven {r : List Nat} (t : Nat) (ln : r.length=7) (pos : 1≤t) (so : r.Pairwise (·≥·))
    (lo : ∀v∈r,3≤v) (vol : r.sum=28+2*(t+1)) (cap : ∀v∈r,v≤t+7) :
    Planaric (List.replicate (t+1) 2 ++ r) := by
  apply (planaric_perm List.perm_append_comm).mp
  match r with
  | [a,b,c,d,e,f,g] =>
    have hg := lo g (by simp)
    have ha := cap a (by simp)
    simp [List.pairwise_cons] at so
    simp only [List.sum_cons,List.sum_nil] at vol
    apply upper_seven_numeric a b c d e f g (t+1) <;> omega
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] |
      _::_::_::_::_::_::_::_::_ => simp at ln

/-- At positive budget every large upper-boundary core reduces to a core
with at most one three, or is realized directly. The branches at eight
and nine are actual graphs and introduce no finite-case premises. -/
theorem upper_of_at_most_one_from (T : Nat) (hT : 1≤T)
    (few : ∀h t, 8≤h.length → T≤t → Input h t → h.count 3≤1 →
      Planaric (List.replicate t 2++h))
    {h : List Nat} {t : Nat} (size : 8≤h.length) (pos : T≤t) (data : Input h t) :
    Planaric (List.replicate t 2++h) := by
  generalize hn : h.length=n at size
  induction n using Nat.strongRecOn generalizing h t with
  | ind n ih =>
    by_cases fewest : h.count 3≤1
    · exact few h t (by omega) pos data fewest
    obtain ⟨⟨sort,hm⟩,vol,mx⟩ := data
    by_cases universal : ∃v∈h, v+1=n+t
    · obtain ⟨v,member,e⟩ := universal
      cases h with
      | nil => contradiction
      | cons a hs =>
        have ha := mx a (by simp)
        have av : v≤a := by
          rcases List.mem_cons.mp member with h|h
          · omega
          · exact List.rel_of_pairwise_cons sort h
        have hub : a=hs.length+t := by simp only [List.length_cons] at ha hn; omega
        apply Universal.boundary (j:=0) hs (by simp only [List.length_cons] at hn; omega) sort.of_cons
          (fun x m => hm x (by simp [m])) (by decide) hub
        simpa using vol
    have cap {d} (mem : d∈h) : d+2≤n+t := by
      have := mx d mem; have ne : d+1≠n+t := fun e => universal ⟨d,mem,e⟩
      omega
    obtain ⟨r,sub,perm⟩ := remove_two_threes (by omega : 2≤h.count 3)
    have rl := perm.length_eq
    have rs := perm.sum_nat
    simp only [List.length_cons] at rl
    simp only [List.sum_cons] at rs
    have rOrd := sort.sublist sub
    have rLow : ∀v∈r,3≤v := fun v m => hm v (sub.subset m)
    have rCap : ∀v∈r,v+2≤n+t := fun v m => cap (sub.subset m)
    apply (planaric_perm (perm.append_left _)).mpr
    by_cases eight_n : n=8
    · exact eight t (by omega) (by omega) rOrd rLow (by omega) (by intro v m; have := rCap v m; omega)
    have rVol : r.sum=4*r.length+2*(t+1) := by omega
    have pl : Planaric (List.replicate (t+1) 2++r) := by
      by_cases nine_n : n=9
      · apply seven t (by omega) (by omega) rOrd rLow (by omega)
        intro v m; have := rCap v m; omega
      · have inp : Input r (t+1) := ⟨⟨rOrd,rLow⟩,rVol,by intro v m; have := rCap v m; omega⟩
        apply ih r.length (by omega) (h:=r) (t:=t+1) <;> first | exact inp | omega
    have glued := restore_equal_pair (s:=t+1) (g:=3) (by omega) (by decide) pl
    simpa only [show t+1+3-4=t by omega] using glued

theorem upper_of_at_most_one
    (few : ∀h t, 8≤h.length → 1≤t → Input h t → h.count 3≤1 →
      Planaric (List.replicate t 2++h))
    {h : List Nat} {t : Nat} (size : 8≤h.length) (pos : 1≤t) (data : Input h t) :
    Planaric (List.replicate t 2++h) :=
  upper_of_at_most_one_from 1 (by decide) few size pos data

end SparseBoundary.Fan.Three
