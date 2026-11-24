import SparseBoundary.ZeroTruncation
import SparseBoundary.FanEightThree
import SparseBoundary.SevenBoundary
import SparseBoundary.GraphSixLower

namespace SparseBoundary.ZeroCore
open Graph

/-- Three copies of K₄ meet the three edges of the central triangle. -/
private theorem nine_sixes : Planaric [6,6,6,3,3,3,3,3,3] := by
  let A : Graph 3 := ⟨7⟩
  let B : Graph 5 := ⟨831⟩
  let C : Graph 7 := ⟨1700833⟩
  let D : Graph 9 := ⟨55809294369⟩
  have pa : A.Planar := Fan.two_apex_path_planar (by unfold Fan.TwoApexPath; decide +kernel)
  have pb : B.Planar := clique_sum_edge pa 0 1 (by decide) (by decide +kernel) (by decide +kernel)
  have pc : C.Planar := clique_sum_edge pb 2 4 (by decide) (by decide +kernel) (by decide +kernel)
  have pd : D.Planar := clique_sum_edge pc 5 6 (by decide) (by decide +kernel) (by decide +kernel)
  exact (planaric_perm (d:=[3,3,3,3,3,3,6,6,6]) (by decide)).mp
    ⟨D,by unfold Realizes; decide +kernel,pd⟩

private theorem rotate (r : List Nat) (hp : Planaric (r++[3,3])) : Planaric (3::3::r) :=
  (planaric_perm List.perm_append_comm).mp hp

private theorem eight (r : List Nat) (j : Nat) (j1 : j≤1) (ln : r.length=6)
    (ord : r.Pairwise (·≥·)) (lo : ∀x∈r,3≤x) (three : 3∈r)
    (vol : r.sum+6+2*j=32) (cap : ∀x∈r,x≤6) : Planaric (3::3::r) := by
  match r with
  | [a,b,c,d,e,f] =>
    have ha := cap a (by simp)
    have hf := lo f (by simp)
    simp at ord three vol
    have f3 : f=3 := by omega
    subst f
    by_cases top : j=0
    · by_cases threeTail : d=3
      · have e3 : e=3 := by omega
        have hc : 4≤c := by omega
        subst d e
        exact rotate _ (Fan.Eight.five_threes a b c 0 (by omega) (by omega) hc (by omega) (by omega))
      · apply restore_three_mem _ (by simp)
        apply (planaric_perm (List.perm_append_comm (l₁:=[a,b,c,d,e,3]) (l₂:=[2]))).mp
        by_cases e3 : e=3
        · subst e; exact upper_six_two_threes a b c d 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        · exact upper_six_one_three a b c d e 1 (by omega) (by omega) (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)
    · apply restore_three_mem _ (by simp)
      apply (planaric_perm (List.perm_append_comm (l₁:=[a,b,c,d,e,3]) (l₂:=[2]))).mp
      by_cases e3 : e=3
      · subst e
        by_cases c3 : c=3
        · have d3 : d=3 := by omega
          subst c d; exact lower_six_four_threes a b 1 (by omega) (by omega) (by omega)
        · exact lower_six_two_or_three_threes a b c d 1 (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)
      · exact lower_six_one_three a b c d e 1 (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | _::_::_::_::_::_::_::_ => simp at ln

private theorem nine (r : List Nat) (j : Nat) (j1 : j≤1) (ln : r.length=7)
    (ord : r.Pairwise (·≥·)) (lo : ∀x∈r,3≤x) (three : 3∈r)
    (vol : r.sum+6+2*j=36) (cap : ∀x∈r,x≤7) : Planaric (3::3::r) := by
  match r with
  | [a,b,c,d,e,f,g] =>
    have ha := cap a (by simp)
    have hg := lo g (by simp)
    simp at ord three vol
    by_cases bad : a=6 ∧ b=6 ∧ c=6 ∧ d=3 ∧ j=0
    · obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := bad
      have eq : e=3 ∧ f=3 ∧ g=3 := by omega
      obtain ⟨rfl,rfl,rfl⟩ := eq
      exact rotate [6,6,6,3,3,3,3] nine_sixes
    apply restore_three_mem _ (by simpa using three)
    apply (planaric_perm (List.perm_append_comm (l₁:=[a,b,c,d,e,f,g]) (l₂:=[2]))).mp
    by_cases top : j=0
    · apply upper_seven_numeric a b c d e f g 1 <;> omega
    · apply lower_seven_numeric a b c d e f g 1 <;> omega
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | _::_::_::_::_::_::_::_::_ => simp at ln

/-- With at least three threes, a zero-subdivision core reduces to a
    one-subdivision core with two fewer high vertices. At sizes eight
    and nine the target or its residual is realized outright. -/
theorem many (j : Nat) (hj : j≤1) (h : List Nat) (size : 8≤h.length)
    (core : Core h) (vol : h.sum+2*j=4*h.length) (cap : ∀ x∈h, x+1≤h.length)
    (threes : 3≤h.count 3)
    (smaller : ∀ r : List Nat, 8≤r.length → r.length+2=h.length → Core r →
      r.sum+2*j=4*r.length+2 → (∀ x∈r,x≤r.length) → Planaric (2::r)) : Planaric h := by
  obtain ⟨so,hm⟩ := core
  by_cases full : ∃ x∈h,x+1=h.length
  · obtain ⟨v,hv,eq⟩ := full
    cases h with
    | nil => contradiction
    | cons a l =>
      have va : v≤a := by
        rcases List.mem_cons.mp hv with e|e
        · omega
        · exact List.rel_of_pairwise_cons so e
      have hi := cap a (by simp)
      have un := Fan.Universal.boundary (a:=a) (t:=0) (j:=j) l (by simp at size; omega) so.of_cons
        (fun x xh => hm x (by simp [xh])) hj (by simp at hi eq; omega) (by simp at vol; omega)
      exact un
  let r := (h.erase 3).erase 3
  have h3 : 3∈h := List.count_pos_iff.mp (by omega)
  have e3 : 3∈h.erase 3 := List.count_pos_iff.mp (by rw [List.count_erase_self]; omega)
  have pm : h.Perm (3::3::r) := (List.perm_cons_erase h3).trans ((List.perm_cons_erase e3).cons 3)
  have sub : r.Sublist h := List.erase_sublist.trans List.erase_sublist
  have lr := pm.length_eq; have sr := pm.sum_nat; have cr := pm.count_eq 3
  simp only [List.length_cons,List.sum_cons] at lr sr
  have r3 : 3∈r := List.count_pos_iff.mp (by simp at cr; omega)
  have mx (x) (hx : x∈r) : x≤r.length := by
    have hmem := sub.subset hx
    have he := cap x hmem
    have ne : x+1≠h.length := fun e => full ⟨x,hmem,e⟩
    omega
  have rs := so.sublist sub
  have low (x) (hx : x∈r) := hm x (sub.subset hx)
  apply (planaric_perm pm).mpr
  by_cases s6 : r.length=6
  · exact eight r j hj s6 rs low r3 (by omega) (fun x m => by have := mx x m; omega)
  by_cases s7 : r.length=7
  · exact nine r j hj s7 rs low r3 (by omega) (fun x m => by have := mx x m; omega)
  exact restore_three_mem (smaller r (by omega) (by omega) ⟨rs,low⟩ (by omega) mx) r3

end SparseBoundary.ZeroCore
