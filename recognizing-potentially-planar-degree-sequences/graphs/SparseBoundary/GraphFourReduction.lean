import SparseBoundary.GraphUnion
import SparseBoundary.GraphPairInsertion
import SparseBoundary.GraphEightNear
import SparseBoundary.FanUpperHigh
import SparseBoundary.SevenFour

namespace SparseBoundary.FourCore

/-- Upper-boundary numerical hypotheses for cores of minimum degree four. -/
def Input (h : List Nat) (t : Nat) : Prop :=
  h.Pairwise (·≥·) ∧ (∀ d∈h, 4≤d) ∧ h.sum=4*h.length+2*t ∧
    (∀ d∈h,d+1≤h.length+t)

theorem erase_copies (h : List Nat) (u k : Nat) (hc : k≤h.count u) :
    ∃ r, r.Sublist h ∧ h.Perm (List.replicate k u ++ r) := by
  induction k generalizing h with
  | zero => exact ⟨h,.refl _,by simp⟩
  | succ k ih =>
    have mem : u∈h := List.count_pos_iff.mp (by omega)
    have le : k≤(h.erase u).count u := by simp; omega
    obtain ⟨r,sub,per⟩ := ih (h.erase u) le
    exact ⟨r,sub.trans List.erase_sublist,by
      simpa only [List.replicate_succ,List.cons_append] using (List.perm_cons_erase mem).trans (per.cons u)⟩

private theorem excess (h : List Nat) (lo : ∀ v∈h,4≤v) :
    5*h.length ≤ h.sum+h.count 4 := by
  induction h with
  | nil => simp
  | cons v h ih =>
    have hv := lo v (by simp)
    have ht := ih (fun x hx => lo x (by simp [hx]))
    simp only [List.length_cons,List.sum_cons,List.count_cons]
    by_cases e : v=4 <;> simp [e] <;> omega

theorem upper_small {h : List Nat} {t : Nat} (size : 6≤h.length ∧ h.length≤7)
    (budget : 2≤t) (input : Input h t) : Planaric (List.replicate t 2 ++ h) := by
  obtain ⟨order,lo,vol,cap⟩ := input
  apply (planaric_perm List.perm_append_comm).mp
  match h with
  | [a,b,c,d,e,f] =>
    have bound := cap a (by simp)
    have low := lo f (by simp)
    simp at order vol bound
    apply six_min_four a b c d e f t t <;> first | grind | omega
  | [a,b,c,d,e,f,g] =>
    have bound := cap a (by simp)
    have low := lo g (by simp)
    simp at order vol bound
    apply SevenFour.min_four <;> first | grind | omega
  | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | _::_::_::_::_::_::_::_::_ =>
    simp at size

theorem near {h : List Nat} {t : Nat} (size : 8≤h.length) (input : Input h t)
    (near : ∃ x∈h,h.length+t≤x+2) : Planaric (List.replicate t 2 ++ h) := by
  obtain ⟨ord,lo,vol,cap⟩ := input
  match h with
  | [] => simp at size
  | a::r =>
    obtain ⟨x,hx,high⟩ := near
    have le : x≤a := by
      rcases List.mem_cons.mp hx with rfl|hh
      · exact Nat.le_refl _
      · exact List.rel_of_pairwise_cons ord hh
    have ac := cap a (by simp)
    have low (v) (hv : v∈r) := lo v (List.mem_cons_of_mem _ hv)
    simp only [List.length_cons,List.sum_cons] at size vol high ac
    by_cases top : a=r.length+t
    · exact FourCone.near_universal (j:=0) r (by decide) (by omega) low (by omega) (by omega)
    by_cases p8 : r.length=7
    · match r with
      | [b,c,d,e,f,g,h] =>
        have lowh := low h (by simp)
        simp at vol ac high top
        apply FourCone.eight_near a b c d e f g h t ord.of_cons lowh (by omega) (by omega)
      | [] | [_] | [_,_] | [_,_,_] | [_,_,_,_] | [_,_,_,_,_] | [_,_,_,_,_,_] | _::_::_::_::_::_::_::_::_ =>
        simp at p8
    · exact FourCone.near_universal (j:=1) r (by decide) (by omega) low (by omega) (by omega)

/-- On any upper boundary with at least two degree-two entries, every
    sufficiently large counterexample of minimum four reduces to one with
    a single four. In particular, an even number of fours always works.
    The auxiliary hypothesis is confined to smaller cores of the same parity. -/
theorem upper_of_single_four {h : List Nat} {t : Nat} (size : 8≤h.length) (budget : 2≤t)
    (input : Input h t)
    (one : ∀ r,8≤r.length → r.length≤h.length → r.count 4=1 → h.count 4%2=1 →
      Input r t → Planaric (List.replicate t 2 ++ r)) :
    Planaric (List.replicate t 2 ++ h) := by
  generalize hn : h.length=n at *
  induction n using Nat.strongRecOn generalizing h with
  | ind n ih =>
    have original := input
    obtain ⟨order,lo,vol,cap⟩ := input
    by_cases none : h.count 4=0
    · have high (d) (hd : d∈h) : 5≤d := by
        have low := lo d hd
        have ne : d≠4 := by rintro rfl; have := List.count_pos_iff.mpr hd; omega
        omega
      exact Fan.upper_min_five h t (by omega) ⟨order,high,vol,cap⟩
    by_cases single : h.count 4=1
    · exact one h (by omega) (by omega) single (by omega) original
    by_cases top : ∃ x∈h,h.length+t≤x+2
    · exact near (by omega) original top
    obtain ⟨r,sub,perm⟩ := erase_copies h 4 2 (by omega)
    have len := perm.length_eq
    have sum := perm.sum_nat
    have cnt := perm.count_eq 4
    simp only [List.length_append,List.length_replicate,List.sum_append,List.sum_replicate_nat,
      List.count_append,List.count_replicate_self] at len sum cnt
    have data : Input r t := by
      refine ⟨order.sublist sub,fun x hx => lo x (sub.subset hx),by omega,?_⟩
      intro x hx
      have nothi : ¬h.length+t≤x+2 := fun e => top ⟨x,sub.subset hx,e⟩
      omega
    have residual : Planaric (List.replicate t 2 ++ r) := by
      by_cases large : 8≤r.length
      · apply ih r.length (by omega) (h:=r) data rfl large
        intro w hw ub c par dat
        exact one w hw (by omega) c (by omega) dat
      · exact upper_small ⟨by omega,by omega⟩ budget data
    have lifted := restore_equal_pair (g:=4) budget (by decide) residual
    have ed : t+4-4=t := by omega
    rw [ed] at lifted
    exact (planaric_perm (perm.append_left _)).mpr lifted

theorem upper_even_fours {h : List Nat} {t : Nat} (size : 8≤h.length) (budget : 2≤t)
    (input : Input h t) (even : h.count 4%2=0) : Planaric (List.replicate t 2 ++ h) :=
  upper_of_single_four size budget input (fun _ _ _ _ par _ => by omega)

private theorem max_excess {h : List Nat} {t : Nat} (input : Input h t) {x : Nat} (mem : x∈h) :
    x≤4+2*t := by
  have perm := List.perm_cons_erase mem
  have len := perm.length_eq
  have sum := perm.sum_nat
  have each (l : List Nat) (lo : ∀x∈l,4≤x) : 4*l.length≤l.sum := by
    induction l with
    | nil => simp
    | cons x l ih =>
      have head := lo x (by simp)
      have tail := ih (fun x hx => lo x (List.mem_cons_of_mem _ hx))
      simp only [List.length_cons,List.sum_cons]; omega
  have lower := each (h.erase x) (fun v hv => input.2.1 v (List.mem_of_mem_erase hv))
  have vol := input.2.2.1
  simp only [List.sum_cons,List.length_cons] at len sum
  omega

/-- At zero or one subdivision, six fours may be peeled off as an
    independent octahedron until the core has order between eight and
    thirteen. This statement is uniform in the number of vertices. -/
theorem low_budget_from_finite {h : List Nat} {t : Nat} (size : 8≤h.length) (small : t≤1)
    (input : Input h t)
    (base : ∀r,8≤r.length → r.length≤13 → Input r t → Planaric (List.replicate t 2 ++ r)) :
    Planaric (List.replicate t 2 ++ h) := by
  generalize hn : h.length=n at *
  induction n using Nat.strongRecOn generalizing h with
  | ind n ih =>
    by_cases enough : n≤13
    · exact base h (by omega) (by omega) input
    have ex := excess h input.2.1
    have vol := input.2.2.1
    obtain ⟨r,sub,perm⟩ := erase_copies h 4 6 (by omega)
    have len := perm.length_eq
    have sum := perm.sum_nat
    simp only [List.length_append,List.length_replicate,List.sum_append,List.sum_replicate_nat] at len sum
    have data : Input r t := by
      refine ⟨input.1.sublist sub,fun x hx => input.2.1 x (sub.subset hx),by omega,?_⟩
      intro x hx
      have cap := max_excess input (sub.subset hx)
      omega
    have pr : Planaric (List.replicate t 2 ++ r) := ih r.length (by omega) data rfl (by omega)
    have oct : Planaric (List.replicate 6 4) := Graph.Octahedron.realize 0 0 0 0 0 0 0
      (by decide) (by decide) (by decide) (by decide)
    have whole := planaric_append oct pr
    have order : (List.replicate 6 4 ++ (List.replicate t 2 ++ r)).Perm
        (List.replicate t 2 ++ (List.replicate 6 4 ++ r)) := by
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁:=List.replicate 6 4) (l₂:=List.replicate t 2)).append_right r
    exact (planaric_perm (order.trans (perm.symm.append_left _))).mp whole

end SparseBoundary.FourCore
