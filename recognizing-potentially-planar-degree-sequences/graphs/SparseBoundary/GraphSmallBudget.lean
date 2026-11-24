import SparseBoundary.GraphSmallBudgetProfiles
import SparseBoundary.GraphFourReduction

namespace SparseBoundary.FourCore

private theorem oct : Planaric (List.replicate 6 4) :=
  Graph.Octahedron.realize 0 0 0 0 0 0 0 (by decide) (by decide) (by decide) (by decide)

private theorem append_six_fours {F R : List Nat} {k : Nat}
    (p : Planaric (F ++ List.replicate k 4 ++ R)) :
    Planaric (F ++ List.replicate (k+6) 4 ++ R) := by
  have hp := planaric_append p oct
  have per : ((F ++ List.replicate k 4 ++ R) ++ List.replicate 6 4).Perm
      ((F ++ List.replicate k 4) ++ (List.replicate 6 4 ++ R)) := by
    rw [List.append_assoc (F ++ List.replicate k 4) R (List.replicate 6 4)]
    exact (List.perm_append_comm (l₁:=R) (l₂:=List.replicate 6 4)).append_left (F ++ List.replicate k 4)
  have eqn : List.replicate k 4 ++ List.replicate 6 4=List.replicate (k+6) 4 := by
    apply List.eq_replicate_iff.mpr; exact ⟨by simp,by simp; grind⟩
  have out := (planaric_perm per).mp hp
  rw [← eqn]
  simpa only [List.append_assoc] using out

private theorem repeat_six {F R : List Nat} {offset : Nat} (hb : offset≤8)
    (basis : ∀ n,8≤n → n≤13 → Planaric (F ++ List.replicate (n-offset) 4 ++ R))
    (p : Nat) (hp : 8≤p) : Planaric (F ++ List.replicate (p-offset) 4 ++ R) := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    by_cases small : p≤13
    · exact basis p hp small
    · have reduced := ih (p-6) (by omega) (by omega)
      have lifted := append_six_fours reduced
      rwa [show p-6-offset+6=p-offset by omega] at lifted

/-- The three minimum-four profiles of subdivision budget at most one and
    the four single-three profiles hold for every core order p ≥ 8. -/
theorem all_small_budget_profiles (p : Nat) (hp : 8≤p) : FiniteProfiles.Profiles p := by
  have basis (n : Nat) (lo : 8≤n) (hi : n≤13) : FiniteProfiles.Profiles n := by
    have cases : n=8 ∨ n=9 ∨ n=10 ∨ n=11 ∨ n=12 ∨ n=13 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact FiniteProfiles.Order8.all_profiles
    · exact FiniteProfiles.Order9.all_profiles
    · exact FiniteProfiles.Order10.all_profiles
    · exact FiniteProfiles.Order11.all_profiles
    · exact FiniteProfiles.Order12.all_profiles
    · exact FiniteProfiles.Order13.all_profiles
  unfold FiniteProfiles.Profiles
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have s := repeat_six (F:=[]) (R:=[]) (offset:=0) (by decide)
      (fun n lo hi => by simpa using (basis n lo hi).1) p hp
    simpa using s
  · have s := repeat_six (F:=[2, 5, 5]) (R:=[]) (offset:=2) (by decide)
      (fun n lo hi => by simpa using (basis n lo hi).2.1) p hp
    simpa using s
  · have s := repeat_six (F:=[2, 6]) (R:=[]) (offset:=1) (by decide)
      (fun n lo hi => by simpa using (basis n lo hi).2.2.1) p hp
    simpa using s
  · have s := repeat_six (F:=[5]) (R:=[3]) (offset:=2) (by decide)
      (fun n lo hi => by simpa using (basis n lo hi).2.2.2.1) p hp
    simpa using s
  · have s := repeat_six (F:=[2, 7]) (R:=[3]) (offset:=2) (by decide)
      (fun n lo hi => by simpa using (basis n lo hi).2.2.2.2.1) p hp
    simpa using s
  · have s := repeat_six (F:=[2, 6, 5]) (R:=[3]) (offset:=3) (by decide)
      (fun n lo hi => by simpa using (basis n lo hi).2.2.2.2.2.1) p hp
    simpa using s
  · have s := repeat_six (F:=[2, 5, 5, 5]) (R:=[3]) (offset:=4) (by decide)
      (fun n lo hi => by simpa using (basis n lo hi).2.2.2.2.2.2) p hp
    simpa using s

private theorem extract_highs (r : List Nat) (sort : r.Pairwise (·≥·)) (low : ∀x∈r,4≤x) :
    ∃ u, u.Pairwise (·≥·) ∧ (∀x∈u,5≤x) ∧ r.Perm (u ++ List.replicate (r.length-u.length) 4) := by
  let high := fun x : Nat => decide (5≤x)
  let u := r.filter high
  let v := r.filter (fun x => !high x)
  have per : (u++v).Perm r := List.filter_append_perm high r
  have eqv : v=List.replicate (r.length-u.length) 4 := by
    apply List.eq_replicate_iff.mpr
    constructor
    · have eq := per.length_eq; rw [List.length_append] at eq; omega
    · intro x hx
      obtain ⟨h1,h2⟩ := List.mem_filter.mp hx
      have := low x h1
      simp [high] at h2
      omega
  refine ⟨u,sort.filter _,fun x hx => ?_,eqv ▸ per.symm⟩
  exact of_decide_eq_true (List.mem_filter.mp hx).2

private theorem few_highs {u : List Nat} (lo : ∀x∈u,5≤x) (vol : u.sum≤4*u.length+3) :
    u.length≤3 := by
  have lower (s : List Nat) (h : ∀x∈s,5≤x) : 5*s.length≤s.sum := by
    induction s with
    | nil => simp
    | cons x s ih =>
      have h1 := h x (by simp)
      have h2 := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
      simp only [List.length_cons,List.sum_cons]; omega
  have := lower u lo
  omega

/-- Upper layer with at most one degree-two vertex and minimum core degree
    at least four, including all core orders at least eight. -/
theorem small_budget_min_four {h : List Nat} {t : Nat} (size : 8≤h.length) (budget : t≤1)
    (input : Input h t) : Planaric (List.replicate t 2 ++ h) := by
  obtain ⟨ord,lo,vol,_⟩ := input
  obtain ⟨u,uo,ul,per⟩ := extract_highs h ord lo
  have branches := all_small_budget_profiles h.length size
  apply (planaric_perm (per.append_left _)).mpr
  have length := per.length_eq
  have total := per.sum_nat
  simp only [List.length_append,List.length_replicate] at length
  simp only [List.sum_append,List.sum_replicate_nat] at total
  have eq : u.sum=4*u.length+2*t := by omega
  have cap := few_highs ul (by omega : u.sum≤4*u.length+3)
  match u with
  | [] =>
    have et : t=0 := by simp at eq; omega
    simpa [et] using branches.1
  | [a] =>
    have ha := ul a (by simp)
    simp at eq
    have ea : a=6 := by omega
    have et : t=1 := by omega
    simpa [ea,et] using branches.2.2.1
  | [a,b] =>
    have ha := ul a (by simp)
    have hb := ul b (by simp)
    simp at eq
    have ea : a=5 := by omega
    have eb : b=5 := by omega
    have et : t=1 := by omega
    simpa [ea,eb,et] using branches.2.1
  | [a,b,c] =>
    have ha := ul a (by simp); have hb := ul b (by simp); have hc := ul c (by simp)
    simp at eq; omega
  | _::_::_::_::_ => simp at cap

/-- Upper layer with a single three and at most one degree-two vertex.
    The hypotheses are the numerical core conditions. -/
theorem small_budget_one_three {h : List Nat} {t : Nat} (size : 8≤h.length) (budget : t≤1)
    (sorted : h.Pairwise (·≥·)) (low : ∀ d∈h,3≤d) (count : h.count 3=1)
    (vol : h.sum=4*h.length+2*t) : Planaric (List.replicate t 2 ++ h) := by
  let r := h.erase 3
  have mem : 3∈h := List.count_pos_iff.mp (by omega)
  have pp : h.Perm (r++[3]) := (List.perm_cons_erase mem).trans (List.perm_append_singleton 3 r).symm
  have lb (x) (hx : x∈r) : 4≤x := by
    have l := low x (List.mem_of_mem_erase hx)
    have nc : r.count 3=0 := by simp [r,count]
    have ne : x≠3 := by rintro rfl; have := List.count_pos_iff.mpr hx; omega
    omega
  obtain ⟨u,uo,ul,per⟩ := extract_highs r (sorted.erase _) lb
  have branches := all_small_budget_profiles h.length size
  have p := pp.trans (per.append_right [3])
  apply (planaric_perm (p.append_left _)).mpr
  have len := pp.length_eq; have more := per.length_eq
  have total := p.sum_nat
  simp at len
  simp only [List.length_append,List.length_replicate] at more
  simp only [List.sum_append,List.sum_replicate_nat,List.sum_cons,List.sum_nil,Nat.add_zero] at total
  have eq : u.sum=4*u.length+1+2*t := by omega
  have cap := few_highs ul (by omega : u.sum≤4*u.length+3)
  match u with
  | [] => simp at eq; omega
  | [a] =>
    simp at eq
    by_cases z : t=0
    · have ea : a=5 := by omega
      have en : r.length-1=h.length-2 := by omega
      simpa [z,ea,en] using branches.2.2.2.1
    · have ea : a=7 := by omega
      have et : t=1 := by omega
      have en : r.length-1=h.length-2 := by omega
      simpa [et,ea,en] using branches.2.2.2.2.1
  | [a,b] =>
    have ha := ul a (by simp); have hb := ul b (by simp)
    simp at uo eq
    have ea : a=6 := by omega
    have eb : b=5 := by omega
    have et : t=1 := by omega
    have en : r.length-2=h.length-3 := by omega
    simpa [et,ea,eb,en] using branches.2.2.2.2.2.1
  | [a,b,c] =>
    have ha := ul a (by simp); have hb := ul b (by simp); have hc := ul c (by simp)
    simp at eq
    have ea : a=5 := by omega
    have eb : b=5 := by omega
    have ec : c=5 := by omega
    have et : t=1 := by omega
    have en : r.length-3=h.length-4 := by omega
    simpa [et,ea,eb,ec,en] using branches.2.2.2.2.2.2
  | _::_::_::_::_ => simp at cap

/-- The three profiles on two threes at zero subdivision budget, in both
    boundary layers, for every core order of at least eight. -/
theorem two_threes_no_twos (p : Nat) (hp : 8≤p) :
    Planaric (List.replicate (p-2) 4 ++ [3,3]) ∧
    Planaric ([6] ++ List.replicate (p-3) 4 ++ [3,3]) ∧
    Planaric ([5,5] ++ List.replicate (p-4) 4 ++ [3,3]) := by
  have basis (n : Nat) (lo : 8≤n) (hi : n≤13) :
      Planaric (List.replicate (n-2) 4 ++ [3,3]) ∧
      Planaric ([6] ++ List.replicate (n-3) 4 ++ [3,3]) ∧
      Planaric ([5,5] ++ List.replicate (n-4) 4 ++ [3,3]) := by
    have e : n=8 ∨ n=9 ∨ n=10 ∨ n=11 ∨ n=12 ∨ n=13 := by omega
    rcases e with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨FiniteProfiles.Order8.lower_twothree,FiniteProfiles.Order8.six_twothree,FiniteProfiles.Order8.upper_twothree⟩
    · exact ⟨FiniteProfiles.Order9.lower_twothree,FiniteProfiles.Order9.six_twothree,FiniteProfiles.Order9.upper_twothree⟩
    · exact ⟨FiniteProfiles.Order10.lower_twothree,FiniteProfiles.Order10.six_twothree,FiniteProfiles.Order10.upper_twothree⟩
    · exact ⟨FiniteProfiles.Order11.lower_twothree,FiniteProfiles.Order11.six_twothree,FiniteProfiles.Order11.upper_twothree⟩
    · exact ⟨FiniteProfiles.Order12.lower_twothree,FiniteProfiles.Order12.six_twothree,FiniteProfiles.Order12.upper_twothree⟩
    · exact ⟨FiniteProfiles.Order13.lower_twothree,FiniteProfiles.Order13.six_twothree,FiniteProfiles.Order13.upper_twothree⟩

  refine ⟨?_,?_,?_⟩
  · simpa using repeat_six (F:=[]) (R:=[3,3]) (offset:=2) (by decide)
      (fun n lo hi => by simpa using (basis n lo hi).1) p hp
  · exact repeat_six (offset:=3) (by decide) (fun n lo hi => (basis n lo hi).2.1) p hp
  · exact repeat_six (offset:=4) (by decide) (fun n lo hi => (basis n lo hi).2.2) p hp

end SparseBoundary.FourCore
