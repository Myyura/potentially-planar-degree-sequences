import Std

namespace SparseBoundary.ErdosGallai

/-- The numerical Erdős–Gallai criterion, on a list supplied in
nonincreasing order. `EG` itself does not impose the ordering. -/
def EG (d : List Nat) : Prop :=
  d.sum % 2 = 0 ∧ ∀ j, j ≤ d.length →
    (d.take j).sum ≤ j*(j-1)+((d.drop j).map (min j)).sum

def withTwos (h : List Nat) (t : Nat) : List Nat := h ++ List.replicate t 2

private theorem sum_lb (xs : List Nat) (k : Nat) (h : ∀ x ∈ xs, k ≤ x) :
    k*xs.length ≤ xs.sum := by
  induction xs with
  | nil => simp
  | cons v xs ih =>
    have := h v (by simp)
    have := ih (by intro i hi; exact h i (by simp [hi]))
    simp only [List.length_cons,List.sum_cons,Nat.mul_succ]; omega

private theorem capped_eq (xs : List Nat) (k : Nat) (h : ∀ x ∈ xs, k ≤ x) :
    (xs.map (min k)).sum = k*xs.length := by
  rw [(List.map_eq_replicate_iff).mpr (fun i hi => Nat.min_eq_left (h i hi)),
    List.sum_replicate_nat, Nat.mul_comm]

private theorem cut_quadratic (j : Nat) (hj : 3≤j) : 6*j ≤ j*(j-1)+12 := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases h : j=2
    · subst j; decide
    · have hj' : 3≤j := by omega
      have hi := ih hj'
      have hmul : j*(j-1)+j=j*j := by
        calc
          _ = j*((j-1)+1) := (Nat.mul_succ ..).symm
          _ = _ := by rw [show (j-1)+1=j by omega]
      simp only [Nat.add_one_sub_one, Nat.succ_mul]
      omega

private theorem high_cuts (h : List Nat) (t : Nat) (hp : 6 ≤ h.length)
    (hm : ∀ v ∈ h, 3≤v) (hv : h.sum ≤ 4*h.length+2*t)
    (j : Nat) (hj : 3≤j) (hjn : j ≤ (withTwos h t).length) :
    ((withTwos h t).take j).sum ≤ j*(j-1)+(((withTwos h t).drop j).map (min j)).sum := by
  by_cases hcut : j≤h.length
  · have hrem : ∀ v ∈ h.drop j, 3≤v := fun _ hi => hm _ (List.mem_of_mem_drop hi)
    have h1 := sum_lb (h.drop j) 3 hrem
    have h2 := sum_lb ((h.drop j).map (min j)) 3 (by
      intro v hv'
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hv'
      have := hrem d hd; omega)
    have hs := congrArg List.sum (List.take_append_drop j h)
    have hq := cut_quadratic j hj
    simp only [List.sum_append,List.length_map,List.length_drop] at hs h1 h2
    simp only [withTwos,List.take_append_of_le_length hcut,
      List.drop_append_of_le_length hcut,List.map_append,List.map_replicate,
      List.sum_append,List.sum_replicate_nat]
    rw [Nat.min_eq_right (by omega : 2≤j)]
    omega
  · have hle : h.length ≤ j := by omega
    have hmul := Nat.mul_le_mul_left j (show 4≤j-1 by omega)
    simp only [withTwos,List.length_append,List.length_replicate] at hjn
    simp only [withTwos,List.take_append,List.drop_append,List.take_of_length_le hle,
      List.drop_of_length_le hle,List.nil_append,List.take_replicate,List.drop_replicate,
      List.sum_append,List.map_replicate,List.sum_replicate_nat]
    rw [Nat.min_eq_right (by omega : 2≤j)]
    rw [Nat.min_eq_left (by omega : j-h.length≤t)]
    omega

/-- A stronger slack version of the two boundary tests: throughout
`H ≤ 4p+2t`, all cuts from the third onwards follow from the minimum
core degree three. The first two cuts are kept at their exact values. -/
theorem criterion {a b t : Nat} (u : List Nat)
    (hp : 6 ≤ u.length+2) (hm : ∀ v ∈ a::b::u, 3≤v)
    (hv : (a::b::u).sum ≤ 4*(u.length+2)+2*t)
    (he : (a::b::u).sum%2=0) :
    EG (withTwos (a::b::u) t) ↔
      (a ≤ u.length+t+1 ∧ a+b ≤ 2*(u.length+t)+2) := by
  let d := withTwos (a::b::u) t
  have hlen : d.length=u.length+2+t := by simp [d,withTwos]; omega
  have hsmall1 : ∀ v ∈ d.drop 1, 1≤v := by
    intro v hv'
    have hm' := List.mem_of_mem_drop hv'
    change v ∈ (a::b::u) ++ List.replicate t 2 at hm'
    rcases List.mem_append.mp hm' with hu|ht
    · have := hm v hu; omega
    · have := List.mem_replicate.mp ht; omega
  have hsmall2 : ∀ v ∈ d.drop 2, 2≤v := by
    intro v hv'
    have hm' := List.mem_of_mem_drop hv'
    change v ∈ (a::b::u) ++ List.replicate t 2 at hm'
    rcases List.mem_append.mp hm' with hu|ht
    · have := hm v hu; omega
    · have := List.mem_replicate.mp ht; omega
  have right1 := capped_eq (d.drop 1) 1 hsmall1
  have right2 := capped_eq (d.drop 2) 2 hsmall2
  simp only [List.length_drop,hlen] at right1 right2
  have left1 : (d.take 1).sum=a := by simp [d,withTwos]
  have left2 : (d.take 2).sum=a+b := by simp [d,withTwos]
  constructor
  · rintro ⟨_,cuts⟩
    change ∀ j, j≤d.length → _ at cuts
    have c1 := cuts 1 (by omega)
    have c2 := cuts 2 (by omega)
    change (d.take 1).sum ≤ 1*(1-1)+((d.drop 1).map (min 1)).sum at c1
    change (d.take 2).sum ≤ 2*(2-1)+((d.drop 2).map (min 2)).sum at c2
    omega
  · rintro ⟨h1,h2⟩
    constructor
    · simp only [withTwos,List.sum_append,List.sum_replicate_nat]; omega
    intro j hj
    change j≤d.length at hj
    change (d.take j).sum ≤ j*(j-1)+((d.drop j).map (min j)).sum
    match j with
    | 0 => simp
    | 1 => omega
    | 2 => omega
    | k+3 =>
      exact high_cuts (a::b::u) t (by simpa [Nat.add_assoc] using hp) hm
        (by simpa [Nat.add_assoc] using hv) _ (by omega) hj

/-- Exact criterion on both equalities. The first equality uses `k=1`,
the second equality `k=0`. -/
theorem boundary_criterion {a b p t k : Nat} (u : List Nat)
    (hp : p=u.length+2) (h6 : 6≤p) (hm : ∀ v ∈ a::b::u, 3≤v)
    (hvol : (a::b::u).sum + 2*k = 4*p+2*t) :
    EG (withTwos (a::b::u) t) ↔
      a+1 ≤ p+t ∧ 2*p+2 ≤ u.sum+2*k := by
  rw [criterion u (by omega) hm (by omega) (by omega)]
  simp only [List.sum_cons] at hvol
  omega

/-- At eight or more core vertices the tail cut is automatic on both
equalities and throughout the sparser range. -/
theorem large_core_criterion {a b p t : Nat} (u : List Nat)
    (hp : p=u.length+2) (h8 : 8≤p) (hm : ∀ v ∈ a::b::u, 3≤v)
    (hv : (a::b::u).sum ≤ 4*p+2*t)
    (he : (a::b::u).sum%2=0) :
    EG (withTwos (a::b::u) t) ↔ a+1 ≤ p+t := by
  rw [criterion u (by omega) hm (by omega) he]
  have hu := sum_lb u 3 (fun v hi => hm v (by simp [hi]))
  simp only [List.sum_cons] at hv
  omega


private theorem perm_sum {u v : List Nat} (h : u.Perm v) : u.sum=v.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp [Nat.add_left_comm]
  | trans _ _ i j => exact i.trans j

/-- The maximum bound suffices in any ordering if the core has at least
eight entries. In particular one may sort the residual after a reduction. -/
theorem large_core_of_bound (h : List Nat) (t : Nat) (h8 : 8≤h.length)
    (hm : ∀ d ∈ h, 3≤d) (hmax : ∀ d ∈ h, d+1≤h.length+t)
    (hv : h.sum≤4*h.length+2*t) (he : h.sum%2=0) : EG (withTwos h t) := by
  match h with
  | a::b::us =>
    exact (large_core_criterion us (by simp) h8 hm hv he).mpr (hmax a (by simp))

private theorem sum_ub (xs : List Nat) (k : Nat) (h : ∀ x ∈ xs, x≤k) :
    xs.sum ≤ k*xs.length := by
  induction xs with
  | nil => simp
  | cons v xs ih =>
    have := h v (by simp)
    have := ih (by intro i hi; exact h i (by simp [hi]))
    simp only [List.length_cons,List.sum_cons,Nat.mul_succ]; omega

/-- Remove a three and lower a largest entry, then reorder arbitrarily.
The ordinary cut criterion is preserved on both boundary layers for
p ≥ 9; the residual has p−1 core entries and the same subdivision count. -/
theorem reduce_three {a b p t k : Nat} (us rs : List Nat)
    (hp : p=us.length+2) (h9 : 9≤p) (hk : k≤1)
    (hm : ∀ d ∈ a::b::us, 3≤d) (hs : (a::b::us).Pairwise (· ≥ ·))
    (h3 : 3 ∈ b::us)
    (hvol : (a::b::us).sum + 2*k = 4*p+2*t)
    (he : EG (withTwos (a::b::us) t))
    (hnew : rs.Perm ((a-1)::(b::us).erase 3)) :
    EG (withTwos rs t) ∧ rs.length+1=p ∧ rs.sum+2*k=4*rs.length+2*t := by
  have ham := ((boundary_criterion us hp (by omega) hm hvol).mp he).1
  have hall : ∀ v ∈ a::b::us, v≤a := by
    intro v hv
    rcases List.mem_cons.mp hv with q|q
    · omega
    · exact List.rel_of_pairwise_cons hs q
  have hsum := sum_ub _ _ hall
  have ha4 : 4≤a := by
    apply Nat.le_of_not_lt; intro hsmall
    have hc := sum_ub _ 3 (fun v hv => Nat.le_trans (hall v hv) (by omega))
    simp only [List.length_cons] at hc; omega
  have hbu : b+2≤p+t := by
    have hb := hall b (by simp)
    have htail := sum_lb us 3 (fun v hv => hm v (by simp [hv]))
    simp only [List.sum_cons] at hvol
    omega
  have hperm := List.perm_cons_erase h3
  have hlen := hnew.length_eq
  have hl0 := hperm.length_eq
  have hsum' := perm_sum hnew
  have hs0 := perm_sum hperm
  simp only [List.length_cons] at hl0 hlen
  simp only [List.sum_cons] at hs0 hsum' hvol
  have hlen' : rs.length+1=p := by omega
  have hvol' : rs.sum+2*k=4*rs.length+2*t := by omega
  refine ⟨large_core_of_bound rs t (by omega) ?_ ?_ (by omega) (by omega), hlen',hvol'⟩
  · intro v hv
    rcases List.mem_cons.mp (hnew.mem_iff.mp hv) with hv'|hv'
    · omega
    · have := List.mem_of_mem_erase hv'
      exact hm v (by simp [this])
  · intro v hv
    rcases List.mem_cons.mp (hnew.mem_iff.mp hv) with hv'|hv'
    · omega
    · have hvb : v ≤ b := by
        rcases List.mem_cons.mp (List.mem_of_mem_erase hv') with hl|hl
        · omega
        · exact List.rel_of_pairwise_cons hs.of_cons hl
      omega

/-- Removing one four preserves the cut criterion on the two boundary layers
whenever p≥7, all core targets are at least four and the highest target is
strictly below the universal-vertex value. -/
theorem reduce_four {a p t k : Nat} (xs rs : List Nat)
    (hp : p=xs.length+1) (h7 : 7≤p) (hm : ∀ d ∈ a::xs, 4≤d)
    (hmax : ∀ d ∈ a::xs, d+2≤p+t) (h4 : 4 ∈ a::xs)
    (hvol : (a::xs).sum + 2*k = 4*p+2*t)
    (hnew : rs.Perm ((a::xs).erase 4)) :
    EG (withTwos rs t) ∧ rs.length+1=p ∧ rs.sum+2*k=4*rs.length+2*t := by
  have hperm := List.perm_cons_erase h4
  have hlen := hnew.length_eq
  have hl0 := hperm.length_eq
  have hsum' := perm_sum hnew
  have hs0 := perm_sum hperm
  simp only [List.length_cons] at hl0
  simp only [List.sum_cons] at hs0 hvol
  have hlen' : rs.length+1=p := by omega
  have hvol' : rs.sum+2*k=4*rs.length+2*t := by omega
  have inherit (v) (hv : v ∈ rs) := List.mem_of_mem_erase (hnew.mem_iff.mp hv)
  refine ⟨?_,hlen',hvol'⟩
  match rs with
  | [] => simp at hlen' ; omega
  | [_] => simp at hlen' ; omega
  | b::c::vs =>
    have plen : (b::c::vs).length=vs.length+2 := by simp
    have htail := sum_lb vs 4 (fun v hv => hm v (inherit v (by simp [hv])))
    apply (boundary_criterion vs plen (by omega) (fun v hv => Nat.le_trans (by decide) (hm v (inherit v hv))) hvol').mpr
    have := hmax b (inherit b (by simp))
    omega

/-- With eight or more core vertices, deleting a degree-two vertex from
the lower equality reaches the upper equality when the maximum still fits.
No choice of a particular graphical realization is required. -/
theorem remove_two {a b p t : Nat} (us : List Nat)
    (hp : p=us.length+2) (h8 : 8≤p) (hm : ∀ d ∈ a::b::us, 3≤d)
    (hmax : a+1≤p+t)
    (hvol : (a::b::us).sum + 2 = 4*p+2*(t+1)) :
    EG (withTwos (a::b::us) t) := by
  apply (large_core_criterion us hp h8 hm (by omega) (by omega)).mpr hmax

end SparseBoundary.ErdosGallai
