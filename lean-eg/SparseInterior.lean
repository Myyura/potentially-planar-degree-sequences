import BoundaryEG
import SparseBoundary.Remaining
import SparseBoundary.InteriorUniversal
import SparseBoundary.InteriorRepairs
import SparseBoundary.FiveSparse

namespace SparseBoundary
open ErdosGallai

private theorem strip_copies (h : List Nat) (a k : Nat) (many : k≤h.count a) :
    ∃ r, r.Sublist h ∧ h.Perm (List.replicate k a++r) := by
  induction k generalizing h with
  | zero => exact ⟨h,.refl _,by simp⟩
  | succ k ih =>
    have yes : a∈h := List.count_pos_iff.mp (by omega)
    obtain ⟨r,sub,pm⟩ := ih (h.erase a) (by rw [List.count_erase_self]; omega)
    exact ⟨r,sub.trans List.erase_sublist,(List.perm_cons_erase yes).trans
      (by simpa only [List.replicate_succ,List.cons_append] using pm.cons a)⟩

private theorem length_le_volume (h : List Nat) (min : ∀ x∈h,3≤x) :
    4*h.length ≤ h.sum+h.count 3 := by
  induction h with
  | nil => simp
  | cons x l ih =>
    have := min x (by simp)
    have := ih (fun y hy => min y (by simp [hy]))
    by_cases hx : x=3 <;> simp [hx] <;> omega

private theorem bounded_graphic {r : List Nat} (core : Core r) (sz : 4≤r.length)
    (cap : ∀ x∈r,x<r.length) (volume : r.sum≤4*r.length) (even : r.sum%2=0) : Graphic r := by
  by_cases large : 6≤r.length
  · match r with
    | a::b::xs =>
      have m := cap a (by simp)
      have h := sparse_graphic (t:=0) xs (by simpa using large) core.1 core.2
        (by simp at volume ⊢; omega) even (by simp at m; omega)
      simpa [withTwos] using h
    | [] | [_] => simp at sz
  have possibilities : r=[3,3,3,3] ∨ r=[4,4,4,4,4] ∨ r=[4,4,4,3,3] ∨ r=[4,3,3,3,3] := by
    obtain ⟨sort,lower⟩ := core
    match r with
    | [_,_,_,_] | [_,_,_,_,_] => simp at cap even sort lower ⊢ <;> omega
    | [] | [_] | [_,_] | [_,_,_] => simp at sz
    | _::_::_::_::_::_::_ => simp at large
  rcases possibilities with rfl|rfl|rfl|rfl
  · exact planaric_graphic cubic_clique
  · exact ⟨⟨1023⟩,by unfold Graph.Realizes; decide⟩
  · exact ⟨⟨511⟩,by unfold Graph.Realizes; decide⟩
  · exact ⟨⟨507⟩,by unfold Graph.Realizes; decide⟩

/-- Sufficiency throughout the entire strictly sparser region follows from
    the two exact equalities. The induction uses only disjoint K4, edge
    subdivision, and the explicit near-universal repairs. -/
private theorem lower_step (large : LargeExact) (h : List Nat) (t : Nat)
    (ih : ∀ r : List Nat, ∀ s : Nat, r.length+s<h.length+t → Core r → Graphic (profile r s 0) →
      (profile r s 0).sum+2≤4*(profile r s 0).length → profile r s 0 ≠ lowerException → Planaric (profile r s 0))
    (core : Core h) (hg : Graphic (profile h t 0))
    (bound : (profile h t 0).sum+2≤4*(profile h t 0).length)
    (no : profile h t 0 ≠ lowerException) : Planaric (profile h t 0) := by
  by_cases five : h.length≤5
  · exact (lower_sparse_at_most_five core five hg bound).mpr no
  by_cases eq : (profile h t 0).sum+2=4*(profile h t 0).length
  · by_cases seven : h.length≤7
    · have min (x) (hx : x∈profile h t 0) : 2≤x := by
        simp [profile] at hx
        rcases hx with hx|hx
        · have := core.2 x hx; omega
        · omega
      have l0 : (profile h t 0).count 1=0 := List.count_eq_zero.mpr (fun hh=>by have := min 1 hh; omega)
      apply (exact_at_most_seven (j:=1) (by decide) (by intro E; simp [profile] at E; grind)
        (fun x hx => Nat.le_trans (by decide) (min x hx)) hg (by omega)
        (by simpa [high_profile core.2] using seven)).mpr
      simp only [exactBad,one_ne_zero,ite_false]
      intro pm
      have high := pm.countP_eq (fun x => decide (3≤x))
      change highCount (profile h t 0) = 5 at high
      rw [high_profile core.2] at high
      omega
    · exact large h t 1 core (by omega) (by decide) hg eq
  have parity := (eg_of_graphic hg).1
  simp [profile,List.sum_replicate_nat] at parity bound eq
  have strict : h.sum+4≤4*h.length+2*t := by omega
  match h with
  | [] | [_] => simp at five
  | a::b::us =>
    let u:=b::us
    have cap := graphic_degree_lt hg a (by simp [profile])
    simp [profile] at cap
    have others (x) (hx : x∈u) : 3≤x := core.2 x (List.mem_cons_of_mem _ hx)
    have order := core.1
    have vol : a+u.sum+4≤4*(u.length+1)+2*t := strict
    have even : (a+u.sum)%2=0 := by simpa [u,Nat.add_assoc] using parity
    by_cases univ : a=u.length+t
    · have hp := interior_universal u t (by simp [u] at five ⊢; omega) others (by omega) (by omega)
      have pm := (List.perm_append_comm (l₁:=List.replicate t 2) (l₂:=u)).cons a
      rw [← univ] at hp
      simpa [profile,u] using (planaric_perm pm).mp hp
    cases t with
    | succ s =>
      have gr := sparse_graphic (t:=s) us (by simp at five; omega) order core.2
        (by simp [u] at vol; simp; omega) even (by simp [u] at cap univ; omega)
      have gr' : Graphic (profile (a::b::us) s 0) := by simpa [withTwos,profile] using gr
      have smaller := ih (a::b::us) s (by omega) core gr'
        (by simp [profile,List.sum_replicate_nat]; simp [u] at vol; omega) (by
          intro e
          have e' := congrArg highCount e
          change highCount (profile (a::b::us) s 0)=5 at e'
          rw [high_profile core.2] at e'
          omega)
      simp only [profile,List.replicate_zero,List.append_nil]
      exact pad_twos (h:=a::b::us) (s:=s) (t:=s+1) (by simpa [profile] using smaller)
        ⟨a,by simp,by have := core.2 a (by simp); omega⟩ (by omega)
    | zero =>
      simp only [Nat.mul_zero,Nat.add_zero] at vol
      by_cases near : u.length≤a+3
      · have pl := RimGrowth.near_max_interior a u order core.2 (by simp [u] at cap ⊢; omega) near
           (by omega) even
        simpa [profile,u] using pl
      have many := length_le_volume (a::u) core.2
      obtain ⟨r,sub,pm⟩ := strip_copies (a::u) 3 4 (by simp only [List.length_cons,List.sum_cons] at many; omega)
      have len := pm.length_eq
      have sm := pm.sum_nat
      simp only [List.length_append,List.length_replicate,List.sum_append,List.sum_replicate_nat,
        List.length_cons,List.sum_cons] at len sm
      have rCore : Core r := ⟨core.1.sublist sub,fun x hx=>core.2 x (sub.subset hx)⟩
      have maxr (x) (hx : x∈r) : x<r.length := by
        rcases List.mem_cons.mp (sub.subset hx) with rfl|hx
        · omega
        · have hv := List.rel_of_pairwise_cons order hx; omega
      have gr := bounded_graphic rCore (by have := core.2 a (by simp); omega) maxr (by omega) (by omega)
      have upper : r.sum≤4*r.length := by omega
      have restore (p : Planaric r) : Planaric (profile (a::b::us) 0 0) := by
        have join := planaric_append cubic_clique p
        simpa [profile,u] using (planaric_perm pm).mpr join
      by_cases same : r.sum=4*r.length
      · by_cases bad : Exceptional r
        · have hfix := upper_exception_add_four_threes rCore gr same bad
          simpa [profile,u] using (planaric_perm pm).mpr hfix
        apply restore
        have without := upper_iff_without_leaves.mp (upper_from_large large)
        exact without r (by intro e; rw [e] at len; simp at len; omega)
          (fun x hx => Nat.le_trans (by decide) (rCore.2 x hx)) gr same bad
      · apply restore
        have B : (profile r 0 0).sum+2≤4*(profile r 0 0).length := by simp [profile]; omega
        have no : profile r 0 0 ≠ lowerException := by
          simp only [profile,List.replicate_zero,List.append_nil]
          rintro rfl; have := rCore.2 2 (by decide); omega
        simpa [profile] using ih r 0 (by simp [u] at len; simp; omega) rCore (by simpa [profile] using gr) B no

/-- Complete reduction of the full sparse inequality to the two exact equalities. -/
theorem lower_from_exact_normal (large : LargeExact) (h : List Nat) (t : Nat)
    (core : Core h) (hg : Graphic (profile h t 0))
    (bound : (profile h t 0).sum+2≤4*(profile h t 0).length)
    (no : profile h t 0 ≠ lowerException) : Planaric (profile h t 0) := by
  apply lower_step large h t _ core hg bound no
  intro r s smaller
  exact lower_from_exact_normal large r s
termination_by h.length+t

theorem lower_from_large (large : LargeExact) : FirstBoundaryStatement := by
  apply lower_iff_without_leaves.mpr
  intro d _ min hg bound no
  have pos (x) (hx : x∈d) : 1≤x := Nat.le_trans (by decide) (min x hx)
  obtain ⟨h,t,core,p⟩ := normalize_positive d pos
  have l0 : d.count 1=0 := List.count_eq_zero.mpr (fun e => by have := min 1 e; omega)
  rw [l0] at p
  apply (planaric_perm p).mpr
  apply lower_from_exact_normal large h t core ((graphic_perm p).mp hg)
  · rwa [p.sum_nat,p.length_eq] at bound
  · exact fun e => no (e ▸ p)

/-- Both manuscript statements, including all leaves and strict inequalities,
    are together equivalent to the positive construction at the two equalities
    with no leaves and at least eight core vertices. -/
theorem full_iff_large : (FirstBoundaryStatement ∧ SecondBoundaryStatement) ↔ LargeExact := by
  refine ⟨?_,fun L => ⟨lower_from_large L,upper_from_large L⟩⟩
  rintro ⟨lo,up⟩ h t j core big hj hg vol
  let d := profile h t 0
  have high : 8≤highCount d := by simpa [d,high_profile core.2] using big
  have nonempty : d≠[] := by intro e; simp [e,highCount] at high
  have min (x) (hx : x∈d) : 2≤x := by
    simp [d,profile] at hx
    rcases hx with hh|hh
    · have := core.2 x hh; omega
    · omega
  have bound : j=0 ∨ j=1 := by omega
  rcases bound with rfl|rfl
  · exact (upper_iff_without_leaves.mp up) d nonempty min hg (by simpa [d] using vol) (large_not_exceptional high)
  · apply (lower_iff_without_leaves.mp lo) d nonempty min hg (by dsimp [d]; omega)
    intro pm
    have c := pm.countP_eq (fun x => decide (3≤x))
    change highCount d=5 at c
    omega

end SparseBoundary
