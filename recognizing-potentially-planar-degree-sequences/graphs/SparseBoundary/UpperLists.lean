import SparseBoundary.Boundary

namespace SparseBoundary

def highCount (d : List Nat) := d.countP (fun x => decide (3≤x))

def seeds : List (Nat × List Nat) :=
  [(5,[4,4,4,4,3]),(6,[4,4,4,4,4,2]),(6,[5,5,3,3,3,3])]

def universals (x : Nat) (l : List Nat) (k : Nat) :=
  (x+k)::(l++List.replicate k 1)

def isolated : List (List Nat) :=
  [[5,5,5,5,5,3,2,2],[4,4,4,4,4,4,4],[6,6,6,3,3,3,3,2]]

def Exceptional (d : List Nat) : Prop :=
  highCount d = 5 ∨ (highCount d = 6 ∧ d.count 3 = 3) ∨
  (∃ e∈seeds, d.Perm (universals e.1 e.2 (d.count 1))) ∨ (∃ e∈isolated,d.Perm e)

theorem exceptional_perm {d e : List Nat} (p : d.Perm e) : Exceptional d ↔ Exceptional e := by
  unfold Exceptional highCount
  rw [p.countP_eq, p.count_eq 3,p.count_eq 1]
  have equiv (l : List Nat) : d.Perm l ↔ e.Perm l := ⟨p.symm.trans, p.trans⟩
  simp only [equiv]

private theorem num_high {h : List Nat} (hc : ∀ x∈h,3≤x) (t l : Nat) :
    highCount (profile h t l)=h.length := by
  have hh : h.filter (fun x => decide (3≤x))=h := List.filter_eq_self.mpr (by simpa using hc)
  simp [highCount,profile,List.countP_eq_length_filter,hh]

private theorem suffix_three (h : List Nat) (hc : Core h) :
    (h.length=6 ∧ h.count 3=3) ↔ ∃ a b c, 4≤c ∧ h=[a,b,c,3,3,3] := by
  constructor
  · rintro ⟨hlen,count⟩
    cases h with | nil => simp at hlen | cons a h =>
     cases h with | nil => simp at hlen | cons b h =>
      cases h with | nil => simp at hlen | cons c h =>
       cases h with | nil => simp at hlen | cons d h =>
        cases h with | nil => simp at hlen | cons e h =>
         cases h with | nil => simp at hlen | cons f h =>
          cases h with
          | cons g h => simp at hlen
          | nil =>
            obtain ⟨order,lower⟩ := hc
            refine ⟨a,b,c,?_⟩
            simp_all [List.pairwise_cons,List.count_cons]
            grind
  · rintro ⟨a,b,c,hc4,rfl⟩
    have order := hc.1
    simp [List.pairwise_cons] at order
    have ha : a≠3 := by omega
    have hb : b≠3 := by omega
    have hcc : c≠3 := by omega
    simp [ha,hb,hcc]

/-- Equivalence between the permutation-invariant obstruction list and
    the normalized statement printed in the manuscript. -/
theorem exceptional_profile {d h : List Nat} {t l : Nat}
    (core : Core h) (p : d.Perm (profile h t l)) : Exceptional d ↔ UpperForbidden h t l := by
  rw [exceptional_perm p]
  have h3 : (profile h t l).count 3 = h.count 3 := by simp [profile,List.count_replicate]
  have h1 : (profile h t l).count 1=l := by
    have h1 : 1∉h := fun h1 => by have := core.2 1 h1; omega
    simp [profile,List.count_replicate,List.count_eq_zero.mpr h1]
  have sort_profile : (profile h t l).Pairwise (· ≥ ·) := by
    simp only [profile,List.pairwise_append]
    refine ⟨core.1,⟨by simp,by simp,?_⟩,?_⟩
    · intro a ha b hb
      have := List.eq_of_mem_replicate ha
      have := List.eq_of_mem_replicate hb
      omega
    · intro a ha b hb
      have A := core.2 a ha
      rcases List.mem_append.mp hb with hb|hb <;> have := List.eq_of_mem_replicate hb <;> omega
  have eqv (e : List Nat) (he : e.Pairwise (· ≥ ·)) :
      (profile h t l).Perm e ↔ profile h t l=e := by
    exact ⟨fun pm => List.Perm.eq_of_pairwise (fun a b ab ba => by omega) sort_profile he pm,
      fun heq => heq ▸ List.Perm.rfl⟩
  unfold Exceptional UpperForbidden
  rw [num_high core.2,h3,h1,suffix_three h core]
  have u (a : Nat) (ls : List Nat) (hs : (a,ls)∈seeds) :
      (universals a ls l).Pairwise (· ≥ ·) := by
    simp [seeds] at hs
    rcases hs with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      simp [universals,List.pairwise_cons] <;>
      first | omega | (intro _ he; have := List.eq_of_mem_replicate he; omega)
  have u' (e : Nat × List Nat) (he : e∈seeds) := eqv _ (u e.1 e.2 he)
  have i (e : List Nat) (he : e∈isolated) : e.Pairwise (· ≥ ·) := by
    simp [isolated] at he; rcases he with rfl|rfl|rfl <;> decide
  simp only [List.mem_cons,seeds,isolated,exists_or,or_and_right,exists_eq_left] at *
  simp [universals] at u' ⊢
  grind

/-- Every positive sequence can be put into the manuscript's normal
    form with exactly its original number of leaves. -/
theorem normalize_positive (d : List Nat) (pos : ∀ x∈d,1≤x) :
    ∃ h t, Core h ∧ d.Perm (profile h t (d.count 1)) := by
  induction d with
  | nil => exact ⟨[],0,⟨.nil,by simp⟩,.rfl⟩
  | cons x d ih =>
    obtain ⟨h,t,core,perm⟩ := ih fun y hy => pos y (by simp [hy])
    have hx := pos x (by simp)
    by_cases one : x=1
    · subst x
      refine ⟨h,t,core,(perm.cons 1).trans ?_⟩
      simp only [profile,List.count_cons_self,List.replicate_succ]
      exact ((List.perm_middle (a:=1) (l₁:=h) (l₂:=List.replicate t 2 ++ List.replicate (d.count 1) 1)).symm).trans
        ((List.perm_middle (a:=1) (l₁:=List.replicate t 2) (l₂:=List.replicate (d.count 1) 1)).symm.append_left h)
    by_cases two : x=2
    · subst x
      refine ⟨h,t+1,core,(perm.cons 2).trans ?_⟩
      simpa [profile,List.replicate_succ] using
        (List.perm_middle (a:=2) (l₁:=h) (l₂:=List.replicate t 2 ++ List.replicate (d.count 1) 1)).symm
    · let le := fun a b : Nat => decide (b≤a)
      let h' := (x::h).mergeSort le
      have pm : h'.Perm (x::h) := List.mergeSort_perm _ _
      refine ⟨h',t,⟨?_,?_⟩,(perm.cons x).trans ?_⟩
      · have hp := List.pairwise_mergeSort (le:=le) (by simp [le]; omega)
          (by simp [le]; omega) (x::h)
        simpa [le,h'] using hp
      · intro y hy
        rcases List.mem_cons.mp (pm.mem_iff.mp hy) with rfl|e
        · omega
        · exact core.2 _ e
      · simpa [profile,one] using pm.symm.append_right
          (List.replicate t 2 ++ List.replicate (d.count 1) 1)

end SparseBoundary
