import LeanPool.K5MinorFreeChoosability.Planar.Hypermap
import Mathlib.GroupTheory.Perm.Fin
import MapCode

/-! Reading the surviving non-tree darts after a spanning-tree contraction
gives a bouquet. A zero-defect bouquet with the darts in cyclic order has a
noncrossing fixed-point-free pairing. -/
namespace Recognition.Bouquet
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability
open PlanarDegrees.MapCode

private theorem detach {D : Type} [Finite D] [DecidableEq D] (σ A : Perm D)
    (inv : ∀ x, A (A x)=x) (keep : D → Prop) (closed : ∀ x, keep (A x) ↔ keep x)
    (xs : List D) :
    ∃ B : Perm D, eulerDefect σ B ≤ eulerDefect σ A ∧
      (∀ x, B (B x)=x) ∧ (∀ x, B x=A x ∨ B x=x) ∧
      (∀ x, keep x → B x=A x) ∧ ∀ x∈xs, ¬keep x → B x=x := by
  classical
  induction xs with
  | nil => exact ⟨A,le_rfl,inv,fun _ => .inl rfl,fun _ _ => rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨B,weak,undo,old,retired,fixed⟩ := ih
    by_cases change : ¬keep x ∧ B x ≠ x
    · let C := B * swap x (B x)
      have step := eulerDefect_mul_swap_right (σ := σ) (α := B) change.2.symm
        (sameCycle_apply_right.mpr (SameCycle.refl B x))
      have atX : C x=x := by simp [C,undo]
      have atY : C (B x)=B x := by simp [C]
      have other {y} (one : y≠x) (two : y≠B x) : C y=B y := by simp [C,swap_apply_of_ne_of_ne one two]
      have keepY : ¬keep (B x) := by
        rcases old x with eq|eq
        · rw [eq,closed]; exact change.1
        · exact False.elim (change.2 eq)
      refine ⟨C,step.trans weak,?_,?_,?_,?_⟩
      · intro y
        by_cases h : y=x
        · simp [h,atX]
        by_cases k : y=B x
        · simp [k,atY]
        rw [other h k,other (by intro eq; exact k ((undo y).symm.trans (congrArg B eq)))
          (fun eq => h (B.injective eq)),undo]
      · intro y
        by_cases h : y=x
        · exact .inr (h ▸ atX)
        by_cases k : y=B x
        · exact .inr (k ▸ atY)
        rw [other h k]; exact old y
      · intro y hy
        rw [other (fun h => change.1 (h ▸ hy)) (fun h => keepY (h ▸ hy))]
        exact retired _ hy
      · intro y hy no
        rcases List.mem_cons.mp hy with rfl|m
        · exact atX
        by_cases h : y=x
        · exact h ▸ atX
        by_cases k : y=B x
        · exact k ▸ atY
        exact (other h k).trans (fixed _ m no)
    · refine ⟨B,weak,undo,old,retired,?_⟩
      intro y hy no
      rcases List.mem_cons.mp hy with rfl|m
      · exact Classical.byContradiction (fun h => change ⟨no,h⟩)
      · exact fixed _ m no

private theorem split_interval {n : Nat} {i j k l : Fin (n+1)}
    (ij : i<j) (jk : j<k) (kl : k<l) :
    ¬ SameCycle (finRotate _ * swap i k) j l := by
  let inside := fun x : Fin (n+1) => i.val<x.val ∧ x.val≤k.val
  have next (x : Fin (n+1)) : inside x ↔ inside ((finRotate (n+1) * swap i k : Perm (Fin (n+1))) x) := by
    simp only [inside,Perm.mul_apply,coe_finRotate]
    have h₁ := i.isLt
    have h₂ := j.isLt
    have h₃ := k.isLt
    have h₄ := l.isLt
    simp only [Fin.lt_def] at ij jk kl
    by_cases a : x=i
    · subst x
      simp only [swap_apply_left]
      split <;> omega
    by_cases b : x=k
    · subst x
      simp only [swap_apply_right]
      split <;> simp_all [Fin.ext_iff,Fin.val_last]
    rw [swap_apply_of_ne_of_ne a b]
    split <;> simp_all [Fin.ext_iff,Fin.val_last] <;> omega
  intro cycle
  have h := sameCycle_of_step (Setoid.ker inside) (fun z => propext (next z)) cycle
  change inside j=inside l at h
  have yes : inside j := ⟨ij,le_of_lt jk⟩
  exact (not_le_of_gt kl) ((h ▸ yes).2)

private theorem all_cycle {n : Nat} (i j : Fin (n+2)) : SameCycle (finRotate _) i j := by
  have move (v : Fin (n+2)) : finRotate _ v ≠ v := mem_support.mp (by simp [support_finRotate])
  exact isCycle_finRotate.sameCycle (move i) (move j)

private theorem count_rotation (n : Nat) : cycleCount (finRotate (n+2)) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨fun a b => Quotient.inductionOn₂ a b (fun x y => Quotient.sound (s := SameCycle.setoid _) (all_cycle x y))⟩,
    inferInstance⟩

private theorem two_bands {n : Nat} {i j k l : Fin (n+2)}
    (ij : i<j) (jk : j<k) (kl : k<l) :
    0 < eulerDefect (finRotate (n+2)) (swap i k * swap j l) := by
  let σ := finRotate (n+2)
  have ik := lt_trans ij jk
  have jl := lt_trans jk kl
  have a : cycleCount (swap i k) + 1 = Nat.card (Fin (n+2)) := by
    have h := cycleCount_mul_swap_of_not_sameCycle (π := (1 : Perm (Fin (n+2))))
      (x := i) (y := k) (by simpa using ik.ne)
    simpa [cycleCount_one] using h
  have ab := cycleCount_mul_swap_of_not_sameCycle (π := swap i k) (x := j) (y := l)
    (fun h => jl.ne (h.eq_of_left (swap_apply_of_ne_of_ne ij.ne' jk.ne)))
  have r := cycleCount_mul_swap_of_sameCycle ik.ne (all_cycle i k)
  have rr := cycleCount_mul_swap_of_not_sameCycle (split_interval ij jk kl)
  have cp : 0<numComponents σ (swap i k * swap j l) := Nat.card_pos
  have c := count_rotation n
  unfold eulerDefect
  rw [← mul_assoc]
  change 0 < (Nat.card (Fin (n+2)) : ℤ) + 2 * (numComponents σ _ : ℤ) - _ - _ - _
  change cycleCount (finRotate (n+2) * swap i k * swap j l)+1 = cycleCount (finRotate (n+2) * swap i k) at rr
  omega

/-- Two interleaved pairs force positive genus in a bouquet, even in the
presence of arbitrary other pairs or fixed darts. -/
theorem no_crossing {n : Nat} (A : Perm (Fin n)) (undo : ∀ x, A (A x)=x)
    (sphere : eulerDefect (finRotate n) A = 0) (i j : Fin n)
    (ij : i<j) (jk : j<A i) (kl : A i<A j) : False := by
  obtain _|_|n := n
  · exact Fin.elim0 i
  · exact (by omega : ¬ i.val<j.val) ij
  let k := A i
  let l := A j
  let keep := fun y => y=i ∨ y=j ∨ y=k ∨ y=l
  have closed (y) : keep (A y) ↔ keep y := by
    have back (z) (h : keep z) : keep (A z) := by
      rcases h with rfl|rfl|eq|eq
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inl ((congrArg A eq).trans (undo i))
      · exact Or.inr (Or.inl ((congrArg A eq).trans (undo j)))
    exact ⟨fun g => undo y ▸ back _ g,back y⟩
  obtain ⟨B,leq,_,_,pres,off⟩ := detach (finRotate (n+2)) A undo keep closed (List.finRange _)
  have hik : i<k := lt_trans ij jk
  have hjl : j<l := lt_trans jk kl
  have hil : i<l := lt_trans ij hjl
  have eq : B = swap i k * swap j l := by
    ext1 y
    by_cases p : keep y
    · rw [pres y p,Perm.mul_apply]
      rcases p with rfl|rfl|p|p
      · rw [swap_apply_of_ne_of_ne ij.ne hil.ne,swap_apply_left]
      · rw [swap_apply_left,swap_apply_of_ne_of_ne hil.ne' kl.ne']
      · rw [p,swap_apply_of_ne_of_ne jk.ne' kl.ne,swap_apply_right]
        exact undo i
      · rw [p,swap_apply_right,swap_apply_of_ne_of_ne ij.ne' jk.ne]
        exact undo j
    · have h := off y (List.mem_finRange _) p
      simp only [keep,not_or] at p
      rw [h,Perm.mul_apply,swap_apply_of_ne_of_ne p.2.1 p.2.2.2,
        swap_apply_of_ne_of_ne p.1 p.2.2.1]
  rw [eq,sphere] at leq
  exact (not_lt_of_ge leq) (two_bands ij jk kl)

/-- Convert the dart involution of a genus-zero bouquet, numbered in vertex
rotation order, to the noncrossing pairing accepted by the binary map code. -/
def chordData {n : Nat} (A : Perm (Fin n)) (undo : ∀ x, A (A x)=x)
    (free : ∀ x, A x ≠ x) (sphere : eulerDefect (finRotate n) A = 0) : Chords n where
  mate := fun a => if h : a<n then (A ⟨a,h⟩).val else a
  bound := by intro i h; simp [h]
  undo := by intro i h; simp [h,(A ⟨i,h⟩).isLt,undo]
  distinct := by intro i h; simpa [h,Fin.ext_iff] using free ⟨i,h⟩
  noncrossing := by
    intro i j ij jk kl bound
    by_cases hi : i<n
    · simp only [hi,↓reduceDIte] at jk
      have hj : j<n := lt_trans jk (A ⟨i,hi⟩).isLt
      simp only [hi,hj,↓reduceDIte] at kl
      exact no_crossing A undo sphere ⟨i,hi⟩ ⟨j,hj⟩ ij jk kl
    · simp only [hi,↓reduceDIte] at jk; omega

#print axioms chordData
end Recognition.Bouquet
