import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.MvPolynomial.PDeriv

/-! The trace of a power is a sum over based cyclic words. Products in the
coefficient semiring are taken in their displayed left-to-right order. -/

namespace Recognition.TracePower
open scoped BigOperators
noncomputable section

variable {V R : Type*} [Fintype V] [DecidableEq V] [Semiring R]

omit [DecidableEq V] in
private theorem sum_cons {n : Nat} (g : (Fin (n+1) → V) → R) :
    (∑ k, g k) = ∑ x, ∑ k, g (Fin.cons x k) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => V)).sum_comp g, Fintype.sum_prod_type]
  rfl

/-- The entry product along an open walk with ordered intermediate labels. -/
def openWord (A : Matrix V V R) {n : Nat} (x y : V) (k : Fin n → V) : R :=
  (List.ofFn (fun i => A ((Fin.cons (α := fun _ => V) x k) i)
    ((Fin.snoc (α := fun _ => V) k y) i))).prod

omit [Fintype V] [DecidableEq V] in
private theorem open_cons (A : Matrix V V R) {n : Nat} (x z y : V) (k : Fin n → V) :
    openWord A x y (Fin.cons z k) = A x z * openWord A z y k := by
  unfold openWord
  rw [← Fin.cons_snoc_eq_snoc_cons, List.ofFn_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,List.prod_cons]

theorem pow_entry (A : Matrix V V R) (n : Nat) (x y : V) :
    (A ^ (n+1)) x y = ∑ k, openWord A x y (n := n) k := by
  induction n generalizing x with
  | zero => simp [openWord, List.ofFn_succ, Fin.snoc_zero]
  | succ n ih =>
    rw [pow_succ',Matrix.mul_apply,sum_cons]
    apply Finset.sum_congr rfl
    intro z _
    rw [ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact (open_cons A x z y k).symm

/-- For positive length, a cyclic word chooses one label for each of its
positions. Its last factor returns to the first position. -/
theorem trace_pow (A : Matrix V V R) (d : Nat) :
    Matrix.trace (A^(d+1)) = ∑ k : Fin (d+1) → V,
      (List.ofFn (fun i => A (k i) (k (finRotate (d+1) i)))).prod := by
  change (∑ x, (A^(d+1)) x x) = _
  rw [sum_cons]
  apply Finset.sum_congr rfl
  intro x _
  rw [pow_entry]
  apply Finset.sum_congr rfl
  intro k _
  unfold openWord
  rw [Fin.snoc_eq_cons_rotate]

/-- The coefficient semiring can in particular be the endomorphisms of a
polynomial semimodule, with composition as multiplication. -/
theorem trace_pderiv_pow {S : Type*} (vars : V → V → S) (d : Nat) :
    let A : Matrix V V (Module.End Nat (MvPolynomial S Nat)) :=
      fun i j => (MvPolynomial.pderiv (vars i j)).toLinearMap
    Matrix.trace (A^(d+1)) = ∑ k : Fin (d+1) → V,
      (List.ofFn (fun i => A (k i) (k (finRotate (d+1) i)))).prod :=
  trace_pow _ d

end
end Recognition.TracePower
