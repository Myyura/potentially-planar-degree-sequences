import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-! The size calculation in the ETH question. Exponents are measured on the
explicit number of vertices. No existence of the hypothetical reduction is used. -/
namespace Recognition.QuadraticTransfer

def Subroot (f : Nat → Nat) : Prop :=
  ∀ k : Nat, ∃ B : Nat, ∀ n≥B, k*f n ≤ n.sqrt

def Sublinear (f : Nat → Nat) : Prop :=
  ∀ k : Nat, ∃ B : Nat, ∀ n≥B, k*f n ≤ n

/-- A quadratic order bound suffices even if the orders of some target
instances stay bounded while the source size grows without bound. -/
theorem exponents (order f : Nat → Nat) (small : Subroot f)
    (h : ∃ c N : Nat, ∀ n≥N, order n ≤ c*n^2) : Sublinear (f ∘ order) := by
  obtain ⟨c,N,cap⟩ := h
  intro k
  obtain ⟨B,hB⟩ := small ((c+1)*k)
  let S := ∑ i ∈ Finset.range B, f i
  refine ⟨max N (k*S), fun n hn => ?_⟩
  change k*f (order n) ≤ n
  by_cases b : B≤order n
  · have e := hB (order n) b
    have base := cap n ((Nat.le_max_left ..).trans hn)
    have bound : order n ≤ ((c+1)*n)*((c+1)*n) := by
      nlinarith [Nat.zero_le (c^2*n^2)]
    have root := Nat.sqrt_le_sqrt bound
    rw [Nat.sqrt_eq] at root
    exact Nat.le_of_mul_le_mul_left (by simpa [Nat.mul_assoc] using e.trans root) (by omega : 0<c+1)
  · have m : f (order n) ≤ S := Finset.single_le_sum (fun i _ => Nat.zero_le (f i))
      (Finset.mem_range.mpr (by omega))
    exact (Nat.mul_le_mul_left k m).trans ((Nat.le_max_right ..).trans hn)

end Recognition.QuadraticTransfer
