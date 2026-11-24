import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A uniform bound for all integer partitions of weight at most M.
Using dyadic multiplicities makes all products and sums finite. -/
namespace Recognition.HistogramCount
open Finset
open scoped BigOperators

private theorem binaryProduct (x : ℝ) (m : Nat) :
    ∑ a ∈ range (2^m), x^a = ∏ t ∈ range m, (1+x^(2^t)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.mul_two, sum_range_add,prod_range_succ]
    simp_rw [pow_add]
    rw [←mul_sum,ih]
    ring

private theorem decay (m : Nat) {a : ℝ} (pos : 0<a) :
    (∑ j ∈ range m, Real.exp (-a*((j:ℝ)+1))) ≤ 1/a := by
  suffices aux : a*(∑ j ∈ range m, Real.exp (-a*((j:ℝ)+1))) + Real.exp (-a*m) ≤ 1 by
    apply (le_div_iff₀ pos).mpr
    linarith [Real.exp_pos (-a*m)]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ,Nat.cast_succ,mul_add]
    have step := mul_le_mul_of_nonneg_right (Real.add_one_le_exp a) (Real.exp_nonneg (-a*((m:ℝ)+1)))
    rw [←Real.exp_add,show a + -a*((m:ℝ)+1) = -a*m by ring] at step
    linarith

private theorem dyadic (m : Nat) : (∑ t ∈ range m, (1:ℝ)/2^t) ≤ 2 := by
  suffices eq : (∑ t ∈ range m, (1:ℝ)/2^t) + 2/2^m = 2 by
    linarith [show (0:ℝ)≤2/2^m by positivity]
  induction m with
  | zero => simp
  | succ m ih => rw [sum_range_succ,pow_succ, add_assoc _ (1 / _), show (1:ℝ)/2^m + 2/(2^m*2) = 2/2^m by ring]; exact ih

abbrev Histogram (M : Nat) := Fin M → Fin (M+1)
def mass {M : Nat} (h : Histogram M) := ∑ j, (j.val+1)*(h j).val
def candidates (M : Nat) := (univ : Finset (Histogram M)).filter fun h => mass h≤M

private theorem column (M : Nat) (j : Fin M) (k : ℝ) :
    (∑ a : Fin (M+1), Real.exp (-((j.val:ℝ)+1)*(a.val:ℝ)/k)) ≤
      Real.exp (∑ t ∈ range M, Real.exp (-((2:ℝ)^t/k)*((j.val:ℝ)+1))) := by
  let x := Real.exp (-((j.val:ℝ)+1)/k)
  have powers (u : Nat) : Real.exp (-((j.val:ℝ)+1)*(u:ℝ)/k)=x^u := by
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [powers]
  rw [Fin.sum_univ_eq_sum_range]
  have inc : M+1≤2^M := Nat.lt_two_pow_self
  calc
    _ ≤ ∑ a ∈ range (2^M), x^a := sum_le_sum_of_subset_of_nonneg (range_mono inc) (by intros; dsimp [x]; positivity)
    _ = ∏ t ∈ range M, (1+x^(2^t)) := binaryProduct x M
    _ ≤ Real.exp (∑ t ∈ range M, x^(2^t)) := Real.prod_one_add_le_exp_sum _ (fun _ => by dsimp [x]; positivity)
    _ = _ := by
      congr 1
      apply sum_congr rfl
      intro t ht
      dsimp [x]; rw [←Real.exp_nat_mul]
      push_cast
      congr 1
      ring

/-- Uniform in the part multiplicities, including every positive-part
histogram with total weight at most M. At k=√M the bound is exp(3√M). -/
theorem count (M : Nat) (k : ℝ) (pos : 0<k) :
    ((candidates M).card : ℝ) ≤ Real.exp ((M:ℝ)/k+2*k) := by
  classical
  let w (j : Fin M) (a : Fin (M+1)) := Real.exp (-((j.val:ℝ)+1)*a.val/k)
  let E (h : Histogram M) := Real.exp (-(mass h:ℝ)/k)
  have fact (h : Histogram M) : E h=∏ j, w j (h j) := by
    dsimp [w,E,mass]
    rw [←Real.exp_sum]
    congr 1
    push_cast
    simp only [div_eq_mul_inv, neg_mul, ←sum_mul, sum_neg_distrib, neg_mul]
  have low : (candidates M).card * Real.exp (-(M:ℝ)/k) ≤ ∑ h, E h := by
    calc
      _ = ∑ h ∈ candidates M, Real.exp (-(M:ℝ)/k) := by simp
      _ ≤ ∑ h ∈ candidates M, E h := by
        apply sum_le_sum
        intro h hh
        have bound : (mass h:ℝ) ≤ M := by exact_mod_cast (mem_filter.mp hh).2
        exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg bound) pos.le)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Real.exp_nonneg _)
  simp_rw [fact] at low
  rw [←Fintype.prod_sum] at low
  let f (j : Nat) (t : Nat) := Real.exp (-((2:ℝ)^t/k)*((j:ℝ)+1))
  have each (t : Nat) : (∑ j : Fin M, f j.val t) ≤ k*(1/2^t) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => f j t)]
    calc
      _ ≤ 1/((2:ℝ)^t/k) := decay M (by positivity)
      _ = _ := by simp [div_eq_mul_inv,mul_comm]
  have total : (∑ j : Fin M, ∑ t ∈ range M, f j.val t) ≤ 2*k := by
    rw [sum_comm]
    calc
      _ ≤ ∑ t ∈ range M, k*(1/2^t) := sum_le_sum (fun t _ => each t)
      _ ≤ k*2 := by rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (dyadic M) pos.le
      _ = _ := mul_comm _ _
  have upper := calc
    (∏ j : Fin M, ∑ a : Fin (M+1), w j a) ≤ ∏ j : Fin M, Real.exp (∑ t ∈ range M, f j.val t) :=
      prod_le_prod₀ (fun _ _ => sum_nonneg (fun _ _ => Real.exp_nonneg _)) (fun j _ => column M j k)
    _ ≤ Real.exp (2*k) := by rw [←Real.exp_sum]; exact Real.exp_le_exp.mpr total
  have net := low.trans upper
  rw [neg_div, Real.exp_neg,←div_eq_mul_inv] at net
  rw [Real.exp_add,mul_comm]
  exact (div_le_iff₀ (Real.exp_pos _)).mp net

theorem sqrt_bound (M : Nat) (positive : 0<M) :
    ((candidates M).card : ℝ) ≤ Real.exp (3*Real.sqrt M) := by
  have pos : 0<Real.sqrt (M:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast positive)
  have eq : (M:ℝ)/Real.sqrt M=Real.sqrt M :=
    (div_eq_iff (ne_of_gt pos)).mpr (by rw [←sq,Real.sq_sqrt (Nat.cast_nonneg M)])
  simpa only [eq,show Real.sqrt M+2*Real.sqrt M=3*Real.sqrt M by ring] using count M _ pos

end Recognition.HistogramCount
