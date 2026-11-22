import Mathlib.Algebra.Group.ForwardDiff

/-! Extraction of the spherical coefficient after the rotation polynomial
has been obtained. The differential trace expansion itself is a paper proof. -/
namespace Recognition.SphericalTerm
open Finset Polynomial
open scoped BigOperators

def alternating (P : Polynomial ℤ) (f : ℕ) : ℤ :=
  ∑ q ∈ range (f+1), (-1 : ℤ)^(f-q) * (f.choose q : ℤ) * P.eval (q : ℤ)

theorem extraction (P : Polynomial ℤ) (f : ℕ) (bound : P.natDegree ≤ f) :
    alternating P f = (f.factorial : ℤ) * P.coeff f := by
  have expansion := fwdDiff_iter_eq_sum_shift (h := (1 : ℤ)) P.eval f 0
  simp only [zsmul_eq_mul, nsmul_eq_mul, Int.cast_id, mul_one, zero_add] at expansion
  change (∑ q ∈ range (f+1), _) = _
  rw [← expansion]
  rcases bound.eq_or_lt with eq | lt
  · subst f
    rw [P.fwdDiff_iter_degree_eq_factorial]
    change P.coeff P.natDegree * _ = _ * P.coeff P.natDegree
    exact mul_comm _ _
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt lt, Polynomial.coeff_eq_zero_of_natDegree_lt lt]
    simp

theorem positive_iff (P : Polynomial ℤ) (f : ℕ) (bound : P.natDegree ≤ f) :
    0 < alternating P f ↔ 0 < P.coeff f := by
  rw [extraction P f bound]
  exact mul_pos_iff_of_pos_left (by exact_mod_cast Nat.factorial_pos f)

end Recognition.SphericalTerm
