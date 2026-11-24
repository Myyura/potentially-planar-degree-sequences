import Combined.Spectrum
import Mathlib.Order.Lattice.Nat

/-! The extremal subdivision budget of Euler-maximal graphic cores. -/
namespace Combined.Extremal

open SparseBoundary

/-- Minimum budgets attained by graphic cores of order `p`, minimum degree
three or more, and degree sum `6*p - 12`. -/
def budgets (p : ℕ) : Set ℕ := {m | ∃ h : List ℕ, h.length = p ∧
  (∀ x ∈ h, 3 ≤ x) ∧ h.sum + 12 = 6*p ∧ Graphic h ∧ Budget.IsMinimum h 0 m}

/-- The worst minimum budget among the admissible cores. -/
noncomputable def M (p : ℕ) : ℕ := sSup (budgets p)

/-- At each order at least eight the maximum is attained, and the spectrum
construction and sparse theorem give its lower and upper bounds. -/
theorem maximum_and_bounds {p : ℕ} (hp : 8 ≤ p) :
    IsGreatest (budgets p) (M p) ∧ (p-4)/2 ≤ M p ∧ M p ≤ p-6 := by
  have low : (p-4)/2 ∈ budgets p := by
    have witness := Spectrum.fixed_order_spectrum (p:=p) (m:=(p-4)/2) (by omega) le_rfl
    exact ⟨_,witness⟩
  have upper : ∀ m ∈ budgets p, m ≤ p-6 := by
    rintro m ⟨h,rfl,core,sum,graphic,minimum⟩
    exact minimum.2 _ (Budget.maximal_core_upper graphic core hp sum)
  have bounded : BddAbove (budgets p) := ⟨p-6,fun _ => upper _⟩
  have attained : M p ∈ budgets p := Nat.sSup_mem ⟨_,low⟩ bounded
  exact ⟨⟨attained,fun _ hm => le_csSup bounded hm⟩,le_csSup bounded low,upper _ attained⟩

end Combined.Extremal
