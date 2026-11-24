import RecognizingPotentiallyPlanarDegreeSequences.FixedCost
import RecognizingPotentiallyPlanarDegreeSequences.FixedResult

/-! SAT reductions to the Euler-tight budget problems. Their actual output
alphabet is unary, including field delimiters. Both verifiers additionally
accept the binary encoding described in the recognition archive. -/
namespace RecognizingPotentiallyPlanarDegreeSequences.FixedComplexity
open SparseBoundary Recognition FixedBudget FixedVerifier Polynomial

/-- Constant extra depth ensures that every source row can accommodate a
fixed budget, including malformed SAT inputs mapped to small negative rows. -/
def depth : Rule → Nat
  | .fixed r => r
  | .linear => 0

def run (q : Rule) (bits : List Bool) := FixedCost.run (depth q) q bits

def base (q : Rule) (s : List Bool) := FixedCost.padded (depth q) s
def pairs (q : Rule) (s : List Bool) := FixedCost.sourceBudget q (base q s).length
def outputCore (q : Rule) (s : List Bool) := core (base q s) (pairs q s)

theorem fits (q : Rule) (s : List Bool) : pairs q s+3≤(base q s).length := by
  have h := FixedCost.padded_spec (depth q) s
  cases q with
  | fixed r => exact h.2.2.2
  | linear => have n := h.1.1; change (base _ s).length-3+3≤(base _ s).length; dsimp [base] at *;omega

theorem budget_from_order (q : Rule) (s : List Bool) :
    q.budget (outputCore q s).length = pairs q s := by
  cases q with
  | fixed r => rfl
  | linear =>
    have v := (FixedCost.padded_spec 0 s).1
    have e := linear_budget v
    change (core (FixedCost.padded 0 s) ((FixedCost.padded 0 s).length-3)).length/29-1=_
    rw [e]
    change 29*((FixedCost.padded 0 s).length-3+1)/29-1 = (FixedCost.padded 0 s).length-3
    omega

theorem linear_order (s : List Bool) :
    (outputCore .linear s).length=29*(pairs .linear s+1) :=
  linear_budget (FixedCost.padded_spec 0 s).1

/-- All promises hold for both positive and negative SAT instances. Only the
core is written. The verifier computes the budget from the fixed rule. -/
theorem promised (q : Rule) (s : List Bool) :
    let h := outputCore q s
    Wire.fields (run q s).1=some h ∧ (run q s).1.length+12=7*h.length ∧
    Reduction.TableValid h ∧ Graphic h ∧
    (SATBridge.SATLanguage s ↔ Budget.Feasible h 0 (q.budget h.length)) ∧
    (SATBridge.SATLanguage s ↔ ∃ t≤q.budget h.length, Budget.Feasible h 0 t) ∧
    (SATBridge.SATLanguage s → Budget.IsMinimum h 0 (q.budget h.length)) := by
  obtain ⟨valid,graphic,source,_⟩ := FixedCost.padded_spec (depth q) s
  have fit := fits q s
  dsimp only
  rw [budget_from_order]
  refine ⟨?_,FixedCost.run_length _ _ _ fit,core_valid valid fit graphic,core_graphic valid fit graphic,
    source.trans (at_budget_iff valid fit).symm,source.trans (within_budget_iff valid fit).symm,
    fun yes => yes_minimum valid fit (source.mp yes)⟩
  rw [run,FixedCost.run_fields]
  exact Wire.fields_unary _

/-- Karp equivalence on arbitrary input bitstrings, including malformed CNF
encodings, and a polynomial bound for writing the unary output. -/
theorem unary_reduction (q : Rule) :
    (∃ P : Polynomial Nat, ∀ s : List Bool,
      (run q s).2+(run q s).1.length≤P.eval s.length) ∧
    ∀ s : List Bool, SATBridge.SATLanguage s ↔ Language q.budget (run q s).1 := by
  refine ⟨FixedCost.run_polynomial (depth q) q (fits q),fun s => ?_⟩
  have p := promised q s
  simpa only [Language,p.1,Option.some.injEq,exists_eq_left'] using p.2.2.2.2.1

/-- SAT hardness in unary together with a bit certificate and a polynomial
verifier for the same language. Specialize to any fixed r, or to the order
threshold p/29-1. On the latter reduction image, p is a multiple of 29. -/
theorem strong_np_complete (q : Rule) :
    (∃ P : Polynomial Nat, ∀ s : List Bool, (run q s).2+(run q s).1.length≤P.eval s.length) ∧
    (∀ s : List Bool, SATBridge.SATLanguage s ↔ Language q.budget (run q s).1) ∧
    ∃ P Q : Polynomial Nat,
      (∀ s, Language q.budget s ↔ ∃ w : List Bool,
        w.length≤P.eval s.length ∧ (FixedVerifier.run .unary q s w).value=true) ∧
      ∀ s w, (FixedVerifier.run .unary q s w).work≤w.length+Q.eval s.length :=
  ⟨(unary_reduction q).1,(unary_reduction q).2,FixedVerifier.polynomial_verifier .unary q⟩

end RecognizingPotentiallyPlanarDegreeSequences.FixedComplexity
