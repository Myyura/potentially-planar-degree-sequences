import IntervalCosts
import HardnessResult

namespace Recognition.IntervalCosts

/-- Choice of a successful sequence of interval moves on the Euler-tight
outputs of the same polynomial-time reduction. -/
theorem sat_iff_trace (ord : CanonicalRow.CanonicalOrderingInput) (bs : List Bool) :
    ∃ ds : List Nat, Wire.readDegrees (SATBridge.satWire bs) = some ds ∧ Reduction.TableValid ds ∧
      (SATBridge.SATLanguage bs ↔ ∃ xs : List Nat, xs.Perm (ds.filter (fun x => 0<x)) ∧
          RowRule.NumericalTrace xs []) := by
  obtain ⟨ds,h,t,_,equiv,_⟩ := HardnessResult.restricted bs
  exact ⟨ds,h,t,equiv.trans (RowRecognition.interval_iff ord ds)⟩

end Recognition.IntervalCosts
