import Combined

/-! Public declarations for the combined manuscript. Run from the repository
root with `lake env lean combined/Audit.lean`. -/

#print axioms Recognition.HardnessResult.restricted
#print axioms Recognition.UnaryHardness.reduction
#print axioms Recognition.WireOutput.accepts
#print axioms Recognition.WireOutput.sound
#print axioms Recognition.WireOutput.cost
#print axioms SparseBoundary.first_boundary
#print axioms SparseBoundary.second_boundary_invariant
#print axioms SparseBoundary.upper_eight_core
#print axioms SparseBoundary.seven_core_obstruction
#print axioms Combined.Budget.maximal_core_minimum_le
#print axioms Combined.Support.Multi.support_minimum_formula
#print axioms Combined.Support.Multi.excess_leaves
#print axioms Combined.Spectrum.fixed_order_spectrum
#print axioms Combined.Spectrum.symmetric_minimum
#print axioms Combined.Extremal.maximum_and_bounds
#print axioms Combined.FixedCut.max_cut_flip
#print axioms Combined.FixedForward.planar_matching
#print axioms Combined.FixedBudget.core_graphic
#print axioms Combined.FixedBudget.core_valid
#print axioms Combined.FixedBudget.at_budget_iff
#print axioms Combined.FixedBudget.within_budget_iff
#print axioms Combined.FixedBudget.yes_minimum
#print axioms Combined.FixedVerifier.polynomial_verifier
#print axioms Combined.FixedComplexity.promised
#print axioms Combined.FixedComplexity.linear_order
#print axioms Combined.FixedComplexity.strong_np_complete
