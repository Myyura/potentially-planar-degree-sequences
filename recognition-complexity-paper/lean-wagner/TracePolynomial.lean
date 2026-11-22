import TraceRotationFibre

/-! The trace differential evaluated on the entire tree-weighted graph
polynomial. All summands use the same matrix-entry variables. -/
namespace Recognition.TracePolynomial
open Classical MvPolynomial TraceDerivative TraceRotationFibre LeanPool.K5MinorFreeChoosability
open scoped BigOperators
noncomputable section

abbrev Entries (ds : List Nat) (q : Nat) :=
  MvPolynomial (Fin ds.length × Fin q × Fin q) Nat

def edgeProduct (ds : List Nat) (q : Nat) (G : SimpleGraph (Fin ds.length)) : Entries ds q :=
  ∑ k : G.Dart → Fin q, ∏ d, X (endIndex (fun d : G.Dart => d.fst) (dartSymm G) q k d)

/-- Spanning-tree multiplicities are the coefficients before substituting edge traces. -/
def graphPolynomial (ds : List Nat) (q : Nat) : Entries ds q :=
  ∑ G : SimpleGraph (Fin ds.length), C (MatrixTreeWeight.trees G).card * edgeProduct ds q G

def applyTrace (ds : List Nat) (q : Nat) (P : Entries ds q) : Nat :=
  ∑ a : Fin (Fintype.card (Slot ds)) → Fin q,
    eval 0 (differentiate (portIndex (slotTail ds) (slotTurn ds) q a) P)

/-- Evaluation on the full polynomial equals the sum over the separately
differentiated graph terms, even at repeated variables and at dimension zero. -/
theorem apply_graph (ds : List Nat) (q : Nat) :
    applyTrace ds q (graphPolynomial ds q) =
      ∑ G : SimpleGraph (Fin ds.length), (MatrixTreeWeight.trees G).card * rowTrace ds q G := by
  unfold applyTrace graphPolynomial rowTrace traceEvaluation edgeProduct
  simp_rw [evaluate_coefficient, coeff_sum, coeff_C_mul, Finset.sum_mul,
    Nat.mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [coeff_sum, Finset.sum_mul, Finset.mul_sum]
  congr!


/-- Evaluation of the differentiated polynomial agrees with the integer
rotation inventory before the spherical finite-difference extraction. -/
theorem inventory (ds : List Nat) (positive : ∀ d ∈ ds, 0 < d) (q : Nat) :
    (applyTrace ds q (graphPolynomial ds q) : ℤ) =
      (ArithmeticRotation.rowInventory ds (MatrixTreeWeight.rotationWeight ds)).eval (q : ℤ) := by
  rw [apply_graph, Nat.cast_sum]
  simpa only [Nat.cast_mul] using all_graphs_inventory ds q positive

end
end Recognition.TracePolynomial
