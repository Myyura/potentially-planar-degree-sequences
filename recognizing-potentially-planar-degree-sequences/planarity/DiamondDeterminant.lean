import DiamondRotations

namespace Recognition.DiamondExample
open TraceDeterminant TraceRotationFibre
open scoped BigOperators

private theorem positive : ∀ k ∈ row, 0 < k := by decide
private theorem diamond_degrees (i : V) : Nat.card {j // diamond.Adj i j} = row[i.val] := by
  change Nat.card (diamond.neighborSet i) = _
  rw [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree]
  exact (show ∀ x : V, diamond.degree x = row[x.val] by decide +kernel) i

theorem diamond_trace (q : Nat) :
    (rowTrace row q diamond : ℤ) = 72 * (q:ℤ)^3 + 72*q := by
  classical
  rw [rowTrace_inventory row q positive diamond diamond_degrees,ArithmeticRotation.inventory,
    Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_monomial]
  let := Fintype.ofFinite (ArithmeticRotation.Rotation diamond)
  have reindex : (∑ r : ArithmeticRotation.Rotation diamond,
      (row.prod : ℤ) * (q : ℤ) ^ ArithmeticRotation.exponent diamond r) =
      ∑ o : Orient, (row.prod : ℤ) * (q : ℤ) ^ faces o := by
    symm
    apply Finset.sum_equiv rotations (fun _ => by simp)
    intro o _
    rw [show rotations o = rotation o from rfl,face_count]
  rw [reindex,Fintype.sum_prod_type]
  simp [faces,row]
  ring

/-- The two degree-three vertices are labelled. They force all five edges.
The trace weights are 36 per rotation and the graph has eight spanning trees. -/
theorem determinant (kirchhoff : KirchhoffExpansion) (root : Fin row.length) (q : Nat) :
    H row root q = 576 * (q:ℤ)^3 + 576*q := by
  classical
  rw [H_graph kirchhoff row root positive,TracePolynomial.apply_graph]
  calc
    _ = (((MatrixTreeWeight.trees diamond).card * rowTrace row q diamond : Nat) : ℤ) := by
      apply congrArg (fun n : Nat => (n : ℤ))
      apply Finset.sum_eq_single diamond
      · intro G _ ne
        rw [rowTrace_wrong row q G (fun deg => ne (unique_graph G deg)),mul_zero]
      · simp
    _ = _ := by rw [tree_count,Nat.cast_mul,diamond_trace]; ring

/-- The actual third forward difference at zero. Its constant term is included. -/
theorem third_difference (kirchhoff : KirchhoffExpansion) (root : Fin row.length) :
    (∑ q ∈ Finset.Icc 0 3, (-1 : ℤ)^(3-q) * (3 : Nat).choose q * H row root q) = 3456 := by
  simp_rw [determinant kirchhoff]
  decide +kernel

theorem manuscript_difference (kirchhoff : KirchhoffExpansion) (root : Fin row.length) :
    (∑ q ∈ Finset.Icc 1 3, (-1 : ℤ)^(3-q) * (3 : Nat).choose q * H row root q) = 3456 := by
  simp_rw [determinant kirchhoff]
  decide +kernel

end Recognition.DiamondExample
