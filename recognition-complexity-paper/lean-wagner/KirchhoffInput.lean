import TraceDeterminant
import Mathlib.RingTheory.Localization.FractionRing

namespace Recognition.KirchhoffInput
open TraceDeterminant Matrix MvPolynomial
open scoped BigOperators Matrix
noncomputable section
open Classical

/-- The usual weighted matrix-tree theorem on the complete labelled graph,
in its rooted incidence-matrix form. An unselected edge contributes one. -/
def WeightedMatrixTree : Prop := ∀ (n : Nat) (root : Fin n) (K : Type) [Field K]
    (w : Pair n → K),
  let B : Matrix {v : Fin n // v ≠ root} (Pair n) K := MatrixTreeWeight.reducedIncidence root
  (B * diagonal w * B.transpose).det =
    ∑ T ∈ MatrixTreeWeight.trees (⊤ : SimpleGraph (Fin n)),
      ∏ e, if selected T e then w e else 1

private theorem map_block {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {n : Nat} (root : Fin n) (c : Pair n → R) :
    f (blockDet root c) = blockDet root (fun e => f (c e)) := by
  let B : Matrix {v : Fin n // v ≠ root} (Pair n) R := MatrixTreeWeight.reducedIncidence root
  let C : Matrix {v : Fin n // v ≠ root} (Pair n) S := MatrixTreeWeight.reducedIncidence root
  have entry (v : {v : Fin n // v ≠ root}) (e : Pair n) : f (B v e) = C v e := by
    dsimp [B,C,MatrixTreeWeight.reducedIncidence]
    split <;> simp
  unfold blockDet
  rw [RingHom.map_det]
  congr 1
  ext i j
  rcases i with i|i <;> rcases j with j|j
  · by_cases h : i = j <;> simp [RingHom.mapMatrix_apply,Matrix.diagonal,h]
  · change f ((diagonal c * B.transpose) i j) =
      (diagonal (fun e => f (c e)) * C.transpose) i j
    rw [Matrix.diagonal_mul,Matrix.diagonal_mul,map_mul,Matrix.transpose_apply,Matrix.transpose_apply,entry]
  · change f (-B i j) = -C i j
    rw [map_neg,entry]
  · exact map_zero f

private theorem regular (mt : WeightedMatrixTree) {n : Nat} (root : Fin n) (K : Type) [Field K]
    (c : Pair n → K) (ok : ∀ e, 1 + c e ≠ 0) :
    blockDet root c = ∑ T ∈ MatrixTreeWeight.trees (⊤ : SimpleGraph (Fin n)),
      ∏ e, if selected T e then c e else 1 + c e := by
  have schur := MatrixTreeWeight.incidence_schur root c ok
  unfold blockDet
  rw [schur,mt n root K,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases h : selected T e
  · simp only [ite_eq_left h]
    field_simp [ok]
  · simp [h]

/-- Apply Schur's identity at independent indeterminates, clear in their
fraction field, then specialize the resulting polynomial identity. -/
theorem expansion (mt : WeightedMatrixTree) : KirchhoffExpansion := by
  intro n root S c
  let P := MvPolynomial (Pair n) ℤ
  let K := FractionRing P
  let embed : P →+* K := algebraMap P K
  have inj : Function.Injective embed := IsFractionRing.injective P K
  have ok (e : Pair n) : 1 + embed (X e) ≠ 0 := by
    intro zero
    have pq : (1 + X e : P) = 0 := inj (by simpa [embed] using zero)
    have bad := congrArg (MvPolynomial.eval (fun _ : Pair n => (0 : ℤ))) pq
    simp at bad
  have generic : blockDet root (fun e : Pair n => (X e : P)) =
      ∑ T ∈ MatrixTreeWeight.trees (⊤ : SimpleGraph (Fin n)),
        ∏ e, if selected T e then (X e : P) else 1 + X e := by
    apply inj
    simpa only [map_block,map_sum,map_prod,apply_ite,map_add,map_one] using
      regular mt root K (fun e => embed (X e)) ok
  let specialize : P →+* MvPolynomial S ℤ := eval₂Hom (Int.castRingHom _) c
  have spec (e : Pair n) : specialize (X e) = c e := eval₂Hom_X' _ _ _
  have h := congrArg specialize generic
  simpa only [map_block,map_sum,map_prod,apply_ite,map_add,map_one,spec] using h

theorem recognition (mt : WeightedMatrixTree) (ds : List Nat) (root : Fin ds.length)
    (positive : ∀ k ∈ ds, 0 < k) (dense : 2 * ds.length ≤ ds.sum) :
    let f := ds.sum / 2 + 2 - ds.length
    0 < (∑ q ∈ Finset.Icc 1 f, (-1 : ℤ)^(f-q) * f.choose q * H ds root q) ↔
      SparseBoundary.Planaric ds :=
  TraceDeterminant.criterion (expansion mt) ds root positive dense

end
end Recognition.KirchhoffInput
