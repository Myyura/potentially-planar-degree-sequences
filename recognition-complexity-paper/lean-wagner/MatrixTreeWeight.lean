import ArithmeticRotation
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.MvPolynomial.Basic

/-! The block determinant's Schur reduction and the coefficients after the
weighted matrix-tree expansion. The latter classical identity for a reduced
incidence matrix is the separate step between these two statements. -/
namespace Recognition.MatrixTreeWeight
open Matrix Finset MvPolynomial
open scoped BigOperators Matrix

/-- The concrete Schur complement used by the arithmetic test, for any
rectangular matrix `B` and all specializations with nonzero denominators. -/
theorem schur {E V K : Type*} [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V] [Field K]
    (B : Matrix V E K) (c : E → K) (nonzero : ∀ e, 1+c e ≠ 0) :
    (fromBlocks (1+diagonal c) (diagonal c * B.transpose) (-B) (0 : Matrix V V K)).det =
      (∏ e, (1+c e)) * (B * diagonal (fun e => c e/(1+c e)) * B.transpose).det := by
  let A := diagonal (fun e => 1+c e)
  let D := diagonal (fun e => (1+c e)⁻¹)
  have da : D*A=1 := by simp [D,A,Matrix.diagonal_mul_diagonal,nonzero]
  have ad : A*D=1 := by simp [D,A,Matrix.diagonal_mul_diagonal,nonzero]
  let : Invertible A := ⟨D,da,ad⟩
  have same : 1+diagonal c=A := by
    rw [←diagonal_one,diagonal_add]
  rw [same,det_fromBlocks₁₁,show ⅟A = D from rfl,Matrix.neg_mul,Matrix.neg_mul,zero_sub,neg_neg]
  change (diagonal (fun e => 1+c e)).det * _ = _
  rw [det_diagonal]
  have eq : D * diagonal c = diagonal (fun e => c e / (1+c e)) := by
    rw [show D=diagonal (fun e => (1+c e)⁻¹) from rfl,diagonal_mul_diagonal]
    congr 1; funext e; rw [div_eq_mul_inv,mul_comm]
  rw [Matrix.mul_assoc,←Matrix.mul_assoc D,eq,←Matrix.mul_assoc B]

/-- Orient each unordered pair from its smaller to its larger label and
omit the chosen row of the signed vertex--edge incidence matrix. -/
def reducedIncidence {V K : Type*} [LinearOrder V] [Ring K] (root : V) :
    Matrix {v : V // v ≠ root} {e : V × V // e.1 < e.2} K :=
  fun v e => if v.val=e.val.1 then -1 else if v.val=e.val.2 then 1 else 0

/-- The article's reduced oriented incidence matrix is a direct specialization. -/
theorem incidence_schur {V K : Type*} [Fintype V] [LinearOrder V] [Field K]
    (root : V) (c : {e : V × V // e.1 < e.2} → K) (nonzero : ∀ e, 1+c e≠0) :
    let B : Matrix {v : V // v≠root} _ K := reducedIncidence root
    (fromBlocks (1+diagonal c) (diagonal c * B.transpose) (-B) 0).det =
      (∏ e, (1+c e)) * (B * diagonal (fun e => c e/(1+c e)) * B.transpose).det :=
  schur _ _ nonzero

/-- The squarefree multi-index for the edge set `A`. -/
noncomputable def powerKey {E : Type*} (A : Finset E) : E →₀ Nat :=
  Finsupp.indicator A fun _ _ => 1

private theorem key_inj {E : Type*} {U T : Finset E} : powerKey U = powerKey T ↔ U=T := by
  classical
  constructor
  · intro eq
    ext i
    have at_i := congrArg (fun d : E →₀ Nat => d i) eq
    have value (S : Finset E) : powerKey S i = if i∈S then 1 else 0 := by
      by_cases h : i∈S
      · exact (Finsupp.indicator_of_mem h _).trans (ite_eq_left h).symm
      · exact (Finsupp.indicator_of_notMem h _).trans (ite_eq_right h).symm
    change powerKey U i = powerKey T i at at_i
    rw [value,value] at at_i
    by_cases hu : i∈U <;> by_cases ht : i∈T <;> simp_all
  · rintro rfl; rfl

private theorem edge_monomial {E : Type*} (A : Finset E) :
    (∏ e ∈ A, (X e : MvPolynomial E Nat)) = monomial (powerKey A) 1 := by
  simpa only [pow_one,powerKey] using (MvPolynomial.prod_X_pow (R := Nat) (fun _ : E => 1) A)

/-- One tree is retained, and an arbitrary subset of the remaining edges is added. -/
noncomputable def treeTerm {E : Type*} [DecidableEq E] (U T : Finset E) : MvPolynomial E Nat :=
  (∏ e ∈ T, X e) * ∏ e ∈ U\T, (1+X e)

private theorem treeTerm_expansion {E : Type*} [DecidableEq E] (U T : Finset E) (incl : T⊆U) :
    treeTerm U T = ∑ A ∈ U.powerset.filter (fun A => T⊆A), monomial (powerKey A) 1 := by
  classical
  rw [treeTerm,Finset.prod_one_add,Finset.mul_sum]
  apply Finset.sum_bij (fun S _ => T∪S)
  · intro S hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.union_subset incl
      ((Finset.mem_powerset.mp hs).trans Finset.sdiff_subset)),Finset.subset_union_left⟩
  · intro S hs W hw eq
    have a := Finset.mem_powerset.mp hs
    have b := Finset.mem_powerset.mp hw
    ext e
    have eqmem : e∈T∪S ↔ e∈T∪W := by rw [eq]
    by_cases et : e∈T
    · have ns : e∉S := fun m => (Finset.mem_sdiff.mp (a m)).2 et
      have nw : e∉W := fun m => (Finset.mem_sdiff.mp (b m)).2 et
      simp [ns,nw]
    · simpa [et] using eqmem
  · intro A hA
    obtain ⟨sub,sub'⟩ := Finset.mem_filter.mp hA
    refine ⟨A\T,Finset.mem_powerset.mpr (fun e h => Finset.mem_sdiff.mpr
      ⟨(Finset.mem_powerset.mp sub) (Finset.mem_sdiff.mp h).1,(Finset.mem_sdiff.mp h).2⟩),?_⟩
    ext e
    by_cases et : e∈T
    · simp [et,sub' et]
    · simp [et]
  · intro S hs
    have dis : Disjoint T S := Finset.disjoint_left.mpr fun e et es =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hs) es)).2 et
    rw [←Finset.prod_union dis,edge_monomial]

theorem coefficient_treeTerm {E : Type*} [DecidableEq E] (U T A : Finset E) (incl : T⊆U) :
    (treeTerm U T).coeff (powerKey A) = if T⊆A ∧ A⊆U then 1 else 0 := by
  classical
  rw [treeTerm_expansion U T incl,MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial,key_inj,and_comm]

/-- The graph polynomials live on one common vertex set, so each tree
in this family is a spanning tree of `H`. -/
noncomputable def trees {V : Type*} [Fintype V] (H : SimpleGraph V) : Finset (SimpleGraph V) := by
  classical
  exact Finset.univ.filter (fun T => T ≤ H ∧ T.IsTree)

noncomputable def treeWeighted {V : Type*} [Fintype V] (H : SimpleGraph V) : MvPolynomial (Sym2 V) Nat := by
  classical
  exact ∑ T ∈ trees H, treeTerm H.edgeFinset T.edgeFinset

/-- After the matrix-tree formula, the coefficient of the squarefree graph
monomial is exactly the number of spanning trees of that labelled graph. -/
theorem graph_coefficient {V : Type*} [Fintype V] (H G : SimpleGraph V) (sub : G ≤ H) :
    letI := Classical.decEq V
    letI := Classical.decRel G.Adj
    (treeWeighted H).coeff (powerKey G.edgeFinset) = (trees G).card := by
  classical
  rw [treeWeighted,MvPolynomial.coeff_sum]
  have eq (T) (ht : T∈trees H) : (treeTerm H.edgeFinset T.edgeFinset).coeff (powerKey G.edgeFinset) =
      (if T≤G then (1:Nat) else 0) := by
    have sh : T≤H ∧ T.IsTree := by simpa [trees] using ht
    rw [coefficient_treeTerm _ _ _ (SimpleGraph.edgeFinset_mono sh.1)]
    simp only [SimpleGraph.edgeFinset_subset_edgeFinset,sub,and_true]
  rw [Finset.sum_congr rfl eq,←Finset.sum_filter]
  have same : (trees H).filter (fun T => T≤G) = trees G := by
    ext T; simp only [trees,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨fun t => ⟨t.2,t.1.2⟩,fun t => ⟨⟨t.1.trans sub,t.2⟩,t.1⟩⟩
  simp [same]

/-- Precisely the connected labelled graphs have positive spanning-tree count. -/
theorem trees_pos_iff {V : Type*} [Fintype V] (G : SimpleGraph V) : 0 < (trees G).card ↔ G.Connected := by
  classical
  rw [Finset.card_pos]
  constructor
  · rintro ⟨T,ht⟩
    obtain ⟨sub,tree⟩ : T≤G ∧ T.IsTree := by simpa [trees] using ht
    exact tree.connected.mono sub
  · intro connected
    obtain ⟨T,sub,type⟩ := connected.exists_isTree_le
    exact ⟨T,by simp [trees,sub,type]⟩

/-- The precise positive weight in the trace expansion is the graph's
spanning-tree count times the choices of starting darts at its vertices. -/
noncomputable def rotationWeight (ds : List Nat) (G : ArithmeticRotation.ConnectedRealization ds)
    (_ : ArithmeticRotation.Rotation G.val) : Nat := (trees G.val).card * ds.prod

theorem tree_weighted_difference (ds : List Nat) (positive : ∀ d ∈ ds, 0<d) :
    0 < SphericalTerm.alternating (ArithmeticRotation.rowInventory ds (rotationWeight ds))
        (ds.sum / 2 + 2 - ds.length) ↔
      ∃ G : ArithmeticRotation.ConnectedRealization ds, LeanPool.K5MinorFreeChoosability.IsPlanar G.val := by
  apply ArithmeticRotation.row_difference_iff _ positive
  intro G r
  have nonzero (xs : List Nat) (pos : ∀ d ∈ xs, 0 < d) : 0 < xs.prod := by
    induction xs with
    | nil => decide
    | cons x xs ih => exact Nat.mul_pos (pos _ (.head _)) (ih (fun d h => pos _ (.tail _ h)))
  exact Nat.mul_pos ((trees_pos_iff G.val).mpr G.property.1) (nonzero ds positive)

end Recognition.MatrixTreeWeight
