import TraceEdgeLabels
import TraceVertexProduct

/-! The signed block determinant, differentiated over the integers.
The only mathematical input to the final implication is the classical
denominator-cleared weighted Kirchhoff tree formula for arbitrary edge
weights. The passage from that tree sum to graph multiplicities is proved
below. -/
namespace Recognition.TraceDeterminant
open Classical MvPolynomial Matrix TraceDerivative TraceRotationFibre
open scoped BigOperators Matrix
noncomputable section

abbrev Pair (n : Nat) := {p : Fin n × Fin n // p.1 < p.2}

def blockDet {n : Nat} {R : Type*} [CommRing R] (root : Fin n) (c : Pair n → R) : R :=
  let B : Matrix {v : Fin n // v ≠ root} (Pair n) R := MatrixTreeWeight.reducedIncidence root
  (Matrix.fromBlocks (1+diagonal c) (diagonal c * B.transpose) (-B) 0).det

def selected {n : Nat} (G : SimpleGraph (Fin n)) (e : Pair n) := G.Adj e.val.1 e.val.2

/-- The classical tree expansion after clearing the Schur denominators.
It applies to every assignment of multivariate integer edge weights, with
no degree data, colour dimension, embedding, or differential expression. -/
def KirchhoffExpansion : Prop := ∀ (n : Nat) (root : Fin n) (S : Type)
    (c : Pair n → MvPolynomial S ℤ),
  blockDet root c = ∑ T ∈ MatrixTreeWeight.trees (⊤ : SimpleGraph (Fin n)),
    ∏ e, if selected T e then c e else 1+c e

private def fromChoices {n : Nat} (a : Pair n → Bool) : SimpleGraph (Fin n) where
  Adj i j := if h : i < j then a ⟨(i,j),h⟩ = true else
    if h : j < i then a ⟨(j,i),h⟩ = true else False
  symm := ⟨fun i j h => by
    rcases lt_trichotomy i j with lt|rfl|gt <;> simp_all [lt_asymm]⟩
  loopless := ⟨fun _ => by simp⟩

private theorem fromChoices_selected {n : Nat} (a : Pair n → Bool) (e : Pair n) :
    selected (fromChoices a) e ↔ a e = true := by simp [selected,fromChoices,e.property]

private theorem le_selected {n : Nat} (T G : SimpleGraph (Fin n)) :
    T ≤ G ↔ ∀ e : Pair n, selected T e → selected G e := by
  refine ⟨fun sub _ h => sub h,?_⟩
  intro preserves i j h
  rcases lt_or_gt_of_ne h.ne with a|b
  · exact preserves ⟨(i,j),a⟩ h
  · exact (preserves ⟨(j,i),b⟩ h.symm).symm

private def graphChoices (n : Nat) : (Pair n → Bool) ≃ SimpleGraph (Fin n) where
  toFun := fromChoices
  invFun := fun G e => decide (selected G e)
  left_inv := by
    intro a
    funext e
    simp [fromChoices_selected]
  right_inv := by
    intro G
    apply le_antisymm <;> rw [le_selected] <;> intro e h <;>
      simpa [fromChoices_selected] using h

private def asGraphEdge {n : Nat} (G : SimpleGraph (Fin n)) :
    {e : Pair n // selected G e} ≃ TraceEdgeLabels.Edge G where
  toFun e := ⟨e.val.val,e.val.property,e.property⟩
  invFun e := ⟨⟨e.val,e.property.1⟩,e.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def forget {n : Nat} {G : SimpleGraph (Fin n)} (e : TraceEdgeLabels.Edge G) : Pair n :=
  ⟨e.val,e.property.1⟩

private def edgeWeight {n : Nat} {R : Type*} [CommSemiring R]
    (c : Pair n → R) (G : SimpleGraph (Fin n)) : R := ∏ e : TraceEdgeLabels.Edge G, c (forget e)

private theorem prod_choices {n : Nat} {R : Type*} [CommSemiring R]
    (T : SimpleGraph (Fin n)) (c : Pair n → R) :
    ∏ e, (if selected T e then c e else 1+c e) =
      ∑ G : SimpleGraph (Fin n), if T≤G then edgeWeight c G else 0 := by
  let factors (e : Pair n) (b : Bool) : R := if b then c e else if selected T e then 0 else 1
  have term (e : Pair n) : (if selected T e then c e else 1+c e) = ∑ b, factors e b := by
    by_cases h : selected T e <;> simp [factors,h,add_comm]
  simp_rw [term]
  rw [Fintype.prod_sum]
  apply Finset.sum_equiv (graphChoices n) (fun _ => by simp)
  intro a _
  change _ = if T ≤ fromChoices a then _ else _
  by_cases sub : T ≤ fromChoices a
  · rw [ite_eq_left sub]
    have each (e : Pair n) : factors e (a e) = if selected (fromChoices a) e then c e else 1 := by
      by_cases h : selected (fromChoices a) e
      · simp [factors,h,(fromChoices_selected a e).mp h]
      · have off := mt ((le_selected _ _).mp sub e) h
        have b : a e = false := by simpa [fromChoices_selected] using h
        simp [factors,h,off,b]
    simp_rw [each]
    rw [←Finset.prod_filter]
    rw [Finset.prod_subtype (p := selected (fromChoices a)) _ (fun e => by simp) c]
    exact (asGraphEdge (fromChoices a)).prod_comp (fun e => c (forget e))
  · rw [ite_eq_right sub]
    rw [le_selected] at sub
    push Not at sub
    obtain ⟨e,on,off⟩ := sub
    have b : a e = false := by simpa [fromChoices_selected] using off
    exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [factors,b,on])

/-- Regroup the classical tree sum by its underlying simple graph. -/
theorem tree_sum_graphs {n : Nat} {R : Type*} [CommSemiring R] (c : Pair n → R) :
    (∑ T ∈ MatrixTreeWeight.trees (⊤ : SimpleGraph (Fin n)),
      ∏ e, if selected T e then c e else 1+c e) =
      ∑ G : SimpleGraph (Fin n), ((MatrixTreeWeight.trees G).card : R) * edgeWeight c G := by
  simp_rw [prod_choices]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G _
  rw [←Finset.sum_filter]
  have eq : (MatrixTreeWeight.trees (⊤ : SimpleGraph (Fin n))).filter (fun T => T≤G) =
      MatrixTreeWeight.trees G := by ext T; simp [MatrixTreeWeight.trees,and_comm]
  rw [eq,Finset.sum_const,nsmul_eq_mul]

abbrev Var (ds : List Nat) (q : Nat) := Fin ds.length × Fin q × Fin q
abbrev SignedEntries (ds : List Nat) (q : Nat) := MvPolynomial (Var ds q) ℤ

def signedMatrix (ds : List Nat) (q : Nat) (v : Fin ds.length) : Matrix (Fin q) (Fin q) (SignedEntries ds q) :=
  fun i j => X (v,i,j)

def traceWeight (ds : List Nat) (q : Nat) (e : Pair ds.length) : SignedEntries ds q :=
  Matrix.trace (signedMatrix ds q e.val.1 * signedMatrix ds q e.val.2)

private theorem lift_edge (ds : List Nat) (q : Nat) (e : Pair ds.length) :
    MvPolynomial.map Int.ofNatHom
      (Matrix.trace (vertexMatrix q e.val.1 * vertexMatrix q e.val.2)) = traceWeight ds q e := by
  simp [traceWeight,signedMatrix,Matrix.trace,Matrix.diag,Matrix.mul_apply,vertexMatrix]

theorem determinant_polynomial (kirchhoff : KirchhoffExpansion) (ds : List Nat) (root : Fin ds.length) (q : Nat) :
    blockDet root (traceWeight ds q) = MvPolynomial.map Int.ofNatHom (TracePolynomial.graphPolynomial ds q) := by
  rw [kirchhoff,tree_sum_graphs,TracePolynomial.graphPolynomial,map_sum]
  apply Finset.sum_congr rfl
  intro G _
  rw [map_mul,map_C,←TraceEdgeLabels.edgeProduct ds q G,map_prod]
  congr 1
  unfold edgeWeight
  apply Finset.prod_congr rfl
  intro e _
  exact (lift_edge ds q (forget e)).symm

abbrev Op (S : Type*) (R : Type*) [CommSemiring R] := Module.End R (MvPolynomial S R)

/-- Operators paired when extension of coefficients from naturals to integers
intertwines their actions. Sums and ordered products retain the property. -/
private def compatible (S : Type*) : Subsemiring (Op S Nat × Op S ℤ) where
  carrier := {z | ∀ P, z.2 (MvPolynomial.map Int.ofNatHom P) = MvPolynomial.map Int.ofNatHom (z.1 P)}
  zero_mem' := fun _ => (map_zero _).symm
  one_mem' := fun _ => rfl
  add_mem' := by
    intro a b ha hb P
    change a.2 _ + b.2 _ = MvPolynomial.map _ (a.1 P + b.1 P)
    rw [ha P,hb P,map_add]
  mul_mem' := by
    intro a b ha hb P
    change a.2 (b.2 _) = MvPolynomial.map _ (a.1 (b.1 P))
    rw [hb P,ha (b.1 P)]

private def pairOp {S : Type*} (x : S) : compatible S :=
  ⟨((pderiv x).toLinearMap,(pderiv x).toLinearMap),fun _ => pderiv_map⟩

private def traces {n q : Nat} {R : Type*} [Semiring R] (d : Fin n → Nat)
    (M : Fin n → Matrix (Fin q) (Fin q) R) : R :=
  (List.ofFn (fun v : Fin n => Matrix.trace ((M v)^d v))).prod

private theorem map_traces {n q : Nat} {R T : Type*} [Semiring R] [Semiring T] (h : R →+* T)
    (d : Fin n → Nat) (M : Fin n → Matrix (Fin q) (Fin q) R) :
    h (traces d M) = traces d (fun v => (M v).map h) := by
  simp only [traces,map_list_prod,List.map_ofFn,Function.comp_def,AddMonoidHom.map_trace,Matrix.map_pow]

/-- The literal product of the traces of matrix powers of the integer
partial-derivative operators, in increasing order of the vertex labels. -/
def signedOperator (ds : List Nat) (q : Nat) : Op (Var ds q) ℤ :=
  traces (fun v => ds[v.val]) (fun v i j => (pderiv (v,i,j)).toLinearMap)

private theorem lift_operator (ds : List Nat) (q : Nat) (P : TracePolynomial.Entries ds q) :
    (signedOperator ds q) (MvPolynomial.map Int.ofNatHom P) =
      MvPolynomial.map Int.ofNatHom ((TraceVertexProduct.vertexOperator ds q) P) := by
  let S := Var ds q
  let M (v : Fin ds.length) : Matrix (Fin q) (Fin q) (compatible S) := fun i j => pairOp (v,i,j)
  let W := traces (fun v : Fin ds.length => ds[v.val]) M
  let left : compatible S →+* Op S Nat := (RingHom.fst _ _).comp (compatible S).subtype
  let right : compatible S →+* Op S ℤ := (RingHom.snd _ _).comp (compatible S).subtype
  have l : left W = TraceVertexProduct.vertexOperator ds q := map_traces left _ M
  have r : right W = signedOperator ds q := map_traces right _ M
  rw [←l,←r]
  exact W.property P

/-- The integer value of the manuscript's signed determinant after applying
its full product of matrix differential traces, evaluated at X=0. -/
def H (ds : List Nat) (root : Fin ds.length) (q : Nat) : ℤ :=
  MvPolynomial.eval 0 ((signedOperator ds q) (blockDet root (traceWeight ds q)))

theorem H_graph (kirchhoff : KirchhoffExpansion) (ds : List Nat) (root : Fin ds.length)
    (positive : ∀ k ∈ ds, 0 < k) (q : Nat) :
    H ds root q = (TracePolynomial.applyTrace ds q (TracePolynomial.graphPolynomial ds q) : ℤ) := by
  rw [H,determinant_polynomial kirchhoff,lift_operator,←TraceVertexProduct.vertex_product ds q positive]
  simp only [eval_zero,constantCoeff_eq,coeff_map]
  rfl

/-- Given just the universal classical weighted Kirchhoff expansion,
the literal block determinant and literal differential matrix traces
detect potentially planar sequences throughout the dense positive branch. -/
theorem criterion (kirchhoff : KirchhoffExpansion) (ds : List Nat) (root : Fin ds.length)
    (positive : ∀ k ∈ ds, 0 < k) (dense : 2*ds.length ≤ ds.sum) :
    let f := ds.sum/2 + 2 - ds.length
    0 < (∑ q ∈ Finset.Icc 1 f, (-1 : ℤ)^(f-q) * f.choose q * H ds root q) ↔ SparseBoundary.Planaric ds := by
  have nonempty := List.length_pos_iff.mp (Nat.zero_lt_of_lt root.isLt)
  dsimp only
  simp_rw [H_graph kirchhoff ds root positive,TracePolynomial.apply_graph,Nat.cast_sum,Nat.cast_mul]
  exact difference_planaric ds nonempty positive dense

end
end Recognition.TraceDeterminant
