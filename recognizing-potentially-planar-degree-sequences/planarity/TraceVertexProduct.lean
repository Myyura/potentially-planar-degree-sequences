import TracePower
import TracePolynomial

/-! Ordinary differential matrix traces, multiplied in vertex order, act
on a common polynomial. At zero, a summand depends only on the multiplicity
of each differentiated matrix entry. -/

namespace Recognition.TraceVertexProduct
open Classical MvPolynomial TraceDerivative TraceRotationFibre TracePolynomial
open scoped BigOperators
noncomputable section

private theorem sum_words {R : Type*} [Semiring R] {n : Nat} {J : Fin n → Type*}
    [∀ i, Fintype (J i)] (f : ∀ i, J i → R) :
    (List.ofFn (fun i => ∑ k, f i k)).prod =
      ∑ a : (i : Fin n) → J i, (List.ofFn (fun i => f i (a i))).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ,List.prod_cons, ih (fun i => f i.succ),
      ←(Fin.consEquiv J).sum_comp, Fintype.sum_prod_type,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [List.ofFn_succ, List.prod_cons]
    rfl

abbrev DerOp (S : Type*) := Module.End Nat (MvPolynomial S Nat)

private def op {S : Type*} (x : S) : DerOp S := (pderiv x).toLinearMap

private theorem reverse_action {S : Type*} {n : Nat} (f : Fin n → S) (P : MvPolynomial S Nat) :
    differentiate f P = (((List.ofFn f).map op).reverse.prod) P := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    rw [differentiate,ih, List.ofFn_succ, List.map_cons,List.reverse_cons,List.prod_append]
    simp [Module.End.mul_apply, op]

private def wordCount {S : Type*} (l : List S) : S →₀ Nat :=
  (l.map (fun x => Finsupp.single x 1)).sum

private theorem count_ofFn {S : Type*} {n : Nat} (f : Fin n → S) :
    wordCount (List.ofFn f) = multiplicity f := by
  rw [wordCount,List.map_ofFn,Fin.sum_ofFn]
  rfl

private theorem word_value {S : Type*} [Fintype S] (l : List S) (P : MvPolynomial S Nat) :
    eval 0 ((l.map op).prod P) = P.coeff (wordCount l) * ∏ x, ((wordCount l) x).factorial := by
  have count : multiplicity l.reverse.get = wordCount l := by
    rw [←count_ofFn,List.ofFn_get,wordCount,List.map_reverse,List.sum_reverse]
    rfl
  have act := reverse_action l.reverse.get P
  rw [List.ofFn_get,List.map_reverse,List.reverse_reverse] at act
  rw [←act,evaluate_coefficient,count]

variable (ds : List Nat) (q : Nat)
abbrev Var := Fin ds.length × Fin q × Fin q

def partialMatrix (v : Fin ds.length) : Matrix (Fin q) (Fin q) (DerOp (Var ds q)) :=
  fun i j => op (v,i,j)

/-- The literal product of ordinary matrix traces in the index order of
the input degree sequence. Endomorphism multiplication is composition. -/
def vertexOperator : DerOp (Var ds q) :=
  (List.ofFn (fun v : Fin ds.length => Matrix.trace ((partialMatrix ds q v)^ds[v.val]))).prod

private abbrev Choices := (v : Fin ds.length) → Fin ds[v.val] → Fin q

private def assign : Choices ds q ≃ (Fin (Fintype.card (Slot ds)) → Fin q) :=
  (Equiv.piCurry (fun (v : Fin ds.length) (_ : Fin ds[v.val]) => Fin q)).symm.trans
    ((slotsOrder ds).arrowCongr (Equiv.refl _))

private def atVertex (v : Fin ds.length) (a : Fin ds[v.val] → Fin q) (i : Fin ds[v.val]) :
    Var ds q := (v,a i,a (finRotate ds[v.val] i))

private def allWords (a : Choices ds q) : List (Var ds q) :=
  (List.ofFn (fun v : Fin ds.length => List.ofFn (atVertex ds q v (a v)))).flatten

private theorem summed_operator (positive : ∀ d ∈ ds, 0<d) :
    vertexOperator ds q = ∑ a : Choices ds q, ((allWords ds q a).map op).prod := by
  have expand (v : Fin ds.length) (d : Nat) (pos : 0<d) :
      Matrix.trace ((partialMatrix ds q v)^d) = ∑ a : Fin d → Fin q,
        ((List.ofFn (fun i => ((v,a i,a (finRotate d i)) : Var ds q))).map op).prod := by
    cases d with
    | zero => omega
    | succ d =>
      simpa only [List.map_ofFn, Function.comp_def,partialMatrix] using
        (TracePower.trace_pow (partialMatrix ds q v) d)
  have atV (v : Fin ds.length) : Matrix.trace ((partialMatrix ds q v)^ds[v.val]) =
      ∑ a : Fin ds[v.val] → Fin q, ((List.ofFn (atVertex ds q v a)).map op).prod :=
    expand v _ (positive _ (List.getElem_mem v.isLt))
  unfold vertexOperator
  simp_rw [atV]
  rw [sum_words]
  apply Finset.sum_congr rfl
  intro a _
  simp only [allWords,List.map_flatten,List.prod_flatten,List.map_ofFn,Function.comp_def]

private theorem allcounts (a : Choices ds q) :
    wordCount (allWords ds q a) = multiplicity (portIndex (slotTail ds) (slotTurn ds) q (assign ds q a)) := by
  let f := portIndex (slotTail ds) (slotTurn ds) q (assign ds q a)
  have agree (v : Fin ds.length) (i : Fin ds[v.val]) :
      f (slotsOrder ds ⟨v,i⟩) = atVertex ds q v (a v) i := by
    simp [f, portIndex, slotTail, slotTurn, assign, turn, atVertex]
    exact ⟨rfl,rfl⟩
  rw [wordCount,allWords,List.map_flatten,List.sum_flatten,List.map_ofFn,List.map_ofFn,Fin.sum_ofFn]
  change (∑ v : Fin ds.length, (List.map (fun x => Finsupp.single x 1)
    (List.ofFn (atVertex ds q v (a v)))).sum) = _
  simp only [List.map_ofFn,Fin.sum_ofFn,Function.comp_apply]
  unfold multiplicity
  have h := (slotsOrder ds).sum_comp (fun i => Finsupp.single (f i) (1 : Nat))
  rw [Fintype.sum_sigma] at h
  simpa only [agree] using h

/-- For every input polynomial, the evaluated product of derivative-matrix
traces equals the sum over assignments to the numbered derivative ports. -/
theorem vertex_product (positive : ∀ d ∈ ds, 0<d) (P : Entries ds q) :
    eval 0 ((vertexOperator ds q) P) = applyTrace ds q P := by
  rw [summed_operator ds q positive,LinearMap.sum_apply,map_sum]
  unfold applyTrace
  apply Finset.sum_equiv (assign ds q) (fun _ => by simp)
  intro a _
  rw [word_value,evaluate_coefficient,allcounts]

end
end Recognition.TraceVertexProduct
