import ArithmeticRotation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Iterated formal partial derivatives count matchings of *positions*.
The variable attached to different positions may coincide. -/
namespace Recognition.TraceDerivative
open MvPolynomial
open scoped BigOperators
noncomputable section

variable {S P D : Type*}

/-- The exponent of each variable in a product indexed by positions. -/
def multiplicity [Fintype P] (f : P → S) : S →₀ Nat :=
  ∑ i, Finsupp.single (f i) 1

theorem multiplicity_apply [Fintype P] (f : P → S) (x : S) :
    multiplicity f x = Nat.card {i // f i = x} := by
  classical
  simp [multiplicity, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Apply the partial derivatives in the given order. -/
def differentiate : {n : Nat} → (Fin n → S) → MvPolynomial S Nat → MvPolynomial S Nat
  | 0, _, p => p
  | _+1, f, p => differentiate (fun i => f i.succ) (pderiv (f 0) p)

private theorem factorial_increment [Fintype S] (h : S →₀ Nat) (x : S) :
    (∏ i, (h i).factorial) * (h x+1) = ∏ i, ((h + (Finsupp.single x 1 : S →₀ Nat)) i).factorial := by
  classical
  rw [Fintype.prod_eq_mul_prod_compl x (fun i => (h i).factorial),
      Fintype.prod_eq_mul_prod_compl x (fun i => ((h + (Finsupp.single x 1 : S →₀ Nat)) i).factorial)]
  have eq : ∏ i ∈ ({x}ᶜ : Finset S), ((h + (Finsupp.single x 1 : S →₀ Nat)) i).factorial =
      ∏ i ∈ ({x}ᶜ : Finset S), (h i).factorial := by
    apply Finset.prod_congr rfl
    intro i hi
    have ne : x ≠ i := Ne.symm (by simpa using hi)
    simp [ne]
  rw [eq]
  simp [Nat.factorial_succ]
  ring

/-- Evaluation at zero extracts the coefficient of the differentiated
multi-index, multiplied by one factorial for each repeated variable. -/
theorem evaluate_coefficient [Fintype S] {n : Nat} (f : Fin n → S) (p : MvPolynomial S Nat) :
    eval 0 (differentiate f p) = p.coeff (multiplicity f) * ∏ x, (multiplicity f x).factorial := by
  classical
  induction n generalizing p with
  | zero => simp [differentiate,multiplicity,eval_zero,constantCoeff_eq]
  | succ n ih =>
    let h := multiplicity (fun i : Fin n => f i.succ)
    have step : multiplicity f = h + Finsupp.single (f 0) 1 := by
      simp [multiplicity,h,Fin.sum_univ_succ,add_comm]
    rw [differentiate,ih,coeff_pderiv,step]
    change _ * (h (f 0)+1) * _ = _ * _
    rw [←factorial_increment h (f 0)]
    ring

/-- The derivative slots and the polynomial factors are distinguished,
including distinct occurrences carrying the same variable. -/
abbrev Matching (f : P → S) (g : D → S) := {e : P ≃ D // ∀ i, g (e i) = f i}

private def restrictMatch (f : P → S) (g : D → S) (e : Matching f g) (x : S) :
    {i // f i = x} ≃ {j // g j = x} where
  toFun i := ⟨e.val i, (e.property _).trans i.property⟩
  invFun j := ⟨e.val.symm j, by simpa using (e.property (e.val.symm j)).symm.trans (by simpa using j.property)⟩
  left_inv i := Subtype.ext (e.val.symm_apply_apply _)
  right_inv j := Subtype.ext (e.val.apply_symm_apply _)

private def partitionMatch (f : P → S) (g : D → S) :
    Matching f g ≃ (∀ x, {i // f i = x} ≃ {j // g j = x}) where
  toFun := restrictMatch f g
  invFun b := ⟨Equiv.ofFiberEquiv b,Equiv.ofFiberEquiv_map b⟩
  left_inv e := by apply Subtype.ext; ext i; rfl
  right_inv b := by
    funext x
    ext ⟨i,hi⟩
    subst x
    rfl

/-- A repeated variable of multiplicity k admits k! matchings. If any
multiplicity differs, no matching can exist. -/
theorem count_matchings [Fintype S] [Fintype P] [Fintype D] (f : P → S) (g : D → S) :
    Nat.card (Matching f g) = if multiplicity g = multiplicity f then
        ∏ x, (multiplicity f x).factorial else 0 := by
  classical
  by_cases eq : multiplicity g = multiplicity f
  · rw [ite_eq_left eq,Nat.card_congr (partitionMatch f g),Nat.card_pi]
    apply Finset.prod_congr rfl
    intro x _
    rw [multiplicity_apply, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    apply Fintype.card_equiv (Fintype.equivOfCardEq _)
    simpa only [←Nat.card_eq_fintype_card, ←multiplicity_apply] using DFunLike.congr_fun eq.symm x
  · rw [ite_eq_right eq]
    apply (Nat.card_eq_zero).2
    apply Or.inl
    exact ⟨fun e => eq (by ext x; rw [multiplicity_apply,multiplicity_apply];
                            exact Nat.card_congr (restrictMatch f g e x).symm)⟩

/-- The formal mixed derivative of a product of variables, at zero, counts
exactly the compatible bijections, with no distinctness condition on labels. -/
theorem evaluate_product [Fintype S] [Fintype D] {n : Nat} (f : Fin n → S) (g : D → S) :
    eval 0 (differentiate f (∏ j, X (g j))) = Nat.card (Matching f g) := by
  classical
  rw [evaluate_coefficient,count_matchings,
      show (∏ j, (X (g j) : MvPolynomial S Nat)) = monomial (multiplicity g) 1 from
        (monomial_sum_one _ _).symm, coeff_monomial]
  split <;> simp_all

section Trace

variable {V : Type*} (ports : P → V) (ends : D → V) (next : Equiv.Perm P)
  (flip : Equiv.Perm D) (q : Nat)

/-- A vertex trace and an edge trace use reversed index pairs at the
opposite ends of an edge. -/
def portIndex (a : P → Fin q) (p : P) : V × Fin q × Fin q :=
  (ports p, a p, a (next p))

def endIndex (k : D → Fin q) (d : D) : V × Fin q × Fin q :=
  (ends d, k d, k (flip d))

/-- The port successor transported to edge ends, followed in the face
permutation immediately after reversing the current end. -/
def facePerm (e : P ≃ D) : Equiv.Perm D := (e.symm.trans (next.trans e)) * flip

/-- A simultaneous choice of edge indices, derivative indices, and a
compatible matching is a vertex-preserving matching and a colouring
constant around its face cycles. -/
def traceAssignments (involution : Function.Involutive flip) :
    (Σ a : P → Fin q, Σ k : D → Fin q,
      Matching (portIndex ports next q a) (endIndex ends flip q k)) ≃
    (Σ e : Matching ports ends,
      {k : D → Fin q // ∀ d, k d = k (facePerm next flip e.val d)}) where
  toFun
    | ⟨a,k,e⟩ =>
      let vi p := congrArg Prod.fst (e.property p)
      let first p := congrArg (fun t : V × Fin q × Fin q => t.2.1) (e.property p)
      let second p := congrArg (fun t : V × Fin q × Fin q => t.2.2) (e.property p)
      ⟨⟨e.val,vi⟩,⟨k,fun d => by
        let p := e.val.symm (flip d)
        have hd : flip (e.val p) = d := by simp [p,involution d]
        calc
          k d = k (flip (e.val p)) := congrArg k hd.symm
          _ = a (next p) := second p
          _ = k (e.val (next p)) := (first (next p)).symm
          _ = _ := rfl⟩⟩
  invFun
    | ⟨e,k⟩ => ⟨fun p => k.val (e.val p), k.val, ⟨e.val,fun p => by
        have h := k.property (flip (e.val p))
        change k.val (flip (e.val p)) = k.val (e.val (next (e.val.symm (flip (flip (e.val p)))))) at h
        rw [involution,e.val.symm_apply_apply] at h
        exact Prod.ext (e.property p) (Prod.ext rfl h)⟩⟩
  left_inv
    | ⟨a,k,⟨e,he⟩⟩ => by
      have h : (fun p => k (e p)) = a := funext fun p =>
        congrArg (fun t : V × Fin q × Fin q => t.2.1) (he p)
      subst a
      rfl
  right_inv
    | ⟨e,k⟩ => rfl

variable [Fintype V] [Fintype D]
open Classical

/-- Entrywise expansion of the product of vertex differential traces
on the product of edge traces. Every dart receives its first matrix
index independently; the second is the first at the other dart. -/
def traceEvaluation {n : Nat} (v : Fin n → V) (s : Equiv.Perm (Fin n)) : Nat :=
  ∑ a : Fin n → Fin q, eval 0 (differentiate (portIndex v s q a)
    (∑ k : D → Fin q, ∏ d, X (endIndex ends flip q k d)))

private theorem evaluate_sum {S T : Type*} [Fintype S] [Fintype T] {n : Nat}
    (f : Fin n → S) (p : T → MvPolynomial S Nat) :
    eval 0 (differentiate f (∑ t, p t)) = ∑ t, eval 0 (differentiate f (p t)) := by
  simp only [evaluate_coefficient,coeff_sum,Finset.sum_mul]

/-- The value of the formal trace differential operator on one graph
is the sum of q to the number of face cycles over vertex-preserving
bijections from numbered derivative slots to edge ends. -/
theorem traceEvaluation_faces {n : Nat} (v : Fin n → V) (s : Equiv.Perm (Fin n))
    (involution : Function.Involutive flip) :
    traceEvaluation ends flip q v s = ∑ e : Matching v ends,
      q ^ LeanPool.K5MinorFreeChoosability.cycleCount (facePerm s flip e.val) := by
  classical
  unfold traceEvaluation
  simp_rw [evaluate_sum,evaluate_product]
  calc
    _ = Nat.card (Σ a : Fin n → Fin q, Σ k : D → Fin q,
      Matching (portIndex v s q a) (endIndex ends flip q k)) := by
        simp only [Nat.card_sigma]
    _ = _ := by
      rw [Nat.card_congr (traceAssignments v ends s flip q involution),Nat.card_sigma]
      simp_rw [ArithmeticRotation.assignment_count]

end Trace

section MatrixEntry
open Classical
variable {V E : Type*} [Fintype E] (ends : E × Bool → V) (q : Nat)

def flipEnds : Equiv.Perm (E × Bool) where
  toFun d := (d.1,!d.2)
  invFun d := (d.1,!d.2)
  left_inv d := by simp
  right_inv d := by simp

def vertexMatrix (v : V) : Matrix (Fin q) (Fin q) (MvPolynomial (V × Fin q × Fin q) Nat) :=
  fun i j => X (v,i,j)

/-- Each pair of indices on an edge expands the ordinary matrix trace.
Their product is the dart-index polynomial in the differential operator. -/
theorem edgeTrace_product :
    (∏ e, Matrix.trace (vertexMatrix q (ends (e,false)) * vertexMatrix q (ends (e,true)))) =
      ∑ k : E × Bool → Fin q, ∏ d, X (R := Nat) (endIndex ends flipEnds q k d) := by
  let factors (e : E) (ij : Fin q × Fin q) : MvPolynomial (V × Fin q × Fin q) Nat :=
    X (ends (e,false),ij.1,ij.2) * X (ends (e,true),ij.2,ij.1)
  have oneEdge (e : E) : Matrix.trace (vertexMatrix q (ends (e,false)) *
      vertexMatrix q (ends (e,true))) = ∑ ij, factors e ij := by
    rw [Fintype.sum_prod_type]
    rfl
  simp_rw [oneEdge]
  rw [Fintype.prod_sum]
  let m : (E → Fin q × Fin q) ≃ (E × Bool → Fin q) := {
    toFun := fun h d => if d.2 then (h d.1).2 else (h d.1).1
    invFun := fun k e => (k (e,false),k (e,true))
    left_inv := fun _ => by funext _; simp
    right_inv := fun k => by funext ⟨e,b⟩; cases b <;> rfl }
  apply Finset.sum_equiv m (fun _ => by simp)
  intro h _
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro e _
  rw [Fintype.prod_bool,mul_comm]
  rfl

end MatrixEntry
end
end Recognition.TraceDerivative
