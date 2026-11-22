import TracePolynomial

/-! Label an edge by its endpoints in increasing order. A Boolean specifies
which endpoint is the tail of the corresponding dart. -/
namespace Recognition.TraceEdgeLabels
open Classical MvPolynomial TraceDerivative LeanPool.K5MinorFreeChoosability
open scoped BigOperators
noncomputable section

variable {V : Type*} [LinearOrder V] (G : SimpleGraph V)

abbrev Edge := {p : V × V // p.1 < p.2 ∧ G.Adj p.1 p.2}

/-- The increasing pair names an unoriented edge, and the bit selects its end. -/
def darts : Edge G × Bool ≃ G.Dart where
  toFun
    | ⟨e,false⟩ => ⟨e.val,e.property.2⟩
    | ⟨e,true⟩ => ⟨e.val.swap,e.property.2.symm⟩
  invFun d := if h : d.fst < d.snd then ⟨⟨d.toProd,h,d.adj⟩,false⟩ else
    ⟨⟨d.toProd.swap,lt_of_le_of_ne (le_of_not_gt h) d.adj.ne.symm,d.adj.symm⟩,true⟩
  left_inv := by
    rintro ⟨⟨⟨u,v⟩,lt,adj⟩,b⟩
    cases b <;> simp [lt,lt_asymm lt]
  right_inv := by
    rintro ⟨⟨u,v⟩,adj⟩
    by_cases h : u<v <;> simp [h]

theorem flip_is_symm (d : Edge G × Bool) : darts G (flipEnds d) = (darts G d).symm := by
  rcases d with ⟨e,b⟩
  cases b <;> rfl

/-- Reindex the ordinary edge matrix trace product by the two darts
of each edge, preserving the reversal in its matrix index pair. -/
theorem trace_product [Fintype V] (q : Nat) :
    (∏ e : Edge G, Matrix.trace (vertexMatrix q e.val.1 * vertexMatrix q e.val.2)) =
      ∑ k : G.Dart → Fin q, ∏ d, X (R := Nat)
        (endIndex (fun d : G.Dart => d.fst) (dartSymm G) q k d) := by
  classical
  let ends (d : Edge G × Bool) := (darts G d).fst
  have start := edgeTrace_product ends q
  refine start.trans ?_
  let idx := (darts G).arrowCongr (Equiv.refl (Fin q))
  apply Finset.sum_equiv idx (fun _ => by simp)
  intro k _
  apply Finset.prod_equiv (darts G) (fun _ => by simp)
  intro d _
  have first (b : Edge G × Bool) : idx k (darts G b) = k b := by simp [idx]
  simp only [endIndex,ends,dartSymm_apply,←flip_is_symm,first]

/-- The exact polynomial substituted for each labelled graph in the row
test equals the product of its ordinary edge traces. -/
theorem edgeProduct (ds : List Nat) (q : Nat) (K : SimpleGraph (Fin ds.length)) :
    (∏ e : Edge K, Matrix.trace (vertexMatrix q e.val.1 * vertexMatrix q e.val.2)) =
      TracePolynomial.edgeProduct ds q K := trace_product K q

end
end Recognition.TraceEdgeLabels
