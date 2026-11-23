import DiskFullerene.Connectivity

namespace DiskFullerene

/-- Compare the two ends of an edge, in either order. -/
def IsEdge (e : Dart) (a b : Nat) : Prop := e = (a,b) ∨ e = (b,a)

private theorem path_restrict {E : Nat → Nat → Prop} {gone : List Nat}
    {u v} (p : PathAvoiding E gone u v) {F : Nat → Nat → Prop}
    (ok : ∀ x y, x ∉ gone → y ∉ gone → E x y → F x y) : PathAvoiding F [] u v := by
  induction p with
  | here => exact .here (by simp)
  | step p e hc ih => exact ih.step (ok _ _ p.lastOK hc e) (by simp)

private theorem blocker {u v : Nat} (e : Dart) (simple : e.1 ≠ e.2) (apart : ¬ IsEdge e u v) :
    ∃ x, (x = e.1 ∨ x = e.2) ∧ x ≠ u ∧ x ≠ v := by
  obtain ⟨a,b⟩ := e
  simp [IsEdge] at simple apart ⊢
  grind

private theorem fresh {n : Nat} (four : 4 ≤ n) (u v t : Nat) :
    ∃ z, z<n ∧ z ≠ u ∧ z ≠ v ∧ z ≠ t := by
  apply Classical.byContradiction
  intro none
  have hits (i : Nat) (hi : i < 4) : i = u ∨ i = v ∨ i = t := by
    by_cases h : i = u ∨ i = v ∨ i = t
    · exact h
    · exact False.elim (none ⟨i,by omega,by grind⟩)
  have := hits 0 (by decide)
  have := hits 1 (by decide)
  have := hits 2 (by decide)
  have := hits 3 (by decide)
  omega

/-- Deleting any two non-loop edges preserves connectivity. The direct
route forbids one endpoint of each edge. If the endpoints to be joined
are themselves a forbidden edge, a fourth vertex allows two direct routes. -/
theorem twoEdgeConnected {M : MapData} (conn : M.ThreeConnected)
    (e f : Dart) (se : e.1 ≠ e.2) (sf : f.1 ≠ f.2)
    (u v : Nat) (hu : u < M.ord) (hv : v < M.ord) :
    PathAvoiding (fun a b => M.adj a b ∧ ¬ IsEdge e a b ∧ ¬ IsEdge f a b) [] u v := by
  let route := fun a b => M.adj a b ∧ ¬ IsEdge e a b ∧ ¬ IsEdge f a b
  have direct (a b) (ha : a<M.ord) (hb : b<M.ord) (he : ¬ IsEdge e a b)
      (hf : ¬ IsEdge f a b) : PathAvoiding route [] a b := by
    obtain ⟨x,hx,xa,xb⟩ := blocker e se he
    obtain ⟨y,hy,ya,yb⟩ := blocker f sf hf
    have walk := conn.2 [x,y] (by simp) a b ha hb (by simp; grind) (by simp; grind)
    apply path_restrict walk
    intro i j hi hj adj
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi hj
    refine ⟨adj,?_,?_⟩
    · rintro (rfl|rfl) <;> simp at hx <;> grind
    · rintro (rfl|rfl) <;> simp at hy <;> grind
  have middle (a b : Dart) (is : IsEdge a u v) :
      ∃ z, z < M.ord ∧ ¬ IsEdge a u z ∧ ¬ IsEdge a z v ∧
        ¬ IsEdge b u z ∧ ¬ IsEdge b z v := by
    let t := if b.1 = u ∨ b.1 = v then b.2 else b.1
    obtain ⟨z,hz,zu,zv,zt⟩ := fresh conn.1 u v t
    refine ⟨z,hz,?_⟩
    rcases is with rfl|rfl <;> cases b <;> simp [IsEdge] <;> dsimp [t] at zt <;> grind
  by_cases he : IsEdge e u v
  · obtain ⟨z,hz,e₁,e₂,f₁,f₂⟩ := middle e f he
    exact (direct u z hu hz e₁ f₁).trans (direct z v hz hv e₂ f₂)
  · by_cases hf : IsEdge f u v
    · obtain ⟨z,hz,f₁,f₂,e₁,e₂⟩ := middle f e hf
      exact (direct u z hu hz e₁ f₁).trans (direct z v hz hv e₂ f₂)
    · exact direct u v hu hv he hf

end DiskFullerene
