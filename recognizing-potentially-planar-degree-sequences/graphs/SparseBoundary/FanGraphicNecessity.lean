import SparseBoundary.FanGraphic
import SparseBoundary.Cut

namespace SparseBoundary.ErdosGallai

private theorem arcs_even {n} (G : Graph n) (A : List (Fin n)) :
    (G.arcs A A)%2=0 := by
  induction A with
  | nil => simp [Graph.arcs]
  | cons v A ih =>
    change (G.arcs ([v]++A) ([v]++A))%2=0
    simp only [Graph.arcs_append_left,Graph.arcs_append_right,G.arcs_symm A [v]]
    have hh : G.arcs [v] [v]=0 := by simp [Graph.arcs,Graph.neighboursIn]
    omega

private theorem map_sum_le (xs : List α) (f g : α → Nat)
    (h : ∀ v ∈ xs, f v ≤ g v) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons v xs ih =>
    exact Nat.add_le_add (h v (by simp)) (ih (fun w hw => h w (by simp [hw])))

private theorem arc_bound {n} (G : Graph n) (A : List (Fin n)) :
    G.arcs A A ≤ A.length * (A.length-1) := by
  have hh : ∀ v ∈ A, G.neighboursIn v A ≤ A.length-1 := by
    intro v hv
    apply Nat.le_pred_of_lt
    apply Nat.lt_of_le_of_ne (List.length_filter_le _ _)
    intro eq
    have := List.length_filter_eq_length_iff.mp eq v hv
    simp at this
  have hi := map_sum_le A (fun v => G.neighboursIn v A) (fun _ => A.length-1) hh
  simpa [Graph.arcs,List.map_const',List.sum_replicate_nat] using hi

/-- Necessity of every Erdős–Gallai inequality for an actual labelled graph
realization. No assumption is needed about the ordering for this direction. -/
theorem eg_of_graphic {d : List Nat} (hd : Graphic d) : EG d := by
  obtain ⟨G,real⟩ := hd
  let vs := List.finRange d.length
  have hd' : vs.map G.degree = d := Graph.degrees_of_realization real
  constructor
  · have hi := arcs_even G vs
    change ((vs.map G.degree).sum)%2=0 at hi
    rwa [hd'] at hi
  intro j hj
  let A := vs.take j
  let B := vs.drop j
  have hj' : A.length=j := by simp [A,vs,Nat.min_eq_left hj]
  have hparts : A++B=vs := List.take_append_drop _ _
  have hs : (d.take j).sum = G.arcs A A+G.arcs B A := by
    have h : (d.take j).sum=G.arcs A vs := by
      conv => lhs; rw [← hd',← List.map_take]
      rfl
    rw [h,← hparts,Graph.arcs_append_right,G.arcs_symm A B]
  have hb : G.arcs B A ≤ ((d.drop j).map (min j)).sum := by
    have hcap (v : Fin d.length) : G.neighboursIn v A ≤ min j (G.degree v) := by
      have hrow := List.length_filter_le (G.adj v) A
      have hfull : G.degree v = G.neighboursIn v A + G.neighboursIn v B := by
        change (vs.filter _).length = _
        rw [← hparts]; simp [Graph.neighboursIn]
      change (A.filter _).length ≤ _ at hrow ⊢
      change G.degree v=(A.filter _).length+_ at hfull
      omega
    have hh := map_sum_le B (fun v => G.neighboursIn v A) (fun v => min j (G.degree v))
      (fun v _ => hcap v)
    conv => rhs; rw [← hd',← List.map_drop,List.map_map]
    exact hh
  have hh := arc_bound G A
  rw [hj'] at hh
  omega

end SparseBoundary.ErdosGallai
