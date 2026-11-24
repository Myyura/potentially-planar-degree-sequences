import BoundaryCorollaries
import SparseBoundary.GraphSeries

/-! The actual realization predicate for the subdivision budget and its
specialization from the sparse classification to maximal-sum graphic cores. -/

namespace Combined.Budget

open SparseBoundary

/-- The prescribed core degrees, together with exactly `t` twos and `ℓ` leaves,
have a finite simple planar realization. The list order only fixes vertex labels. -/
def Feasible (h : List Nat) (ℓ t : Nat) : Prop :=
  Planaric (List.replicate t 2 ++ h ++ List.replicate ℓ 1)

/-- A least feasible budget, including its realization and optimality. -/
def IsMinimum (h : List Nat) (ℓ t : Nat) : Prop :=
  Feasible h ℓ t ∧ ∀ s, Feasible h ℓ s → t ≤ s

theorem monotone {h : List Nat} {ℓ s t : Nat} (pos : ∃ x ∈ h, 0 < x)
    (hs : Feasible h ℓ s) (st : s ≤ t) : Feasible h ℓ t := by
  obtain ⟨x, hx, hpos⟩ := pos
  have hp := planaric_add_twos hs
    ⟨x, List.mem_append_left _ (List.mem_append_right _ hx), hpos⟩ (t-s)
  have eq : List.replicate t 2 = List.replicate (t-s) 2 ++ List.replicate s 2 := by
    rw [← List.replicate_add, Nat.sub_add_cancel st]
  simpa only [Feasible, eq, List.append_assoc] using hp

theorem minimum_iff {h : List Nat} {ℓ t : Nat} (pos : ∃ x ∈ h, 0 < x)
    (ht : IsMinimum h ℓ t) (s : Nat) : Feasible h ℓ s ↔ t ≤ s :=
  ⟨ht.2 s, monotone pos ht.1⟩

theorem exists_minimum {h : List Nat} {ℓ : Nat} (hex : ∃ t, Feasible h ℓ t) :
    ∃ t, IsMinimum h ℓ t := by
  classical
  exact ⟨Nat.find hex, Nat.find_spec hex, fun _ hs => Nat.find_min' hex hs⟩

private theorem graphic_add_two {d : List Nat} (graphic : Graphic d)
    (pos : ∃ x ∈ d, 0 < x) : Graphic (2 :: d) := by
  obtain ⟨G, hd⟩ := graphic
  obtain ⟨x, hx, hpos⟩ := pos
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hx
  let a : Fin d.length := ⟨i, hi⟩
  have ha : 0 < G.degree a := by rw [hd a]; exact he ▸ hpos
  obtain ⟨b, hb⟩ := List.length_pos_iff_exists_mem.mp ha
  have hab := (List.mem_filter.mp hb).2
  exact ⟨G.subdivide a b, Fin.cases (Graph.subdivide_new_degree hab)
    (fun j => (Graph.subdivide_old_degree hab j).trans (hd j))⟩

theorem graphic_add_twos {h : List Nat} (graphic : Graphic h)
    (pos : ∃ x ∈ h, 0 < x) (t : Nat) : Graphic (List.replicate t 2 ++ h) := by
  induction t with
  | zero => simpa using graphic
  | succ t ih =>
    rw [List.replicate_succ, List.cons_append]
    obtain ⟨x, hx, hpos⟩ := pos
    exact graphic_add_two ih ⟨x, List.mem_append_right _ hx, hpos⟩

/-- For a graphic Euler-maximal core of order `p ≥ 8`, `p − 6` twos suffice. -/
theorem maximal_core_upper {h : List Nat} (graphic : Graphic h)
    (core : ∀ x ∈ h, 3 ≤ x) (eight : 8 ≤ h.length)
    (sum : h.sum + 12 = 6 * h.length) : Feasible h 0 (h.length - 6) := by
  have pos : ∃ x ∈ h, 0 < x := by
    cases h with
    | nil => simp at eight
    | cons x xs => exact ⟨x, by simp, by have := core x (by simp); omega⟩
  have one : h.count 1 = 0 := List.count_eq_zero.mpr (fun hx => by have := core 1 hx; omega)
  have hi : h.countP (fun x => decide (3 ≤ x)) = h.length := by
    rw [List.countP_eq_length_filter, List.filter_eq_self.mpr]
    intro x hx
    exact decide_eq_true (core x hx)
  simp only [Feasible, List.replicate_zero, List.append_nil]
  apply upper_eight_core
  · intro x hx
    rcases List.mem_append.mp hx with ha | hb
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp ha
      decide
    · have := core x hb
      omega
  · exact graphic_add_twos graphic pos _
  · simp [List.count_replicate, one]
    omega
  · simpa [highCount, List.countP_append, List.countP_replicate, hi] using eight

theorem maximal_core_minimum_le {h : List Nat} (graphic : Graphic h)
    (core : ∀ x ∈ h, 3 ≤ x) (eight : 8 ≤ h.length)
    (sum : h.sum + 12 = 6 * h.length) :
    ∃ t ≤ h.length - 6, IsMinimum h 0 t := by
  have hbound := maximal_core_upper graphic core eight sum
  obtain ⟨t, ht⟩ := exists_minimum ⟨_, hbound⟩
  exact ⟨t, ht.2 _ hbound, ht⟩

end Combined.Budget
