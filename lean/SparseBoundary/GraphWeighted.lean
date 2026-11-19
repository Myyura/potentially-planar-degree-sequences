import SparseBoundary.GraphSeries
import SparseBoundary.GraphDeletion

namespace SparseBoundary.Graph

/-- An old label after prepending k degree-two vertices. -/
def oldLabel {n : Nat} : (k : Nat) → Fin n → Fin (n+k)
  | 0, i => i
  | k+1, i => (oldLabel k i).succ

@[simp] theorem oldLabel_eq {n : Nat} (k : Nat) (i j : Fin n) :
    (oldLabel k i == oldLabel k j) = (i == j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    apply Bool.eq_iff_iff.mpr
    simpa only [oldLabel,beq_iff_eq,Fin.succ_inj] using (Bool.eq_iff_iff.mp ih)

/-- Expand each additional copy of an edge as its own path of length two. -/
def expand (H : Graph n) (edges : List (Fin n × Fin n)) : Graph (n+edges.length) :=
  match edges with
  | [] => H
  | (a,b)::rest => (expand H rest).parallelPath (oldLabel rest.length a) (oldLabel rest.length b)

theorem expand_old_adj (H : Graph n) (edges : List (Fin n × Fin n)) (i j : Fin n) :
    (H.expand edges).adj (oldLabel edges.length i) (oldLabel edges.length j) = H.adj i j := by
  induction edges with
  | nil => rfl
  | cons ab E ih => simpa [expand,oldLabel,parallelPath,incident] using ih

theorem expand_planar {H : Graph n} (hp : H.Planar) {edges : List (Fin n × Fin n)}
    (valid : ∀ e ∈ edges, H.adj e.1 e.2 = true) : (H.expand edges).Planar := by
  induction edges with
  | nil => exact hp
  | cons ab E ih =>
    apply parallelPath_planar (ih (fun e he => valid e (by simp [he])))
    exact (expand_old_adj H E ab.1 ab.2).trans (valid ab (by simp))

/-- Increment on an old vertex contributed by the extra edge copies. -/
def increments (E : List (Fin n × Fin n)) (i : Fin n) : Nat :=
  E.countP (fun e => pairRow e.1 e.2 i)

theorem expand_old_degree (H : Graph n) (E : List (Fin n × Fin n)) (i : Fin n) :
    (H.expand E).degree (oldLabel E.length i) = H.degree i + increments E i := by
  induction E with
  | nil => simp [expand,increments,oldLabel]
  | cons ab E ih =>
    simp only [expand, List.length_cons,oldLabel,parallelPath_old_degree,ih,
      increments, List.countP_cons, pairRow, oldLabel_eq]
    cases (i == ab.1 || i == ab.2) <;> simp [Nat.add_assoc]

private theorem new_degree {H : Graph n} {E : List (Fin n × Fin n)}
    (valid : ∀ e ∈ E, H.adj e.1 e.2 = true) (i : Fin (n+E.length)) (hi : i.val < E.length) :
    (H.expand E).degree i = 2 := by
  induction E with
  | nil => contradiction
  | cons ab E ih =>
    refine Fin.cases ?_ (fun j => ?_) i hi
    · exact fun _ => parallelPath_new_degree ((expand_old_adj H E ab.1 ab.2).trans (valid ab (by simp)))
    · intro hj
      have hj' : j.val < E.length := by simpa using hj
      have oval (k) (x : Fin n) : (oldLabel k x).val = x.val + k := by
        induction k with
        | zero => rfl
        | succ k ik => simp [oldLabel,ik,Nat.add_assoc]
      have hna : j ≠ oldLabel E.length ab.1 := by
        intro e; have v := congrArg Fin.val e; rw [oval] at v; omega
      have hnb : j ≠ oldLabel E.length ab.2 := by
        intro e; have v := congrArg Fin.val e; rw [oval] at v; omega
      rw [expand,parallelPath_old_degree,ih (fun e he => valid e (by simp [he])) j hj']
      simp [pairRow,hna,hnb]

/-- The ordinary simple graph has exactly one degree-two vertex for each
    additional edge copy; all old degrees are their weighted degrees. -/
theorem expand_profile {H : Graph n} {E : List (Fin n × Fin n)}
    (valid : ∀ e ∈ E, H.adj e.1 e.2 = true) :
    List.ofFn (H.expand E).degree =
    List.replicate E.length 2 ++ List.ofFn (fun i => H.degree i + increments E i) := by
  apply List.ext_getElem
  · simp [Nat.add_comm]
  · intro j hj _
    simp only [List.length_ofFn] at hj
    by_cases lt : j < E.length
    · simp [List.getElem_append_left (by simpa using lt : j < (List.replicate E.length 2).length),
        new_degree valid ⟨j,hj⟩ lt]
    · let x : Fin n := ⟨j-E.length,by omega⟩
      have oval (k) : (oldLabel k x).val = x.val+k := by
        induction k with
        | zero => rfl
        | succ k ih => simp [oldLabel,ih,Nat.add_assoc]
      have e : (⟨j,hj⟩ : Fin _) = oldLabel E.length x := Fin.ext (by rw [oval]; dsimp [x]; omega)
      simp only [List.getElem_ofFn,List.getElem_append_right (by simp; omega :
        (List.replicate E.length 2).length ≤ j),List.length_replicate,e,expand_old_degree]
      rfl

theorem planaric_profile {H : Graph n} (hp : H.Planar) : Planaric (List.ofFn H.degree) := by
  apply (planaric_on_labels (n := n) List.length_ofFn).mpr
  exact ⟨H,hp,fun i => by simp⟩

/-- General loop-free weighted-support realization lemma, stated directly
    as an existential degree-sequence theorem. -/
theorem expanded_planaric {H : Graph n} (hp : H.Planar) (E : List (Fin n × Fin n))
    (valid : ∀ e ∈ E, H.adj e.1 e.2 = true) :
    Planaric (List.replicate E.length 2 ++ List.ofFn (fun i => H.degree i + increments E i)) := by
  rw [← expand_profile valid]
  exact planaric_profile (expand_planar hp valid)

end SparseBoundary.Graph
