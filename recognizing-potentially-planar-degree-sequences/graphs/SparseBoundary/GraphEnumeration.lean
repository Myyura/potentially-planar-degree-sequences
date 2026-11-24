import SparseBoundary.GraphEncoding

namespace SparseBoundary.Graph

def incident {n : Nat} (r : Fin n → Bool) (G : Graph n) :
    Fin (n+1) → Fin (n+1) → Bool :=
  Fin.cases (Fin.cases false r) (fun x => Fin.cases (r x) (G.adj x))

def adjoinRow {n : Nat} (r : Fin n → Bool) (G : Graph n) : Graph (n+1) :=
  ofRelation (incident r G)

@[simp] theorem adjoin_adj {n : Nat} (r : Fin n → Bool) (G : Graph n)
    (v w : Fin (n+1)) : (adjoinRow r G).adj v w = incident r G v w := by
  apply adj_ofRelation
  · refine Fin.cases ?_ (fun x => ?_)
    · exact Fin.cases rfl (fun _ => rfl)
    · exact Fin.cases rfl (fun y => G.adj_comm x y)
  · exact Fin.cases rfl (fun x => G.adj_self x)

private theorem recover_row {n : Nat} (G : Graph (n+1)) :
    adjoinRow (fun i => G.adj 0 i.succ) (G.restrict Fin.succ) = G := by
  apply eq_of_adj
  refine Fin.cases ?_ (fun x => ?_)
  · refine Fin.cases (by simp) (fun y => ?_)
    simp [incident]
  · refine Fin.cases ?_ (fun y => ?_)
    · simp [incident, adj_comm G x.succ 0]
    · simp [incident]

theorem degree_adjoin_zero {n : Nat} (r : Fin n → Bool) (G : Graph n) :
    (adjoinRow r G).degree 0 = ((List.finRange n).filter r).length := by
  simp only [degree,List.finRange_succ,List.filter_cons,adj_self,
    Bool.false_eq_true,ite_false,List.filter_map,List.length_map]
  rw [show ((adjoinRow r G).adj 0 ∘ Fin.succ) = r from
    funext (fun i => by simp [incident])]

theorem degree_adjoin_succ {n : Nat} (r : Fin n → Bool) (G : Graph n) (v : Fin n) :
    (adjoinRow r G).degree v.succ = G.degree v + (r v).toNat := by
  simp only [degree,List.finRange_succ,List.filter_cons,adjoin_adj,incident,
     Fin.cases_succ,Fin.cases_zero]
  have he : ((adjoinRow r G).adj v.succ ∘ Fin.succ) = G.adj v :=
    funext (fun i => by simp [incident])
  cases r v <;> simp [List.filter_map,he]

private def rows : (n : Nat) → List (Fin n → Bool)
  | 0 => [Fin.elim0]
  | n+1 => (rows n).flatMap fun f => [Fin.cases false f, Fin.cases true f]

private theorem rows_complete {n : Nat} (r : Fin n → Bool) : r ∈ rows n := by
  induction n with
  | zero =>
    have he : r = Fin.elim0 := funext (fun i => i.elim0)
    simp [rows,he]
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨fun i => r i.succ,ih _, ?_⟩
    have he : Fin.cases (r 0) (fun i => r i.succ) = r :=
      funext (Fin.cases rfl (fun _ => rfl))
    cases h : r 0 <;> rw [h] at he <;> simp [he]

/-- Enumerate graphs with assigned degrees by exposing the row incident to
    the first vertex, then solving for the degrees of the remaining labels. -/
def candidates : (n : Nat) → (Fin n → Nat) → List (Graph n)
  | 0, _ => [⟨0⟩]
  | n+1, d =>
    (rows n).flatMap fun r =>
      if ((List.finRange n).filter r).length = d 0 &&
          (List.finRange n).all (fun i => (r i).toNat ≤ d i.succ) then
        (candidates n (fun i => d i.succ - (r i).toNat)).map (adjoinRow r)
      else []

theorem candidates_complete {n : Nat} (G : Graph n) (d : Fin n → Nat)
    (h : ∀ i, G.degree i = d i) : G ∈ candidates n d := by
  induction n with
  | zero =>
    have he : G = ⟨0⟩ := eq_of_adj (fun i => i.elim0)
    simp [candidates,he]
  | succ n ih =>
    let r (i : Fin n) := G.adj 0 i.succ
    let H := G.restrict Fin.succ
    have e : adjoinRow r H = G := recover_row G
    have h0 := degree_adjoin_zero r H
    rw [e,h 0] at h0
    have hs (v : Fin n) : d v.succ = H.degree v + (r v).toNat := by
      simpa only [e,h] using degree_adjoin_succ r H v
    apply List.mem_flatMap.mpr
    refine ⟨r,rows_complete r, ?_⟩
    have ha : (List.finRange n).all (fun i => decide ((r i).toNat ≤ d i.succ)) := by
      apply List.all_eq_true.mpr
      intro x _
      simp [hs x]
    simp only [h0.symm,decide_true,Bool.true_and,ha,ite_true,List.mem_map]
    exact ⟨H,ih H _ (fun i => by rw [hs i]; omega),e⟩

end SparseBoundary.Graph
