import Reduction
import Connectivity
import Examples

namespace Recognition.Promise
open SparseBoundary Reduction Connectivity

/-- Three-connectivity, including the usual minimum order convention. -/
def ThreeConnectedRow (d : List Nat) : Prop :=
  4 ≤ d.length ∧ ∃ G : Graph d.length, G.Realizes d ∧ Robust (fun x y => G.adj x y = true)

private theorem getRaised (xs labels : List Nat) (i : Fin xs.length) :
    (raised xs labels)[i.val]'(by simp [raised]) =
      2*xs[i] - (labels.contains i.val).toNat := by
  simp [raised,List.getElem_zipIdx]

private theorem demand_identity (xs labels : List Nat) (lo : ∀ v ∈ xs, 1 ≤ v) :
    let d (i : Fin xs.length) := xs[i] - (labels.contains i.val).toNat
    (raised xs labels).sum = xs.sum + (List.ofFn d).sum := by
  intro d
  have eq : raised xs labels = List.ofFn (fun i : Fin xs.length => xs[i] + d i) := by
    apply List.ext_getElem
    · simp [raised]
    · intro i h _
      have hi : i < xs.length := by simpa [raised] using h
      rw [getRaised xs labels ⟨i,hi⟩,List.getElem_ofFn]
      have lo' := lo _ (List.getElem_mem hi)
      dsimp [d]
      cases labels.contains i <;> simp <;> omega
  have add (n : Nat) (f g : Fin n → Nat) :
      (List.ofFn fun i => f i + g i).sum = (List.ofFn f).sum + (List.ofFn g).sum := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.ofFn_succ,ih, Nat.add_assoc,Nat.add_left_comm]
  rw [eq,add]
  have re : List.ofFn (fun i : Fin xs.length => xs[i]) = xs := by
    apply List.ext_getElem <;> simp
  rw [re]

theorem layer_three_connected (T : Table) (q : Test) (old : TableValid T.degrees)
    (new : TableValid (layer T q).degrees) (size : 3*q.group.length ≤ T.degrees.length)
    (h : ThreeConnectedRow T.degrees) : ThreeConnectedRow (layer T q).degrees := by
  let xs := T.degrees
  let ls := selectedLabels T q
  let b := 2*xs.length-4-q.group.length
  let d (i : Fin xs.length) := xs[i] - (ls.contains i.val).toNat
  have hn : 5 ≤ xs.length := old.1
  have bound : xs.length-1 ≤ b := by dsimp [b,xs] at *; omega
  have positive : 0 < b := by omega
  have valid (i : Fin xs.length) : 3 ≤ xs[i] ∧ xs[i] < xs.length :=
    old.2.2 _ (List.getElem_mem i.isLt)
  have total : (List.ofFn d).sum = 3*b := by
    have e := demand_identity xs ls (fun v hv => Nat.le_trans (by decide) (old.2.2 v hv).1)
    have oldE : xs.sum+12 = 6*xs.length := old.2.1
    have newE := new.2.1
    change (raised xs ls ++ List.replicate b 3).sum+12 =
      6*(raised xs ls ++ List.replicate b 3).length at newE
    simp only [List.sum_append,List.sum_replicate_nat,List.length_append,List.length_replicate,
      raised,List.length_map,List.length_zipIdx] at newE
    change (raised xs ls).sum + b*3 + 12 = 6*(xs.length+b) at newE
    change (raised xs ls).sum = xs.sum + (List.ofFn d).sum at e
    omega
  obtain ⟨_,G,hrow,robust⟩ := h
  obtain ⟨H,hrob,_,hdeg,hfresh⟩ := extend_graph G robust b positive d
    (fun i => Nat.le_trans (Nat.sub_le ..) (Nat.le_trans (Nat.le_sub_one_of_lt (valid i).2) bound)) total
  have len := layer_order T q
  change (layer T q).degrees.length = xs.length+b at len
  refine ⟨by omega,?_⟩
  suffices witness : ∀ (ys : List Nat) (e : ys = (layer T q).degrees) (l : ys.length = xs.length+b),
      ∃ H : Graph ys.length, H.Realizes ys ∧ Robust (fun i j => H.adj i j = true) from
    witness _ rfl len
  intro ys eq ord
  -- Transport once across equality of the order; positions stay in the original order.
  have aux {n} (same : n=ys.length) (g : Graph n) (row : ∀ i : Fin n, g.degree i = ys[i.val]'(by omega))
      (rob : Robust (fun i j => g.adj i j = true)) :
      ∃ K : Graph ys.length, K.Realizes ys ∧ Robust (fun i j => K.adj i j = true) := by
    subst n
    exact ⟨g,row,rob⟩
  apply aux ord.symm H _ hrob
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro u
    rw [hdeg,hrow]
    subst ys
    change xs[u] + d u = (raised xs ls ++ List.replicate b 3)[u.val]'(by simp [raised]; omega)
    rw [List.getElem_append_left (by simp [raised]),getRaised xs ls u]
    have := (valid u).1
    dsimp [d]
    cases ls.contains u.val <;> simp <;> omega
  · intro j
    rw [hfresh]
    subst ys
    change 3 = (raised xs ls ++ List.replicate b 3)[xs.length+j.val]'(by simp [raised])
    rw [List.getElem_append_right (by simp [raised]),List.getElem_replicate]

theorem encoded_three_connected (I : Instance) (hv : Valid I)
    (base : ThreeConnectedRow (sourceTable I)) : ThreeConnectedRow (encode I) :=
  fold_invariant I hv (fun T => ThreeConnectedRow T.degrees) base layer_three_connected

theorem malformed_no : ¬ Planaric malformedOutput := Examples.three_universal

end Recognition.Promise
