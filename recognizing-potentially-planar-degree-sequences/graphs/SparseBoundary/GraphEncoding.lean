import SparseBoundary.Graph

namespace SparseBoundary.Graph

private def edgeTable (R : Nat → Nat → Bool) : Nat → List Bool
  | 0 => []
  | n+1 => edgeTable R n ++ (List.range n).map (fun i => R i n)

@[simp] private theorem table_length (R : Nat → Nat → Bool) (n : Nat) :
    (edgeTable R n).length = pairCount n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [edgeTable,pairCount,ih]

private theorem pairs_mono {j n : Nat} (h : j ≤ n) : pairCount j ≤ pairCount n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => simp only [pairCount]; omega

private theorem lookup_table (R : Nat → Nat → Bool) {n i j : Nat}
    (hij : i < j) (hjn : j < n) :
    (edgeTable R n)[pairCount j + i]? = some (R i j) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hj : j = n
    · subst j
      rw [edgeTable, List.getElem?_append_right (by simp)]
      simp [List.getElem?_range hij]
    · have h : j < n := by omega
      have hn := pairs_mono (show j + 1 ≤ n by omega)
      simp only [pairCount] at hn
      rw [edgeTable, List.getElem?_append_left (by simp; omega)]
      exact ih h

/-- Encode any symmetric, loop-free Boolean relation. Row j records its
    entries at the columns strictly smaller than j. -/
def ofRelation {n : Nat} (R : Fin n → Fin n → Bool) : Graph n :=
  let R' := fun i j => if hi : i < n then
                         if hj : j < n then R ⟨i,hi⟩ ⟨j,hj⟩ else false
                       else false
  ⟨(BitVec.ofBoolListLE (edgeTable R' n)).cast (table_length R' n)⟩

/-- Completeness of the packed representation for finite labelled simple graphs. -/
theorem adj_ofRelation {n : Nat} (R : Fin n → Fin n → Bool)
    (hs : ∀ i j, R i j = R j i) (hd : ∀ i, R i i = false)
    (i j : Fin n) : (ofRelation R).adj i j = R i j := by
  have hlt : ∀ (v w : Fin n), v.val < w.val → (ofRelation R).adj v w = R v w := by
    intro v w hvw
    have hv : v ≠ w := by intro e; subst w; omega
    simp only [adj, ofRelation, Nat.max_eq_right (Nat.le_of_lt hvw),
      Nat.min_eq_left (Nat.le_of_lt hvw), BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
      List.getD_eq_getElem?_getD, lookup_table _ hvw w.isLt, Option.getD_some,
      dite_eq_left v.isLt, dite_eq_left w.isLt]
    simp [bne_iff_ne.mpr hv]
  by_cases hij : i = j
  · subst j; simp [hd]
  · by_cases hlt' : i.val < j.val
    · exact hlt i j hlt'
    · rw [adj_comm, hs i j]
      apply hlt
      have hv : i.val ≠ j.val := by intro h; exact hij (Fin.ext h)
      omega

private theorem find_pair {n k : Nat} (h : k < pairCount n) :
    ∃ i j : Fin n, i.val < j.val ∧ pairCount j.val + i.val = k := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases h' : k < pairCount n
    · obtain ⟨i,j,hij,he⟩ := ih h'
      exact ⟨i.castSucc,j.castSucc,hij,he⟩
    · simp only [pairCount] at h
      exact ⟨⟨k - pairCount n,by omega⟩,Fin.last n,by change k - pairCount n < n; omega,
        by change pairCount n + (k - pairCount n) = k; omega⟩

theorem eq_of_adj {n : Nat} {G H : Graph n}
    (e : ∀ i j, G.adj i j = H.adj i j) : G = H := by
  obtain ⟨g⟩ := G
  obtain ⟨h⟩ := H
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  obtain ⟨i,j,hij,he⟩ := find_pair ht
  have hne : i ≠ j := by intro hh; subst j; omega
  simpa [adj, bne_iff_ne.mpr hne, Nat.max_eq_right (Nat.le_of_lt hij),
    Nat.min_eq_left (Nat.le_of_lt hij), he] using e i j

/-- The labelled subgraph induced by f, when f is injective. -/
def restrict {n m : Nat} (G : Graph n) (f : Fin m → Fin n) : Graph m :=
  ofRelation (fun x y => G.adj (f x) (f y))

@[simp] theorem restrict_adj {n m : Nat} (G : Graph n) (f : Fin m → Fin n)
    (x y : Fin m) : (G.restrict f).adj x y = G.adj (f x) (f y) :=
  adj_ofRelation _ (fun i j => adj_comm G (f i) (f j)) (fun i => adj_self G (f i)) x y

end SparseBoundary.Graph
