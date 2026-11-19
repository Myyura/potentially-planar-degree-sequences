import SparseBoundary.GraphWeighted

namespace SparseBoundary.Graph

/-! Integer degree increments on complete multipartite supports. A token is
one unit of required degree. Tokens in positions i and i+m of the sorted
2m-token list cannot have the same part when each part has at most m tokens. -/

private theorem color_gap {L : List Nat} (sorted : L.Pairwise (· ≤ ·))
    {m : Nat} (size : L.length = m+m) (bound : ∀ c, L.count c ≤ m)
    (i : Fin m) : L[i.val]'(by omega) ≠ L[m+i.val]'(by omega) := by
  intro equal
  let c := L[i.val]'(by omega)
  have mono (a b : Nat) (ha : a < L.length) (hb : b < L.length) (ab : a≤b) :
      L[a] ≤ L[b] := by
    by_cases e : a=b
    · subst b; exact Nat.le_refl _
    · exact sorted.rel_getElem_of_lt ha hb (by omega)
  have eqWindow : (L.drop i.val).take (m+1) = List.replicate (m+1) c := by
    apply List.ext_getElem
    · simp [size]; omega
    · intro j hj _
      simp only [List.length_take, List.length_drop] at hj
      simp only [List.getElem_take, List.getElem_drop, List.getElem_replicate]
      have h1 := mono i.val (i.val+j) (by omega) (by omega) (by omega)
      have h2 := mono (i.val+j) (m+i.val) (by omega) (by omega) (by omega)
      dsimp [c]; omega
  have sub := (List.take_sublist (m+1) (L.drop i.val)).trans (List.drop_sublist i.val L)
  have hc := sub.count_le c
  rw [eqWindow] at hc
  simp at hc
  exact (Nat.not_succ_le_self m) (Nat.le_trans hc (bound c))

private theorem increment_count (E : List (Fin n × Fin n))
    (noLoop : ∀ e ∈ E, e.1 ≠ e.2) (v : Fin n) :
    increments E v = (E.map Prod.fst).count v + (E.map Prod.snd).count v := by
  induction E with
  | nil => rfl
  | cons e es ih =>
    have he := noLoop e (by simp)
    have hj := ih (fun e' hh => noLoop e' (by simp [hh]))
    simp only [increments, List.countP_cons] at *
    simp only [List.map_cons,List.count_cons]
    rw [hj]
    by_cases ha : v=e.1
    · subst v; simp [pairRow, Ne.symm he, Nat.add_comm, Nat.add_assoc]
    · by_cases hb : v=e.2
      · subst v; simp [pairRow, he, Nat.add_assoc]
      · simp [pairRow, ha, hb, Ne.symm ha, Ne.symm hb]

/-- Given a multiset of token endpoints and a partition into colour classes,
    all endpoints can be paired across classes exactly when every class
    has size at most half the total (sufficiency). -/
theorem cross_pairing (C : Fin n → Nat) (tokens : List (Fin n)) (m : Nat)
    (len : tokens.length = m + m) (cap : ∀ c, (tokens.map C).count c ≤ m) :
    ∃ E : List (Fin n × Fin n), E.length = m ∧ (∀ e ∈ E, C e.1 ≠ C e.2) ∧
      ∀ i, increments E i = tokens.count i := by
  let le (x y : Fin n) := decide (C x ≤ C y)
  let s := tokens.mergeSort le
  have p : s.Perm tokens := List.mergeSort_perm _ _
  have sorted : (s.map C).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    simpa [s,le] using List.pairwise_mergeSort (le := le)
      (fun x y z => by simp [le]; omega) (fun x y => by simp [le]; omega) tokens
  have sl : s.length = m+m := p.length_eq.trans len
  have cl : (s.map C).length = m+m := by simp [sl]
  have sc (c) : (s.map C).count c ≤ m := by
    rw [List.perm_iff_count.mp (p.map C) c]; apply cap
  let A := s.take m
  let B := s.drop m
  have al : A.length = m := by simp [A,sl]
  have bl : B.length = m := by simp [B,sl]
  let E := A.zip B
  have el : E.length = m := by simp [E,al,bl]
  have legal : ∀ e ∈ E, C e.1 ≠ C e.2 := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem he
    have hh := color_gap sorted cl sc (⟨i,by omega⟩ : Fin m)
    simpa [E,A,B] using hh
  refine ⟨E,el,legal,fun v => ?_⟩
  have noloop (e) (h : e ∈ E) : e.1 ≠ e.2 := fun he => legal e h (congrArg C he)
  rw [increment_count _ noloop, List.map_fst_zip (by omega : A.length ≤ B.length),
    List.map_snd_zip (by omega : B.length ≤ A.length), ← List.count_append]
  exact (List.take_append_drop m s) ▸ (List.perm_iff_count.mp p v)

/-- A complete multipartite planar support realizes all balanced token
    assignments by introducing one degree-two vertex per pair. -/
theorem multipartite_planaric {G : Graph n} (hp : G.Planar) (C : Fin n → Nat)
    (cross : ∀ i j, C i ≠ C j → G.adj i j = true)
    (tokens : List (Fin n)) (m : Nat)
    (len : tokens.length = m+m) (cap : ∀ c, (tokens.map C).count c ≤ m) :
    Planaric (List.replicate m 2 ++ List.ofFn (fun i => G.degree i + tokens.count i)) := by
  obtain ⟨E,el,hl,inc⟩ := cross_pairing C tokens m len cap
  simpa only [el,inc] using expanded_planaric hp E (fun e he => cross _ _ (hl e he))

/-- Vertices with zero demand place no restrictions on the support.
    Only different colors that actually occur among the tokens need edges. -/
theorem active_multipartite_planaric {G : Graph n} (hp : G.Planar) (C : Fin n → Nat)
    (tokens : List (Fin n)) (m : Nat)
    (cross : ∀ i ∈ tokens, ∀ j ∈ tokens, C i ≠ C j → G.adj i j = true)
    (len : tokens.length = m+m) (cap : ∀ c, (tokens.map C).count c ≤ m) :
    Planaric (List.replicate m 2 ++ List.ofFn (fun i => G.degree i + tokens.count i)) := by
  obtain ⟨E, el, hl, inc⟩ := cross_pairing C tokens m len cap
  have legal (e) (he : e∈E) : G.adj e.1 e.2=true := by
    apply cross _ _ _ _ (hl e he) <;> apply List.count_pos_iff.mp <;> rw [← inc] <;>
      apply List.countP_pos_iff.mpr <;> exact ⟨e,he,by simp [pairRow]⟩
  simpa only [el,inc] using expanded_planaric hp E legal

end SparseBoundary.Graph
