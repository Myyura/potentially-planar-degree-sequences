import SparseBoundary.Graph

namespace SparseBoundary
namespace Graph
variable {n : Nat}

/-- The directed count is convenient even when the two sets coincide. -/
def neighboursIn (G : Graph n) (v : Fin n) (B : List (Fin n)) : Nat :=
  (B.filter (G.adj v)).length

def arcs (G : Graph n) (A B : List (Fin n)) : Nat :=
  (A.map (fun v => G.neighboursIn v B)).sum

private theorem add_sums (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

@[simp] theorem arcs_append_left (G : Graph n) (A B C : List (Fin n)) :
    G.arcs (A ++ B) C = G.arcs A C + G.arcs B C := by simp [arcs]

@[simp] theorem arcs_append_right (G : Graph n) (A B C : List (Fin n)) :
    G.arcs A (B ++ C) = G.arcs A B + G.arcs A C := by
  simp [arcs, neighboursIn, add_sums]

theorem arcs_symm (G : Graph n) (A B : List (Fin n)) :
    G.arcs A B = G.arcs B A := by
  suffices hs : ∀ v, G.arcs [v] B = G.arcs B [v] by
    induction A with
    | nil => simp [arcs, neighboursIn,List.map_const', List.sum_replicate_nat]
    | cons v A ih =>
      change G.arcs ([v] ++ A) B = G.arcs B ([v] ++ A)
      simp only [arcs_append_left, arcs_append_right, hs, ih]
  intro v
  induction B with
  | nil => simp [arcs, neighboursIn]
  | cons w B ih =>
    change G.arcs [v] ([w] ++ B) = G.arcs ([w] ++ B) [v]
    simp only [arcs_append_right, arcs_append_left, ih, Nat.add_right_cancel_iff]
    simp only [arcs, neighboursIn, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    cases he : G.adj v w <;> simp [← G.adj_comm v w, he]

theorem cut_balance (G : Graph n) (A B : List (Fin n))
    (parts : A ++ B = List.finRange n) :
    (A.map G.degree).sum + G.arcs B B = (B.map G.degree).sum + G.arcs A A := by
  have degSum (L : List (Fin n)) : (L.map G.degree).sum = G.arcs L (A ++ B) := by
    rw [parts]; rfl
  rw [degSum A, degSum B, arcs_append_right, arcs_append_right, G.arcs_symm B A]
  omega

theorem degrees_of_realization {d : List Nat} {G : Graph d.length} (h : G.Realizes d) :
    (List.finRange d.length).map G.degree = d := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simpa using h (⟨i,hj⟩ : Fin d.length)

theorem cut_lower_bound {high low : List Nat} {G : Graph (high ++ low).length}
    (real : G.Realizes (high ++ low)) :
    high.sum ≤ low.sum + G.arcs ((List.finRange _).take high.length)
                                ((List.finRange _).take high.length) := by
  let vs := List.finRange (high ++ low).length
  have h := G.cut_balance (vs.take high.length) (vs.drop high.length) (List.take_append_drop ..)
  have hd : vs.map G.degree = high ++ low := degrees_of_realization real
  rw [List.map_take, List.map_drop, hd] at h
  simp at h
  dsimp [vs] at h
  omega

private theorem row_cap (G : Graph n) {v : Fin n} {A : List (Fin n)} (hv : v ∈ A) :
    G.neighboursIn v A + 1 ≤ A.length := by
  have hle := List.length_filter_le (G.adj v) A
  have hne : (A.filter (G.adj v)).length ≠ A.length := by
    intro he
    have := List.length_filter_eq_length_iff.mp he v hv
    simp at this
  unfold neighboursIn; omega

private theorem full_row {v w : Fin n} (G : Graph n) {A : List (Fin n)}
    (hv : v ∈ A) (hw : w ∈ A) (hvw : v ≠ w)
    (full : A.length ≤ G.neighboursIn v A + 1) : G.adj v w = true := by
  obtain ⟨L,R,rfl⟩ := List.append_of_mem hv
  simp only [neighboursIn, List.filter_append, List.filter_cons, adj_self,
    Bool.false_eq_true, ite_false, List.length_append, List.length_cons] at full
  have hl := List.length_filter_le (G.adj v) L
  have hr := List.length_filter_le (G.adj v) R
  have hl' : (L.filter (G.adj v)).length = L.length := by omega
  have hr' : (R.filter (G.adj v)).length = R.length := by omega
  simp only [List.mem_append, List.mem_cons] at hw
  rcases hw with h|h|h
  · exact List.length_filter_eq_length_iff.mp hl' w h
  · exact False.elim (hvw h.symm)
  · exact List.length_filter_eq_length_iff.mp hr' w h

private theorem sum_cap {f g : α → Nat} (L : List α)
    (h : ∀ v ∈ L, f v ≤ g v) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

private theorem attains_cap {f g : α → Nat} (L : List α)
    (bound : ∀ v ∈ L, f v ≤ g v) (total : (L.map g).sum ≤ (L.map f).sum) :
    ∀ v ∈ L, f v = g v := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hb := bound x (by simp)
    have ht : ∀ v ∈ L, f v ≤ g v := fun y hy => bound y (by simp [hy])
    have hs := sum_cap L ht
    simp only [List.map_cons,List.sum_cons] at total
    intro y hy
    rcases List.mem_cons.mp hy with h|h
    · subst y; omega
    · exact ih ht (by omega) y h

private theorem singleton_minor {k : Nat} {required : Fin k → Fin k → Bool}
    {G : Graph n} (f : Fin k → Fin n)
    (inj : ∀ ⦃i j⦄, f i = f j → i = j)
    (edges : ∀ i j, required i j = true → G.adj (f i) (f j) = true) :
    G.minorTest required (fun i => [f i]) = true := by
  apply List.all_eq_true.mpr
  intro i _
  simp only [connected, Bool.true_and]
  apply List.all_eq_true.mpr
  intro j _
  apply Bool.and_eq_true_iff.mpr
  constructor
  · by_cases h : i = j
    · simp [h]
    · have h' : f i ≠ f j := fun he => h (inj he)
      simp [disjoint,h']
  · cases hr : required i j with
    | false => simp
    | true => simp [links,edges i j hr]

private theorem take_vertex {k n : Nat} (h : k ≤ n) (i : Fin k) :
    i.castLE h ∈ (List.finRange n).take k := by
  have hl : i.val < ((List.finRange n).take k).length := by simp; omega
  have hm := List.getElem_mem (l := (List.finRange n).take k) (n := i.val) hl
  have he : ((List.finRange n).take k)[i.val] = i.castLE h := by
    apply Fin.ext
    simp [Fin.castLE]
  rw [he] at hm
  exact hm

/-- At the upper boundary five high vertices must induce a clique,
    for every length and degree pattern of the low suffix. -/
theorem five_core_obstruction (high low : List Nat) (hk : high.length = 5)
    (budget : high.sum = low.sum + 20) : ¬ Planaric (high ++ low) := by
  rintro ⟨G,hr,hp⟩
  let A := (List.finRange (high ++ low).length).take high.length
  have hn : 5 ≤ (high ++ low).length := by simp [hk]
  have hl : A.length = 5 := by simp [A,hk]
  have hcap (v : _) (hv : v ∈ A) : G.neighboursIn v A ≤ 4 := by
    have := row_cap G hv; omega
  have hc := cut_lower_bound hr
  change high.sum ≤ low.sum + G.arcs A A at hc
  have ha : (A.map (fun _ => 4)).sum ≤ (A.map (fun v => G.neighboursIn v A)).sum := by
    have ht : (A.map (fun _ => 4)).sum = 20 := by simp [List.map_const', hl]
    rw [ht]; change 20 ≤ G.arcs A A; omega
  have hsat := attains_cap A hcap ha
  apply hp.1
  refine ⟨_,singleton_minor (G := G) (fun i : Fin 5 => i.castLE hn) (fun {_ _} he => Fin.ext (congrArg (fun (v : Fin (high ++ low).length) => v.val) he)) ?_⟩
  intro i j hij
  have hi : i.castLE hn ∈ A := by simpa [A,hk] using take_vertex hn i
  have hj : j.castLE hn ∈ A := by simpa [A,hk] using take_vertex hn j
  have hne : i ≠ j := by simpa [clique5] using hij
  exact full_row G hi hj (fun he => hne (Fin.ext (congrArg (fun (v : Fin (high ++ low).length) => v.val) he))) (by rw [hsat _ hi,hl]; decide)

private theorem prefix_labels {n k : Nat} (h : k ≤ n) :
    (List.finRange n).take k = (List.finRange k).map (Fin.castLE h) := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left h]
  · intro i _ _
    apply Fin.ext
    simp [Fin.castLE]

/-- With six core degrees, three of them equal to three, the upper
    boundary forces all nine cross edges between the two triples. -/
theorem six_core_obstruction (a b c : Nat) (low : List Nat)
    (budget : a+b+c+9 = low.sum + 24) :
    ¬ Planaric ([a,b,c,3,3,3] ++ low) := by
  let high := [a,b,c,3,3,3]
  let d := high ++ low
  rintro ⟨G,hr,hp⟩
  have hn : 6 ≤ d.length := by simp [d,high]
  let A := (List.finRange d.length).take 6
  let cap (v : Fin d.length) := if v.val < 3 then 5 else 3
  have labels : A = (List.finRange 6).map (Fin.castLE hn) := prefix_labels hn
  have hl : A.length = 6 := by rw [labels]; simp
  have hcap (v : _) (hv : v ∈ A) : G.neighboursIn v A ≤ cap v := by
    by_cases small : v.val < 3
    · have := row_cap G hv
      simp [cap,small]; omega
    · have hv' := hv
      rw [labels] at hv'
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv'
      have val : i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by
        change ¬ i.val < 3 at small
        omega
      have deg : G.degree (i.castLE hn) = 3 := by
        rw [hr]
        rcases val with hi|hi|hi <;> simp [Fin.castLE,hi]
      have bound : G.neighboursIn (i.castLE hn) A ≤ G.degree (i.castLE hn) := by
        let v := i.castLE hn
        change ((A.filter (G.adj v)).length) ≤ ((List.finRange _).filter (G.adj v)).length
        let B := (List.finRange d.length).drop 6
        have e : A ++ B = List.finRange d.length := List.take_append_drop ..
        have q := congrArg (fun L => (L.filter (G.adj v)).length) e
        simp only [List.filter_append, List.length_append] at q
        exact q ▸ Nat.le_add_right _ _
      change ¬ i.val < 3 at small
      simpa [cap, small] using (by rw [deg] at bound; exact bound : G.neighboursIn (i.castLE hn) A ≤ 3)
  have hc := cut_lower_bound (high := high) (low := low) hr
  change high.sum ≤ low.sum + G.arcs A A at hc
  have hhigh : high.sum = a+b+c+9 := by simp [high]; omega
  have hsum : (A.map cap).sum = 24 := by
    rw [labels,List.map_map]
    change ((List.finRange 6).map (fun i => if i.val < 3 then 5 else 3)).sum = 24
    decide
  have ha : (A.map cap).sum ≤ (A.map (fun v => G.neighboursIn v A)).sum := by
    rw [hsum]; change 24 ≤ G.arcs A A; omega
  have hsat := attains_cap A hcap ha
  have linksAcross (i j : Fin 6) (hs : i.val < 3) (hd : i ≠ j) :
      G.adj (i.castLE hn) (j.castLE hn) = true := by
    have hi := take_vertex hn i
    have hj := take_vertex hn j
    change i.castLE hn ∈ A at hi
    change j.castLE hn ∈ A at hj
    apply full_row G hi hj
    · intro e; exact hd (Fin.ext (congrArg (fun (v : Fin d.length) => v.val) e))
    · rw [hl,hsat _ hi]; simp [cap,Fin.castLE,hs]
  apply hp.2
  refine ⟨_,singleton_minor (G := G) (fun i : Fin 6 => i.castLE hn)
    (fun {_ _} he => Fin.ext (congrArg (fun (v : Fin d.length) => v.val) he)) ?_⟩
  intro i j hedge
  have hne : i ≠ j := by intro eq; subst j; simp [biclique33] at hedge
  by_cases hs : i.val < 3
  · exact linksAcross i j hs hne
  · have hj : j.val < 3 := by simpa [biclique33,hs] using hedge
    rw [G.adj_comm]
    exact linksAcross j i hj hne.symm
end Graph
end SparseBoundary
