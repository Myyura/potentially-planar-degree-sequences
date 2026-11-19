import SparseBoundary.LeafLift

namespace SparseBoundary.Graph

private theorem neighbor_in_bag {G : Graph n} {z : Fin n} {s : List (Fin n)}
    (hc : G.connected s = true) (hz : z ∈ s) :
    (∃ w ∈ s, G.adj z w = true) ∨ ∀ w ∈ s, w = z := by
  match s with
  | [] => simp at hz
  | [x] => simp_all
  | x::y::ys =>
    obtain ⟨ha,ht⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨w,hw,edge⟩ := List.any_eq_true.mp ha
    rcases List.mem_cons.mp hz with e|hz'
    · subst x
      exact Or.inl ⟨w,List.mem_cons_of_mem _ hw,edge⟩
    · rcases neighbor_in_bag ht hz' with ⟨u,hu,he⟩|hh
      · exact Or.inl ⟨u,List.mem_cons_of_mem _ hu,he⟩
      · have e := hh w hw
        subst w
        exact Or.inl ⟨x,by simp,(G.adj_comm _ _).trans edge⟩

theorem bag_data {G : Graph n} {R : Fin k → Fin k → Bool} {s}
    (hm : minorTest G R s = true) :
    (∀ i, G.connected (s i) = true) ∧
    (∀ i j, i ≠ j → ∀ x ∈ s i, x ∉ s j) ∧
    (∀ i j, R i j = true → ∃ x ∈ s i, ∃ y ∈ s j, G.adj x y = true) := by
  simp only [minorTest,List.all_eq_true,List.mem_finRange,true_implies,Bool.and_eq_true,
    Bool.or_eq_true,beq_iff_eq,Bool.not_eq_true',Bool.eq_false_iff] at hm
  have hd {i j} (e : i ≠ j) : disjoint (s i) (s j) :=
    ((hm i).2 j).1.resolve_left e
  have hl {i j} (h : R i j = true) : links G (s i) (s j) :=
    ((hm i).2 j).2.resolve_left (by simp [h])
  refine ⟨fun i => (hm i).1, fun i j e => ?_, fun i j h => ?_⟩
  · simpa [disjoint,List.all_eq_true] using hd e
  · simpa [links,List.any_eq_true] using hl h

private theorem anchor_in_bag {G : Graph (n+1)} {a b : Fin n}
    (only : ∀ w, G.adj 0 w = true → w = a.succ ∨ w = b.succ)
    {R : Fin k → Fin k → Bool} {s} (hm : G.minorTest R s = true)
    (three : ∀ i, ∃ j p q, j ≠ p ∧ j ≠ q ∧ p ≠ q ∧
      R i j = true ∧ R i p = true ∧ R i q = true) :
    ∃ t : Fin n, (t = a ∨ t = b) ∧ ∀ i, 0 ∈ s i → t.succ ∈ s i := by
  classical
  obtain ⟨hc,hd,hl⟩ := bag_data hm
  have localChoice (i) (hi : 0 ∈ s i) : a.succ ∈ s i ∨ b.succ ∈ s i := by
    rcases neighbor_in_bag (hc i) hi with ⟨w, hw, he⟩ | hs
    · rcases only w he with ha|hb
      · exact Or.inl (ha ▸ hw)
      · exact Or.inr (hb ▸ hw)
    · have meeting {j} (e : R i j = true) : a.succ ∈ s j ∨ b.succ ∈ s j := by
        obtain ⟨x,hx,y,hy,edge⟩ := hl i j e
        rw [hs x hx] at edge
        rcases only y edge with h|h
        · exact Or.inl (h ▸ hy)
        · exact Or.inr (h ▸ hy)
      obtain ⟨j,p,q,hjp,hjq,hpq,ej,ep,eq⟩ := three i
      have h₁ := hd j p hjp
      have h₂ := hd j q hjq
      have h₃ := hd p q hpq
      rcases meeting ej with ha|hb <;> rcases meeting ep with ha'|hb' <;>
        rcases meeting eq with ha''|hb'' <;> grind
  by_cases found : ∃ i, 0 ∈ s i ∧ a.succ ∈ s i
  · obtain ⟨j,hj,ha⟩ := found
    refine ⟨a,Or.inl rfl,fun i hi => ?_⟩
    by_cases e : i=j
    · exact e ▸ ha
    · exact False.elim (hd i j e 0 hi hj)
  · exact ⟨b,Or.inr rfl,fun i hi => (localChoice i hi).resolve_left (fun ha => found ⟨i,hi,ha⟩)⟩

/-- Add a vertex whose only possible neighbours are the ends of an existing
    edge, allowing old edges to be dropped. Includes both subdivision of
    that edge and insertion of a parallel two-edge path. -/
theorem degree_two_extension {H : Graph n} {G : Graph (n+1)} (hp : H.Planar)
    (a b : Fin n) (he : H.adj a b = true)
    (old : ∀ x y : Fin n, G.adj x.succ y.succ = true → H.adj x y = true)
    (only : ∀ w, G.adj 0 w = true → w = a.succ ∨ w = b.succ) : G.Planar := by
  have pull {k : Nat} {R : Fin k → Fin k → Bool} (irr : ∀ i,R i i = false)
      (three : ∀ i, ∃ j p q, j ≠ p ∧ j ≠ q ∧ p ≠ q ∧
         R i j = true ∧ R i p = true ∧ R i q = true)
      (s) (hs : G.minorTest R s = true) : ∃ bags,H.minorTest R bags = true := by
    obtain ⟨t,ht,inside⟩ := anchor_in_bag only hs three
    have hd := (bag_data hs).2.1
    let f : Fin (n+1) → Fin n := Fin.cases t id
    have neighbor (w : Fin n) (e : G.adj 0 w.succ = true) : t = w ∨ H.adj t w = true := by
      rcases only w.succ e with h|h <;> simp only [Fin.succ_inj] at h <;>
        subst w <;> rcases ht with ht|ht <;> subst t <;> simp_all [H.adj_comm]
    apply transfer_minor irr s hs f
    · intro x y
      refine Fin.cases ?_ (fun i => ?_) x <;> refine Fin.cases ?_ (fun j => ?_) y
      · exact fun _ => Or.inl rfl
      · exact neighbor j
      · intro e
        rcases neighbor i ((G.adj_comm _ _).trans e) with h|h
        · exact Or.inl h.symm
        · exact Or.inr ((H.adj_comm _ _).trans h)
      · exact fun e => Or.inr (old i j e)
    · intro i j hij x hx y hy eq
      have keep (z : Fin (n+1)) (u) : z ∈ s u → (f z).succ ∈ s u :=
        Fin.cases (inside u) (fun _ h => h) z
      exact hd i j hij _ (keep x i hx) (eq ▸ keep y j hy)
  constructor
  · rintro ⟨s,hs⟩
    exact hp.1 (pull (by decide) (by decide) s hs)
  · rintro ⟨s,hs⟩
    exact hp.2 (pull (by decide) (by decide) s hs)

end SparseBoundary.Graph
