import SparseBoundary.GraphEncoding

namespace SparseBoundary.Graph

/-- Maps of a branch set may collapse an edge. Repetitions can then be
    erased while retaining a connected ordering of the image. -/
theorem connected_image {G : Graph n} {H : Graph m} (f : Fin n → Fin m)
    (hom : ∀ x y, G.adj x y = true → f x = f y ∨ H.adj (f x) (f y) = true)
    (s : List (Fin n)) (hc : G.connected s = true) :
    ∃ t, H.connected t = true ∧ ∀ z, z ∈ t ↔ z ∈ s.map f := by
  match s with
  | [] => simp [connected] at hc
  | [x] => exact ⟨[f x],rfl,fun _ => Iff.rfl⟩
  | x::y::ys =>
    obtain ⟨ha,ht⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨w,hw,he⟩ := List.any_eq_true.mp ha
    obtain ⟨t,hcon,hm⟩ := connected_image f hom (y::ys) ht
    have hw' := (hm (f w)).mpr (List.mem_map.mpr ⟨w,hw,rfl⟩)
    by_cases hx : f x ∈ t
    · refine ⟨t,hcon,?_⟩
      intro z
      simp only [List.map_cons, List.mem_cons]
      constructor
      · intro hz; exact Or.inr (by simpa using (hm z).mp hz)
      · rintro (rfl|hz)
        · exact hx
        · exact (hm z).mpr (by simpa using hz)
    · rcases hom x w he with h|h
      · exact (hx (h ▸ hw')).elim
      · refine ⟨f x :: t,?_,?_⟩
        · cases t with
          | nil => simp at hw'
          | cons u us =>
            exact Bool.and_eq_true_iff.mpr ⟨List.any_eq_true.mpr ⟨f w,hw',h⟩,hcon⟩
        · intro z
          rw [List.map_cons,List.mem_cons,List.mem_cons,hm]

private theorem disjoint_iff {s t : List (Fin n)} :
    disjoint s t = true ↔ ∀ x ∈ s, x ∉ t := by simp [disjoint,List.all_eq_true]

private theorem links_iff {G : Graph n} {s t : List (Fin n)} :
    links G s t = true ↔ ∃ x ∈ s, ∃ y ∈ t, G.adj x y = true := by simp [links,List.any_eq_true]

private theorem minor_iff {G : Graph n} {R : Fin k → Fin k → Bool} {s} :
    minorTest G R s = true ↔
    (∀ i, G.connected (s i) = true) ∧
    (∀ i j, i ≠ j → disjoint (s i) (s j) = true) ∧
    (∀ i j, R i j = true → links G (s i) (s j) = true) := by
  simp only [minorTest,List.all_eq_true,List.mem_finRange,true_implies,Bool.and_eq_true,
    Bool.or_eq_true,beq_iff_eq,Bool.not_eq_true',Bool.eq_false_iff]
  grind

/-- A weak graph homomorphism transfers any minor model on whose distinct
    bags it does not identify vertices. -/
theorem transfer_minor {G : Graph n} {H : Graph m} {R : Fin k → Fin k → Bool}
    (irrefl : ∀ i, R i i = false)
    (s : Fin k → List (Fin n)) (model : G.minorTest R s = true)
    (f : Fin n → Fin m)
    (hom : ∀ x y, G.adj x y = true → f x = f y ∨ H.adj (f x) (f y) = true)
    (separate : ∀ i j, i ≠ j → ∀ x ∈ s i, ∀ y ∈ s j, f x ≠ f y) :
    ∃ bags, H.minorTest R bags = true := by
  classical
  obtain ⟨hc,_,hl⟩ := minor_iff.mp model
  let T i := connected_image f hom (s i) (hc i)
  let b i := Classical.choose (T i)
  have spec i := Classical.choose_spec (T i)
  refine ⟨b, minor_iff.mpr ⟨fun i => (spec i).1,?_,?_⟩⟩
  · intro i j hij
    apply disjoint_iff.mpr
    intro z hi hj
    obtain ⟨x,hx,ex⟩ := List.mem_map.mp (((spec i).2 z).mp hi)
    obtain ⟨y,hy,ey⟩ := List.mem_map.mp (((spec j).2 z).mp hj)
    exact separate i j hij x hx y hy (ex.trans ey.symm)
  · intro i j hr
    have hij : i ≠ j := by intro h; subst j; rw [irrefl] at hr; contradiction
    obtain ⟨x,hx,y,hy,he⟩ := links_iff.mp (hl i j hr)
    rcases hom x y he with h|h
    · exact (separate i j hij x hx y hy h).elim
    · exact links_iff.mpr ⟨f x, ((spec i).2 _).mpr (List.mem_map.mpr ⟨x,hx,rfl⟩),
        f y, ((spec j).2 _).mpr (List.mem_map.mpr ⟨y,hy,rfl⟩), h⟩

private theorem leaf_member {G : Graph n} {z r : Fin n}
    (only : ∀ w, G.adj z w = true → w = r) (h : G.connected s = true)
    (hz : z ∈ s) : r ∈ s ∨ ∀ w ∈ s, w = z := by
  match s with
  | [] => simp at hz
  | [x] => simp_all
  | x::y::ys =>
    obtain ⟨ha,ht⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨w,hw,edge⟩ := List.any_eq_true.mp ha
    rcases List.mem_cons.mp hz with e|hz'
    · subst x
      exact Or.inl (List.mem_cons_of_mem _ ((only w edge) ▸ hw))
    · rcases leaf_member only ht hz' with hr|hh
      · exact Or.inl (List.mem_cons_of_mem _ hr)
      · have e := hh w hw
        subst w
        rw [G.adj_comm] at edge
        exact Or.inl (List.mem_cons.mpr (Or.inl (only x edge).symm))

private theorem minor_parent {G : Graph n} {z r : Fin n}
    (only : ∀ w, G.adj z w = true → w = r)
    {R : Fin k → Fin k → Bool} {bags} (model : G.minorTest R bags = true)
    (two : ∀ i, ∃ j k, j ≠ k ∧ R i j = true ∧ R i k = true) :
    ∀ i, z ∈ bags i → r ∈ bags i := by
  obtain ⟨hc,hd,hl⟩ := minor_iff.mp model
  intro i hi
  rcases leaf_member only (hc i) hi with h|h
  · exact h
  · obtain ⟨j,k,hjk,hij,hik⟩ := two i
    have parent {j} (e : R i j = true) : r ∈ bags j := by
      obtain ⟨x,hx,y,hy,he⟩ := links_iff.mp (hl i j e)
      rw [h x hx] at he
      exact (only y he) ▸ hy
    exact False.elim (disjoint_iff.mp (hd j k hjk) r (parent hij) (parent hik))

/-- Add one new vertex adjacent only to a chosen old vertex. Old labels are
    shifted by one. -/
def withLeaf {n : Nat} (H : Graph n) (r : Fin n) : Graph (n+1) :=
  ofRelation (fun x y => Fin.cases (Fin.cases false (fun b => b == r) y)
    (fun a => Fin.cases (a == r) (H.adj a) y) x)

private theorem leaf_edges (H : Graph n) (r : Fin n) (x y : Fin (n+1)) :
    (H.withLeaf r).adj x y =
    Fin.cases (Fin.cases false (fun b => b == r) y)
      (fun a => Fin.cases (a == r) (H.adj a) y) x := by
  apply adj_ofRelation
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;>
      simp [Fin.cases,H.adj_comm]
  · intro i; refine Fin.cases ?_ (fun a => ?_) i <;> simp

theorem withLeaf_planar {H : Graph n} (hp : H.Planar) (r : Fin n) : (H.withLeaf r).Planar := by
  let G := H.withLeaf r
  let f : Fin (n+1) → Fin n := Fin.cases r (fun i : Fin n => i)
  have only (w : Fin (n+1)) : G.adj 0 w = true → w = r.succ := by
    refine Fin.cases ?_ (fun w => ?_) w
    · simp [G]
    · simp [G,leaf_edges]
  have pull {k : Nat} {R : Fin k → Fin k → Bool} (irr : ∀ i,R i i = false)
      (two : ∀ i,∃ j k,j ≠ k ∧ R i j = true ∧ R i k = true)
      (s) (hs : G.minorTest R s = true) : ∃ b,H.minorTest R b = true := by
    have parent := minor_parent only hs two
    have hd := (minor_iff.mp hs).2.1
    apply transfer_minor irr s hs f
    · intro x y
      refine Fin.cases ?_ (fun a => ?_) x <;> refine Fin.cases ?_ (fun b => ?_) y <;>
        simp [f,G,leaf_edges] <;> grind
    · intro i j hij x hx y hy he
      have hdis := disjoint_iff.mp (hd i j hij)
      have keep (x : Fin (n+1)) (u : Fin k) : x ∈ s u → (f x).succ ∈ s u := by
        refine Fin.cases ?_ (fun a h => ?_) x
        · exact parent u
        · exact h
      exact hdis _ (keep x i hx) (he ▸ keep y j hy)
  constructor
  · rintro ⟨s,hs⟩
    exact hp.1 (pull (by decide) (by decide) s hs)
  · rintro ⟨s,hs⟩
    exact hp.2 (pull (by decide) (by decide) s hs)


@[simp] theorem withLeaf_new_degree (H : Graph n) (r : Fin n) : (H.withLeaf r).degree 0 = 1 := by
  simp [degree,List.finRange_succ,List.filter_map,Function.comp_def,leaf_edges]
  rw [← List.count_eq_length_filter]
  exact (List.nodup_finRange n).count_of_mem (List.mem_finRange r)

theorem withLeaf_old_degree (H : Graph n) (r i : Fin n) :
    (H.withLeaf r).degree i.succ = H.degree i + (if i = r then 1 else 0) := by
  simp only [degree,List.finRange_succ,List.filter_map,List.filter_cons]
  have e : ((H.withLeaf r).adj i.succ ∘ Fin.succ) = H.adj i := by
    funext j; simp [leaf_edges]
  rw [e]
  by_cases h : i=r <;> simp [h,leaf_edges,Nat.add_comm]

end SparseBoundary.Graph

namespace SparseBoundary

private theorem of_indexed {d : List Nat} {n : Nat} (hn : d.length = n)
    (h : ∃ G : Graph n, G.Planar ∧ ∀ i : Fin n, G.degree i = d[i.val]'(by omega)) :
    Planaric d := by
  subst n
  obtain ⟨G,hp,hd⟩ := h
  exact ⟨G,hd,hp⟩

/-- Attach a leaf to any chosen entry of an existing planaric profile.
    The output labels the new leaf first. -/
theorem planaric_attach_leaf {d : List Nat} (hp : Planaric d) (r : Fin d.length) :
    Planaric (1 :: List.ofFn (fun i : Fin d.length => d[i] + (if i = r then 1 else 0))) := by
  obtain ⟨G,hd,hp⟩ := hp
  let L := List.ofFn (fun i : Fin d.length => d[i] + (if i = r then 1 else 0))
  have hn : (1::L).length = d.length+1 := by simp [L]
  apply of_indexed (d := 1::L) hn
  refine ⟨G.withLeaf r,Graph.withLeaf_planar hp r,?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [L,Graph.withLeaf_old_degree]
    exact hd j

end SparseBoundary

