import Triangulation.Provenance
import Triangulation.Layers
import SparseBoundary.TruncationData

namespace Recognition.StackedMinor
open Rigidity Stacking

/-- Five disjoint connected branch sets of a clique minor. The connectivity
condition says that a predicate constant along internal edges is constant
on the whole branch set. -/
structure Branches {V : Type} (M : Map V) where
  bag : Fin 5 → V → Prop
  uniform : ∀ i (p : V → Prop),
    (∀ x y, bag i x → bag i y → M.adj x y → (p x ↔ p y)) →
    ∀ x y, bag i x → bag i y → (p x ↔ p y)
  disjoint : ∀ i j, i ≠ j → ∀ x, bag i x → ¬bag j x
  linked : ∀ i j, i ≠ j → ∃ x y, bag i x ∧ bag j y ∧ M.adj x y

private theorem fifth (i p q r : Fin 5) : ∃ j : Fin 5, j ≠ i ∧ j ≠ p ∧ j ≠ q ∧ j ≠ r := by
  revert i p q r
  decide +kernel

private theorem symm {V : Type} (M : Map V) {a b : V} (h : M.adj a b) : M.adj b a := by
  obtain ⟨c,f⟩ := h
  exact ⟨c,M.flip f⟩

private theorem no_fresh_edge {V : Type} (M : Map V) (fill : Choice V) (s t : Star M fill) :
    ¬(stack M fill).adj (.inr s) (.inr t) := by
  rintro ⟨u,f⟩
  cases u <;> exact False.elim f

private theorem joint {V : Type} (M : Map V) {fill : Choice V} (s : Star M fill) {u v : V}
    (hu : s.val u) (hv : s.val v) : u=v ∨ M.adj u v := by
  obtain ⟨a,b,c,f,h⟩ := s.property.1
  rw [h] at hu hv
  have N {i j k} (p : M.face i j k) : M.adj i j := ⟨k,p⟩
  have ab := N f
  have bc := N (M.rot f)
  have ca := N (M.rot (M.rot f))
  have ba := symm M ab
  have cb := symm M bc
  have ac := symm M ca
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;> grind

private theorem anchor {V : Type} (M : Map V) (fill : Choice V) (B : Branches (stack M fill))
    (i : Fin 5) (s : Star M fill) (belongs : B.bag i (.inr s)) :
    ∃ v, s.val v ∧ B.bag i (.inl v) := by
  classical
  apply Classical.byContradiction
  intro missing
  have isolated (y : Vertex M fill) (hy : B.bag i y) : ¬(stack M fill).adj (.inr s) y := by
    cases y with
    | inl a => exact fun h => missing ⟨a,(star_neighbors M fill s a).mp h,hy⟩
    | inr t => exact no_fresh_edge M fill s t
  have singleton (v : Vertex M fill) (h : B.bag i v) : v = .inr s := by
    apply (B.uniform i (fun w => w = .inr s) _ _ v belongs h).mp rfl
    intro x y hx hy edge
    constructor
    · rintro rfl
      exact False.elim (isolated y hy edge)
    · rintro rfl
      exact False.elim (isolated x hx (symm _ edge))
  obtain ⟨a,b,c,_,key⟩ := s.property.1
  let owner (u : V) := if h : ∃ j, B.bag j (.inl u) then h.choose else i
  have own (u j) (inBag : B.bag j (.inl u)) : owner u = j := by
    have ex : ∃ j, B.bag j (.inl u) := ⟨j,inBag⟩
    by_cases same : ex.choose = j
    · simpa [owner,ex] using same
    · exact False.elim (B.disjoint _ _ same _ ex.choose_spec inBag)
  obtain ⟨j,ji,ja,jb,jc⟩ := fifth i (owner a) (owner b) (owner c)
  obtain ⟨x,y,hx,hy,edge⟩ := B.linked i j (Ne.symm ji)
  rw [singleton _ hx] at edge
  cases y with
  | inr t => exact no_fresh_edge M fill s t edge
  | inl u =>
    have hu := (star_neighbors M fill s u).mp edge
    rw [key] at hu
    have := own u j hy
    rcases hu with rfl | rfl | rfl <;> grind

/-- A clique minor of order five survives simultaneous deletion of stars.
Inside each branch set, project a star onto an incident old vertex of that
same set; adjacent projections coincide or form an old edge. -/
noncomputable def project {V : Type} (M : Map V) (fill : Choice V)
    (B : Branches (stack M fill)) : Branches M := by
  classical
  let rep (i : Fin 5) (z : Vertex M fill) (h : B.bag i z) : V :=
    match z with
    | .inl v => v
    | .inr s => (anchor M fill B i s h).choose
  have owned (i z h) : B.bag i (.inl (rep i z h)) := by
    cases z with
    | inl v => exact h
    | inr s => exact (anchor M fill B i s h).choose_spec.2
  have step (i j) (x y : Vertex M fill) (hx : B.bag i x) (hy : B.bag j y)
      (edge : (stack M fill).adj x y) : rep i x hx = rep j y hy ∨ M.adj (rep i x hx) (rep j y hy) := by
    cases x with
    | inl u =>
      cases y with
      | inl v => exact Or.inr ((old_edges M fill u v).mp edge)
      | inr s =>
        exact joint M s ((star_neighbors M fill s u).mp (symm _ edge)) (anchor M fill B j s hy).choose_spec.1
    | inr s =>
      cases y with
      | inl v => exact joint M s (anchor M fill B i s hx).choose_spec.1 ((star_neighbors M fill s v).mp edge)
      | inr t => exact False.elim (no_fresh_edge M fill s t edge)
  refine ⟨fun i v => B.bag i (.inl v),?_,fun i j ne x => B.disjoint i j ne (.inl x),?_⟩
  · intro i p localEdge a b ha hb
    let inside (z : Vertex M fill) := ∃ hz : B.bag i z, p (rep i z hz)
    have const (x y) (hx : B.bag i x) (hy : B.bag i y) (e : (stack M fill).adj x y) :
        inside x ↔ inside y := by
      have only (z) (hz : B.bag i z) : inside z ↔ p (rep i z hz) := ⟨fun ⟨_,g⟩ => g,fun g => ⟨hz,g⟩⟩
      rw [only _ hx,only _ hy]
      rcases step i i x y hx hy e with eq | link
      · rw [eq]
      · exact localEdge _ _ (owned i x hx) (owned i y hy) link
    have all := B.uniform i inside const (.inl a) (.inl b) ha hb
    exact ⟨fun h => (all.mp ⟨ha,h⟩).elim (fun _ q => q),fun h => (all.mpr ⟨hb,h⟩).elim (fun _ q => q)⟩
  · intro i j ne
    obtain ⟨x,y,hx,hy,e⟩ := B.linked i j ne
    refine ⟨rep i x hx,rep j y hy,owned _ _ hx,owned _ _ hy,?_⟩
    rcases step _ _ _ _ hx hy e with eq | edge
    · exact False.elim (B.disjoint i j ne _ (owned _ _ hx) (eq ▸ owned _ _ hy))
    · exact edge

theorem no_five {V : Type} {M : Map V} (h : StackedMap M) : ¬Nonempty (Branches M) := by
  induction h with
  | tetra =>
    rintro ⟨B⟩
    have pick (i : Fin 5) : ∃ v, B.bag i v := by
      obtain ⟨j,ne,_,_,_⟩ := fifth i i i i
      obtain ⟨x,_,hx,_,_⟩ := B.linked i j (Ne.symm ne)
      exact ⟨x,hx⟩
    let f i := (pick i).choose
    have injective (i j) (h : f i = f j) : i=j := by
      apply Classical.byContradiction
      intro ne
      exact B.disjoint i j ne (f i) (pick i).choose_spec (h ▸ (pick j).choose_spec)
    have nd : (List.ofFn f).Nodup := by
      apply List.nodup_iff_eq_of_getElem_eq.mpr
      intro i j hi hj e
      simp only [List.getElem_ofFn] at e
      exact congrArg Fin.val (injective _ _ e)
    have bound := nd.length_le_of_subset (l₂ := List.finRange 4) (fun x _ => List.mem_finRange x)
    simp at bound
  | subdivide _ fill ih => exact fun ⟨B⟩ => ih ⟨project _ fill B⟩

open SparseBoundary SparseBoundary.Graph SparseBoundary.Truncation

theorem no_clique5_minor {d : List Nat} (R : Layers.Model d) (built : StackedMap R.map)
    (G : Graph d.length) (same : ∀ i j : Fin d.length, R.edge i.val j.val ↔ G.adj i j = true)
    (bags : Fin 5 → List (Fin d.length)) : G.minorTest clique5 bags = false := by
  classical
  cases res : G.minorTest clique5 bags with
  | false => rfl
  | true =>
    apply False.elim
    apply no_five built
    have B := model_iff.mp res
    let id (v : R.V) : Fin d.length := ⟨R.label v,Layers.bound R v⟩
    let inv (j : Fin d.length) := ((R.hits j.val).mp j.isLt).choose
    have key (j : Fin d.length) : R.label (inv j) = j.val := ((R.hits j.val).mp j.isLt).choose_spec
    have ret (v : R.V) : inv (id v) = v := R.inj _ _ (key (id v))
    have get (j : Fin d.length) : id (inv j) = j := Fin.ext (key j)
    have lift (i j : Fin d.length) (h : G.adj i j = true) : R.map.adj (inv i) (inv j) := by
      obtain ⟨x,y,hx,hy,g⟩ := (same i j).mpr h
      exact R.inj x (inv i) (hx.trans (key i).symm) ▸ R.inj y (inv j) (hy.trans (key j).symm) ▸ g
    refine ⟨⟨fun i v => id v ∈ bags i,?_,fun i j ne x => B.sep i j ne (id x),?_⟩⟩
    · intro i p localEdge a b ha hb
      have H := uniform_bag (B.con i) (fun j => p (inv j)) (fun x hx y hy e =>
        localEdge (inv x) (inv y) ((get x).symm ▸ hx) ((get y).symm ▸ hy) (lift x y e)) (id a) ha (id b) hb
      simpa only [ret] using H
    · intro i j ne
      obtain ⟨x,hx,y,hy,e⟩ := B.link i j (by simp [clique5,ne])
      exact ⟨inv x,inv y,(get x).symm ▸ hx,(get y).symm ▸ hy,lift x y e⟩

end Recognition.StackedMinor
