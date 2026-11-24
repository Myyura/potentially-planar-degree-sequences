import Combined.PlanarBounds
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Degrees on one part of a planar cut, with both Euler bounds evaluated on
the actual crossing graph and the actual induced graph. -/

namespace Combined.FixedCut

open LeanPool.K5MinorFreeChoosability
open scoped BigOperators

noncomputable def valency {V : Type} (G : SimpleGraph V) (v : V) := Nat.card {w // G.Adj v w}

theorem as_degree {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    valency G x = G.degree x := by
  rw [valency, Nat.card_eq_fintype_card]
  exact G.card_neighborSet_eq_degree x

theorem edge_count {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nat.card G.edgeSet = G.edgeFinset.card := by
  simp [SimpleGraph.edgeFinset, Nat.card_eq_fintype_card]

abbrev cross {V : Type} (G : SimpleGraph V) (S : Set V) := G.between S Sᶜ

theorem degree_split {V : Type} [Finite V] (G : SimpleGraph V) (S : Set V) (x : S) :
    valency G x.val = valency (G.induce S) x + valency (cross G S) x.val := by
  classical
  let e : {y // G.Adj x.val y} ≃
      {z : S // (G.induce S).Adj x z} ⊕ {z // (cross G S).Adj x.val z} := {
    toFun := fun y => if h : y.val ∈ S then .inl ⟨⟨y.val,h⟩,y.property⟩
      else .inr ⟨y.val, y.property, Or.inl ⟨x.property,h⟩⟩
    invFun := Sum.elim (fun y => ⟨y.val.val, y.property⟩) (fun y => ⟨y.val,y.property.1⟩)
    left_inv := fun y => by by_cases h : y.val ∈ S <;> simp [h]
    right_inv := fun z => by
      cases z with
      | inl y => simp [y.val.property]
      | inr y =>
        have hy : y.val ∉ S := by rcases y.property.2 with h | h; exact h.2; exact False.elim (h.1 x.property)
        simp [hy] }
  exact (Nat.card_congr e).trans Nat.card_sum

theorem sum_on_part {V : Type} [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    (∑ x : S, valency G x.val) =
      2 * Nat.card (G.induce (S : Set V)).edgeSet + Nat.card (cross G S).edgeSet := by
  classical
  let C := cross G (S : Set V)
  let K := G.induce (S : Set V)
  have bip : C.IsBipartiteWith (S : Set V) (↑(Sᶜ) : Set V) := by
    simpa [C,cross] using (SimpleGraph.between_isBipartiteWith (G := G) (s := (S : Set V))
      (t := (S : Set V)ᶜ) disjoint_compl_right)
  have left : (∑ x : S, C.degree x.val) = C.edgeFinset.card := by
    exact (Finset.sum_coe_sort S (fun x => C.degree x)).trans (C.isBipartiteWith_sum_degrees_eq_card_edges bip)
  simp_rw [degree_split G (S : Set V), as_degree]
  rw [Finset.sum_add_distrib]
  change (∑ x : S, K.degree x) + (∑ x : S, C.degree x.val) = 2*Nat.card K.edgeSet + Nat.card C.edgeSet
  rw [left, edge_count, edge_count]
  exact congrArg (· + C.edgeFinset.card) K.sum_degrees_eq_twice_card_edges

/-- The density of the old positions forces a lower bound on the number
of twos. Equality simultaneously saturates the two induced graph bounds. -/
theorem saturation {V : Type} [Fintype V] (G : SimpleGraph V) (flat : IsPlanar G)
    (S : Finset V) (r s b : Nat) (four : 4 ≤ S.card)
    (order : Nat.card V = S.card+b+s) (cubes : b+4=2*S.card+2*r)
    (mass : (∑ x : S, valency G x.val) + 24 = 12*S.card+6*r) :
    r ≤ s ∧ (s=r →
      Nat.card (G.induce (S : Set V)).edgeSet + 6 = 3*S.card ∧
      Nat.card (cross G S).edgeSet + 4 = 2*Nat.card V ∧
      ∀ v, 2 ≤ valency (cross G S) v) := by
  classical
  let K := G.induce (S : Set V)
  let C := cross G (S : Set V)
  let color := fun x : V => decide (x ∈ S)
  have colored (u v) (h : C.Adj u v) : color u ≠ color v := by
    rcases h.2 with h | h
    · simp [color, show u ∈ S from h.1, show v ∉ S from h.2]
    · simp [color, show u ∉ S from h.1, show v ∈ S from h.2]
  have pk := PlanarBounds.planar_subgraph G K Subtype.val Subtype.val_injective (fun _ _ h => h) flat
  have pc : IsPlanar C := PlanarBounds.planar_subgraph G C id Function.injective_id (fun _ _ h => h.1) flat
  have size : Nat.card (↑(S : Set V)) = S.card := by simp
  have capK := PlanarBounds.simple_edges pk (by omega)
  have capC := PlanarBounds.bipartite_edges pc (by omega) color colored
  have count := sum_on_part G S
  change (∑ x : S, valency G x.val) = 2*Nat.card K.edgeSet + Nat.card C.edgeSet at count
  refine ⟨by omega, ?_⟩
  intro hit
  have tight : Nat.card C.edgeSet + 4 = 2*Nat.card V := by omega
  change Nat.card K.edgeSet + 6 = 3*S.card ∧ _
  exact ⟨by omega, tight, PlanarBounds.bipartite_tight_degree pc (by omega) color colored tight⟩

/-- Flipping one old vertex in a largest planar cut cannot add crossing edges.
Thus at least half of its neighbors lie across the cut. -/
theorem max_cut_flip {V : Type} [Fintype V] (G : SimpleGraph V) (flat : IsPlanar G)
    (S : Finset V) (size : 3 ≤ Nat.card V)
    (tight : Nat.card (cross G S).edgeSet + 4 = 2*Nat.card V) (x : S) :
    2 * valency (G.induce (S : Set V)) x ≤ valency G x.val := by
  classical
  let K := G.induce (S : Set V)
  let s := S.erase x.val
  let D := K.induce ({x}ᶜ : Set S)
  let C := cross G (s : Set V)
  have iso : D ≃g G.induce (s : Set V) := {
    toFun := fun y => ⟨y.val.val,Finset.mem_erase.mpr ⟨(fun h => y.property (Subtype.ext h)),y.val.property⟩⟩
    invFun := fun y => ⟨⟨y.val,(Finset.mem_erase.mp y.property).2⟩,
      fun h => (Finset.mem_erase.mp y.property).1 (congrArg Subtype.val (Set.mem_singleton_iff.mp h))⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := Iff.rfl }
  have deletion : Nat.card (G.induce (s : Set V)).edgeSet + valency K x = Nat.card K.edgeSet := by
    rw [← Nat.card_congr iso.mapEdgeSet]
    exact (PlanarBounds.deleted_counts K x).1
  have cap : Nat.card C.edgeSet + 4 ≤ 2*Nat.card V := by
    have pc := PlanarBounds.planar_subgraph G C id Function.injective_id (fun _ _ h => h.1) flat
    apply PlanarBounds.bipartite_edges pc size (fun v => decide (v ∈ s))
    intro u v h
    rcases h.2 with h | h
    · simp [show u ∈ s from h.1, show v ∉ s from h.2]
    · simp [show u ∉ s from h.1, show v ∈ s from h.2]
  have one := sum_on_part G S
  have two := sum_on_part G s
  have mass : (∑ y : s, valency G y.val) + valency G x.val = ∑ y : S, valency G y.val := by
    rw [Finset.sum_coe_sort,Finset.sum_coe_sort]
    exact Finset.sum_erase_add _ _ x.property
  change (∑ y : S, valency G y.val) = 2*Nat.card K.edgeSet + Nat.card (cross G S).edgeSet at one
  change (∑ y : s, valency G y.val) = 2*Nat.card (G.induce (s : Set V)).edgeSet + Nat.card C.edgeSet at two
  change 2*valency K x ≤ _
  omega

end Combined.FixedCut
