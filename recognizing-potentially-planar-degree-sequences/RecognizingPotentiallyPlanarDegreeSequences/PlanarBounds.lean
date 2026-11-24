import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar
import LeanPool.K5MinorFreeChoosability.Planar.Examples
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! Sharp Euler edge bounds, including graphs with leaves, isolated vertices and
multiple components. Vertices, edges and embeddings are the actual finite graph data. -/

namespace RecognizingPotentiallyPlanarDegreeSequences.PlanarBounds

open LeanPool.K5MinorFreeChoosability Equiv.Perm

theorem planar_subgraph [Finite V] (G : SimpleGraph V) (H : SimpleGraph W)
    (f : W → V) (inj : Function.Injective f)
    (sub : ∀ u v, H.Adj u v → G.Adj (f u) (f v)) (flat : IsPlanar G) : IsPlanar H := by
  classical
  apply isPlanar_of_minorModel flat
  refine ⟨fun w => {f w}, fun _ => Finset.singleton_nonempty _, ?_, ?_, ?_⟩
  · intro w
    rw [← connSet_iff_induce_connected]
    simpa using connSet_singleton G (f w)
  · intro a b ne
    simpa using inj.ne ne
  · exact fun a b h => ⟨f a, by simp, f b, by simp, sub a b h⟩

private theorem as_finset {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nat.card G.edgeSet = G.edgeFinset.card := by
  simp [SimpleGraph.edgeFinset, Nat.card_eq_fintype_card]

/-- Removing one vertex deletes exactly its incident edges. -/
theorem deleted_counts {V : Type} [Fintype V] (G : SimpleGraph V) (x : V) :
    let J := G.induce ({x}ᶜ : Set V)
    Nat.card J.edgeSet + Nat.card {y // G.Adj x y} = Nat.card G.edgeSet ∧
      Nat.card ({x}ᶜ : Set V) + 1 = Nat.card V := by
  classical
  dsimp only
  have stat := G.card_edgeFinset_induce_compl_singleton x
  rw [G.card_edgeFinset_deleteIncidenceSet] at stat
  have deg : G.degree x = Nat.card {y // G.Adj x y} := by
    rw [Nat.card_eq_fintype_card]; exact (G.card_neighborSet_eq_degree x).symm
  constructor
  · rw [as_finset, as_finset, ← deg, stat, Nat.sub_add_cancel (G.degree_le_card_edgeFinset x)]
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_compl_set, @Fintype.card_unique ({x} : Set V)]
    have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
    omega

/-- The two Euler bounds proved together. The coloring argument is needed only
for the bound on a bipartite graph. -/
private theorem edge_bounds (n : Nat) : ∀ (V : Type) [Finite V] (G : SimpleGraph V),
    Nat.card V = n → 3 ≤ n → IsPlanar G →
    Nat.card G.edgeSet + 6 ≤ 3 * n ∧
    ∀ (side : V → Bool), (∀ u v, G.Adj u v → side u ≠ side v) →
      Nat.card G.edgeSet + 4 ≤ 2 * n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro V _ G size three planar
    classical
    let _ := Fintype.ofFinite V
    by_cases large : ∀ x : V, 2 ≤ Nat.card {y // G.Adj x y}
    · obtain ⟨M⟩ := planar
      have nv : Nonempty V := Nat.card_pos_iff.mp (by omega) |>.1
      let x := nv.some
      have nn : Nonempty {y // G.Adj x y} := (Nat.card_pos_iff.mp (by have := large x; omega)).1
      have : Nonempty G.Dart := ⟨⟨(x, nn.some.val), nn.some.property⟩⟩
      have comp := one_le_numComponents M.rot (dartSymm G)
      have darts := card_dart_eq_two_mul G
      rw [← card_edgeSet_eq_cycleCount] at darts
      have euler := M.euler
      have vert : cycleCount M.rot ≤ Nat.card V := by
        rw [cycleCount_eq_card_nonisolated M.isRotationSystem]
        exact Nat.card_le_card_of_injective _ Subtype.val_injective
      constructor
      · have faces : 3 * M.numFaces ≤ Nat.card G.Dart := mul_numClasses_le
          (SameCycle.setoid M.facePerm) 3 (three_le_card_face M.isRotationSystem large)
        omega
      · intro side cuts
        have faces : 4 * M.numFaces ≤ Nat.card G.Dart := mul_numClasses_le
          (SameCycle.setoid M.facePerm) 4 (four_le_card_face M.isRotationSystem large side cuts)
        omega
    · obtain ⟨x, small⟩ := Classical.not_forall.mp large
      let s := ({x}ᶜ : Set V)
      let J := G.induce s
      obtain ⟨edges, vertices⟩ := deleted_counts G x
      change Nat.card J.edgeSet + Nat.card {y // G.Adj x y} = Nat.card G.edgeSet at edges
      change Nat.card s + 1 = Nat.card V at vertices
      by_cases tiny : Nat.card s = 2
      · have pairs := J.card_edgeFinset_le_card_choose_two
        rw [← Nat.card_eq_fintype_card, tiny, ← as_finset] at pairs
        change Nat.card J.edgeSet ≤ 1 at pairs
        exact ⟨by omega, fun _ _ => by omega⟩
      · have sub := planar_subgraph G J Subtype.val Subtype.val_injective (fun _ _ h => h) planar
        obtain ⟨simple, bip⟩ := ih (Nat.card s) (by omega) s J rfl (by omega) sub
        exact ⟨by omega, fun side cuts => by
          have b := bip (side ∘ Subtype.val) (fun u v h => cuts u v h)
          omega⟩

theorem simple_edges {V : Type} [Finite V] {G : SimpleGraph V} (flat : IsPlanar G)
    (size : 3 ≤ Nat.card V) : Nat.card G.edgeSet + 6 ≤ 3 * Nat.card V :=
  (edge_bounds _ V G rfl size flat).1

theorem bipartite_edges {V : Type} [Finite V] {G : SimpleGraph V} (flat : IsPlanar G)
    (size : 3 ≤ Nat.card V) (side : V → Bool)
    (cuts : ∀ u v, G.Adj u v → side u ≠ side v) :
    Nat.card G.edgeSet + 4 ≤ 2 * Nat.card V :=
  (edge_bounds _ V G rfl size flat).2 side cuts

theorem simple_tight_degree {V : Type} [Finite V] {G : SimpleGraph V}
    (flat : IsPlanar G) (size : 4 ≤ Nat.card V)
    (tight : Nat.card G.edgeSet + 6 = 3 * Nat.card V) (x : V) :
    3 ≤ Nat.card {y // G.Adj x y} := by
  classical
  let _ := Fintype.ofFinite V
  let s := ({x}ᶜ : Set V)
  let J := G.induce s
  obtain ⟨edges, vertices⟩ := deleted_counts G x
  change Nat.card J.edgeSet + Nat.card {y // G.Adj x y} = Nat.card G.edgeSet at edges
  change Nat.card s + 1 = Nat.card V at vertices
  have flatJ := planar_subgraph G J Subtype.val Subtype.val_injective (fun _ _ h => h) flat
  have b := simple_edges flatJ (by omega)
  omega

theorem bipartite_tight_degree {V : Type} [Finite V] {G : SimpleGraph V}
    (flat : IsPlanar G) (size : 4 ≤ Nat.card V) (side : V → Bool)
    (cuts : ∀ u v, G.Adj u v → side u ≠ side v)
    (tight : Nat.card G.edgeSet + 4 = 2 * Nat.card V) (x : V) :
    2 ≤ Nat.card {y // G.Adj x y} := by
  classical
  let _ := Fintype.ofFinite V
  let s := ({x}ᶜ : Set V)
  let J := G.induce s
  obtain ⟨edges, vertices⟩ := deleted_counts G x
  change Nat.card J.edgeSet + Nat.card {y // G.Adj x y} = Nat.card G.edgeSet at edges
  change Nat.card s + 1 = Nat.card V at vertices
  have flatJ := planar_subgraph G J Subtype.val Subtype.val_injective (fun _ _ h => h) flat
  have b := bipartite_edges flatJ (by omega) (side ∘ Subtype.val) (fun u v h => cuts u v h)
  omega

end RecognizingPotentiallyPlanarDegreeSequences.PlanarBounds
