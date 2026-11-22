import MatrixTreeWeight
import GraphCounts
import PlanarEdgeSwitch
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Edge selection and component minimization for connected planar
realizations. All sizes refer to the original labelled vertex set. -/

namespace Recognition.ForestSelection
open SimpleGraph LeanPool.K5MinorFreeChoosability
open scoped BigOperators

/-- A nonempty finite forest lies in a spanning tree of the complete graph
on the same vertices. -/
theorem forest_edge_bound {V : Type*} [Finite V] [Nonempty V] (G : SimpleGraph V)
    (forest : G.IsAcyclic) : Nat.card G.edgeSet < Nat.card V := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨T, sub, _, tree⟩ := (connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
    (H := G) le_top forest
  have edges := Finset.card_le_card (edgeFinset_mono sub)
  have count := tree.card_edgeFinset
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, Nat.card_eq_fintype_card]
  omega

/-- The first edge survives deletion as a connection between its endpoints;
the other edge can be taken in a different component. Positivity is used
only to find this second edge. -/
theorem select_edges {V : Type*} [Finite V] [Nonempty V] (G : SimpleGraph V)
    (positive : ∀ x, ∃ y, G.Adj x y) (dense : Nat.card V ≤ Nat.card G.edgeSet)
    (disconnected : ¬ G.Connected) :
    ∃ u v x y : V, G.Adj u v ∧ G.Adj x y ∧ ¬ G.Reachable u x ∧ ¬ G.IsBridge s(u,v) := by
  classical
  have cycle : ¬G.IsAcyclic := fun acyclic => (forest_edge_bound G acyclic).not_ge dense
  rw [isAcyclic_iff_forall_adj_isBridge] at cycle
  push Not at cycle
  obtain ⟨u,v,uv,nonbridge⟩ := cycle
  have apart : ∃ x, ¬ G.Reachable u x := by
    by_contra! all
    exact disconnected ((connected_iff_exists_forall_reachable G).2 ⟨u,all⟩)
  obtain ⟨x,ux⟩ := apart
  obtain ⟨y,xy⟩ := positive x
  exact ⟨u,v,x,y,uv,xy,ux,nonbridge⟩

/-- The geometric component switch, in a form that can be shared by any
finite vertex type. -/
def CanMerge (V : Type*) [Finite V] : Prop :=
  ∀ (G : SimpleGraph V), IsPlanar G → ∀ {u v x y : V},
    G.Adj u v → G.Adj x y → ¬G.Reachable u x → ¬G.IsBridge s(u,v) →
      ∃ H : SimpleGraph V, IsPlanar H ∧
        (∀ i, Nat.card {j // H.Adj i j} = Nat.card {j // G.Adj i j}) ∧
        Nat.card H.ConnectedComponent < Nat.card G.ConnectedComponent

private theorem degreeSum (ds : List Nat) (G : SimpleGraph (Fin ds.length))
    (row : ∀ i : Fin ds.length, Nat.card {j // G.Adj i j} = ds[i.val]) :
    ds.sum = 2 * Nat.card G.edgeSet := by
  classical
  have sum := G.sum_degrees_eq_twice_card_edges
  have each (i : Fin ds.length) : G.degree i = ds[i.val] := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact row i
  simp_rw [each] at sum
  have all : (∑ i : Fin ds.length, ds[i.val]) = ds.sum := by
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem <;> simp
  rwa [all, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at sum

/-- Minimize component count among all planar graphs with the indicated
labelled degrees. A component switch contradicts minimality unless the
minimum was already achieved by a connected graph. -/
theorem connected_of_switch (ds : List Nat) (nonempty : ds ≠ [])
    (positive : ∀ d ∈ ds, 0 < d) (enough : 2 * ds.length ≤ ds.sum)
    (merge : CanMerge (Fin ds.length))
    (realizes : ∃ G : SimpleGraph (Fin ds.length), IsPlanar G ∧
      ∀ i : Fin ds.length, Nat.card {j // G.Adj i j} = ds[i.val]) :
    ∃ G : ArithmeticRotation.ConnectedRealization ds, IsPlanar G.val := by
  classical
  have size : 0 < ds.length := List.length_pos_iff.2 nonempty
  let _ : Nonempty (Fin ds.length) := ⟨⟨0,size⟩⟩
  let P (n : Nat) := ∃ G : SimpleGraph (Fin ds.length), IsPlanar G ∧
    (∀ i : Fin ds.length, Nat.card {j // G.Adj i j} = ds[i.val]) ∧
    Nat.card G.ConnectedComponent = n
  obtain ⟨A,pa,ra⟩ := realizes
  have hex : ∃ n, P n := ⟨_,A,pa,ra,rfl⟩
  obtain ⟨G,plane,row,count⟩ := Nat.find_spec hex
  refine ⟨⟨G,?_,row⟩,plane⟩
  by_contra disc
  have neighbor (i : Fin ds.length) : ∃ j, G.Adj i j := by
    have val : 0 < Nat.card {j // G.Adj i j} := row i ▸ positive _ (List.getElem_mem i.isLt)
    obtain ⟨⟨j,hj⟩⟩ := (Nat.card_pos_iff.1 val).1
    exact ⟨j,hj⟩
  have density : Nat.card (Fin ds.length) ≤ Nat.card G.edgeSet := by
    rw [Nat.card_fin]
    have := degreeSum ds G row
    omega
  obtain ⟨u,v,x,y,uv,xy,apart,nonbridge⟩ := select_edges G neighbor density disc
  obtain ⟨H,ph,pres,less⟩ := merge G plane uv xy apart nonbridge
  have small : P (Nat.card H.ConnectedComponent) :=
    ⟨H,ph,fun i => (pres i).trans (row i),rfl⟩
  exact (Nat.find_min' hex small).not_gt (count ▸ less)

private theorem simple_row_iff (ds : List Nat) :
    SparseBoundary.Planaric ds ↔ ∃ G : SimpleGraph (Fin ds.length), IsPlanar G ∧
      ∀ i : Fin ds.length, Nat.card {j // G.Adj i j} = ds[i.val] := by
  classical
  constructor
  · rintro ⟨K, d, p⟩
    exact ⟨Wagner.toSimple K, (Wagner.planar_iff_rotation K).1 p,
      fun i => (Wagner.neighbor_count K i).trans (d i)⟩
  · rintro ⟨G, plane, row⟩
    let rel (i j : Fin ds.length) := decide (G.Adj i j)
    let K := SparseBoundary.Graph.ofRelation rel
    have edge (x y : Fin ds.length) : K.adj x y = rel x y :=
      SparseBoundary.Graph.adj_ofRelation rel (fun i j => decide_eq_decide.mpr (G.adj_comm i j))
        (fun i => decide_eq_false_iff_not.mpr (G.irrefl (v := i))) x y
    have same : Wagner.toSimple K = G := by
      ext x y
      rw [Wagner.toSimple_adj,edge]
      simp [rel]
    refine ⟨K, ?_, (Wagner.planar_iff_rotation K).2 (same ▸ plane)⟩
    intro i
    rw [← Wagner.neighbor_count K i, same]
    exact row i

theorem planaric_connected_iff_of_switch (ds : List Nat) (nonempty : ds ≠ [])
    (positive : ∀ d ∈ ds, 0 < d) (enough : 2 * ds.length ≤ ds.sum)
    (merge : CanMerge (Fin ds.length)) :
    SparseBoundary.Planaric ds ↔
      ∃ G : ArithmeticRotation.ConnectedRealization ds, IsPlanar G.val := by
  rw [simple_row_iff]
  exact ⟨connected_of_switch ds nonempty positive enough merge,
    fun ⟨H,p⟩ => ⟨H.val,p,H.property.2⟩⟩

/-- Every potentially planar positive list with at least as many edges as
vertices admits a connected planar realization, on the same input labels. -/
theorem planaric_connected_iff (ds : List Nat) (nonempty : ds ≠ [])
    (positive : ∀ d ∈ ds, 0 < d) (enough : 2 * ds.length ≤ ds.sum) :
    SparseBoundary.Planaric ds ↔
      ∃ G : ArithmeticRotation.ConnectedRealization ds, IsPlanar G.val :=
  planaric_connected_iff_of_switch ds nonempty positive enough fun G plane =>
    PlanarEdgeSwitch.merge G plane

/-- In the dense positive branch, the finite difference of the
tree-weighted rotation inventory decides ordinary potential planarity. -/
theorem tree_weighted_iff_planaric (ds : List Nat) (nonempty : ds ≠ [])
    (positive : ∀ d ∈ ds, 0 < d) (enough : 2 * ds.length ≤ ds.sum) :
    0 < SphericalTerm.alternating
        (ArithmeticRotation.rowInventory ds (MatrixTreeWeight.rotationWeight ds))
        (ds.sum / 2 + 2 - ds.length) ↔ SparseBoundary.Planaric ds :=
  (MatrixTreeWeight.tree_weighted_difference ds positive).trans
    (planaric_connected_iff ds nonempty positive enough).symm

end Recognition.ForestSelection
