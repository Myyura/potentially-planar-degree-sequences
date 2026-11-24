import Triangulation.BipartiteMinor
import Triangulation.Forward
import Triangulation.SourceBridge
import Triangulation.HardnessConverse
import StackedGraph
import SparseBoundary.GraphEncoding

/-! Interface between the finite face and forbidden-minor definitions.
Both directions of the geometric bridge are propositions, not axioms. -/
namespace Recognition.Transfer
open SparseBoundary Reduction Layers HardnessConverse

/-- The labelled graph extracted from the actual faces of a model. -/
noncomputable def graph {d : List Nat} (R : Model d) : Graph d.length := by
  classical
  exact Graph.ofRelation fun i j => decide (R.edge i.val j.val)

theorem same_edges {d : List Nat} (R : Model d) : SameEdges R (graph R) := by
  classical
  let a : Fin d.length → Fin d.length → Bool := fun i j => decide (R.edge i.val j.val)
  have sym i j : R.edge i j → R.edge j i := by
    rintro ⟨x,y,hx,hy,z,f⟩
    exact ⟨y,x,hy,hx,z,R.map.flip f⟩
  have comm i j : a i j = a j i := by
    apply decide_eq_decide.mpr
    exact ⟨sym _ _,sym _ _⟩
  have irr i : a i i = false := by
    change decide (R.edge i.val i.val) = false
    apply decide_eq_false_iff_not.mpr
    rintro ⟨x,y,hx,hy,z,f⟩
    exact R.map.distinct f (R.inj _ _ (hx.trans hy.symm))
  intro i j
  change R.edge i.val j.val ↔ (Graph.ofRelation a).adj i j = true
  rw [Graph.adj_ofRelation _ comm irr]
  exact decide_eq_true_iff.symm

theorem graph_realizes {d : List Nat} (R : Model d) : (graph R).Realizes d :=
  compatible_degrees R _ (same_edges R)

theorem partition_to_stacked (I : Instance) (hv : Valid I) (hp : ThreePartition I) :
    ∃ R : Model (encode I), StackedMap R.map := by
  obtain ⟨R, origin, required⟩ := SourceBridge.prescribed_origin I hv hp
  exact Forward.encode_stacked I hv R origin required

theorem partition_to_planaric (I : Instance) (hv : Valid I) (hp : ThreePartition I) :
    Planaric (encode I) := by
  obtain ⟨R,origin⟩ := partition_to_stacked I hv hp
  exact ⟨graph R,graph_realizes R,BipartiteMinor.stacked_planar R origin (graph R) (same_edges R)⟩

theorem partition_to_map (I : Instance) (hv : Valid I) (hp : ThreePartition I) :
    Nonempty (Model (encode I)) := by
  obtain ⟨R, required⟩ := SourceBridge.prescribed_model I hv hp
  exact Forward.encode_prescribed I hv R required

/-- The numerical and 3-connectivity promises hold even for malformed input. -/
theorem all_promises (I : Instance) :
    TableValid (reduceInstance I) ∧ Promise.ThreeConnectedRow (reduceInstance I) :=
  ⟨reduce_promise I, StackedGraph.reduction_three_connected I⟩

/-- Correctness of the actual total instance map, using the
Euler-tight embedding theorem for the reverse implication. The source language includes its validity check. -/
theorem reduction_iff (inwards : TightEmbedding) (I : Instance) :
    Planaric (reduceInstance I) ↔ Valid I ∧ ThreePartition I := by
  by_cases hv : Valid I
  · rw [reduce_valid I hv]
    constructor
    · exact fun h => ⟨hv, hardness_converse inwards I hv h⟩
    · intro ⟨_, hp⟩
      exact partition_to_planaric I hv hp
  · rw [reduce_invalid I hv]
    exact ⟨fun h => False.elim (Promise.malformed_no h), fun h => False.elim (hv h.1)⟩
end Recognition.Transfer
