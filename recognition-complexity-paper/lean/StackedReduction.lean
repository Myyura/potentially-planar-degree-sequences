import Certificate
import ComplexityCost
import Enumeration
import Fallback
import Triangulation.StackedMinor
import MapCode
import TraceCheck

/-! Main reduction statements. The standard geometric translations and the
external complexity-class results are listed in the companion proof index. -/
namespace Recognition
open SparseBoundary Reduction Layers Transfer SourceConverse

def HasStackedRealization (d : List Nat) : Prop := ∃ R : Layers.Model d, StackedMap R.map

theorem stacked_graph_k5free {d : List Nat} (R : Layers.Model d) (h : StackedMap R.map) :
    K5Free (graph R) := by
  rintro ⟨bags,minor⟩
  rw [StackedMinor.no_clique5_minor R h _ (same_edges R) bags] at minor
  contradiction

/-- Exact reduction, on every parsed input, for the language of degree lists
admitting a tetrahedron-plus-facial-stellations construction. -/
theorem stacked_reduction_iff (I : Instance) :
    HasStackedRealization (reduceInstance I) ↔ Valid I ∧ ThreePartition I := by
  by_cases hv : Valid I
  · rw [reduce_valid I hv]
    refine ⟨?_,fun ⟨_,partition⟩ => partition_to_stacked I hv partition⟩
    rintro ⟨R,built⟩
    exact ⟨hv,HardnessConverse.decode_output_k5free I hv (graph R)
      (stacked_graph_k5free R built) R (same_edges R)⟩
  · rw [reduce_invalid I hv]
    exact ⟨fun ⟨R,_⟩ => False.elim (malformed_no_map ⟨R⟩), fun h => False.elim (hv h.1)⟩

/-- The metered program and the full output promises refer to the same value. -/
theorem metered_stacked_reduction (I : Instance) :
    let out := ComplexityCost.compile I
    (HasStackedRealization out.value ↔ Valid I ∧ ThreePartition I) ∧
    TableValid out.value ∧ Promise.ThreeConnectedRow out.value ∧
    out.work ≤ ComplexityCost.workBound (ComplexityCost.unarySize I) := by
  dsimp only
  rw [ComplexityCost.compile_value]
  exact ⟨stacked_reduction_iff I,(all_promises I).1,(all_promises I).2,ComplexityCost.compile_work I⟩

end Recognition
