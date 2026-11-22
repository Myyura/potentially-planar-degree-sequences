import MaximalPlane
import AugmentFaces
import ReverseTrace
import SparseBoundary.GraphEncoding

namespace Recognition.Augment
open SparseBoundary Recognition.Wagner LeanPool.K5MinorFreeChoosability

/-- Extend an arbitrary labelled simple planar graph to a triangulation on
the very same vertices, including the isolated labels of the input graph. -/
theorem augmentation {n : Nat} (hn : 4 ≤ n) : ReverseTrace.Augmentation n := by
  classical
  intro A planar
  let _ : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨H,inc,maximal⟩ := exists_maximal (toSimple A) ((planar_iff_rotation A).mp planar)
  obtain ⟨M⟩ := maximal.1
  have count := maximal_tight M maximal (maximal_connected maximal) (by simpa using hn)
  let rel (x y : Fin n) := decide (H.Adj x y)
  let K := Graph.ofRelation rel
  have edge (x y : Fin n) : K.adj x y = rel x y :=
    Graph.adj_ofRelation rel (fun i j => decide_eq_decide.mpr (H.adj_comm i j))
      (fun i => decide_eq_false_iff_not.mpr (H.irrefl (v:=i))) x y
  have same : toSimple K = H := by
    ext x y
    rw [toSimple_adj,edge]; simp [rel]
  refine ⟨K,?_,(planar_iff_rotation K).mpr (same ▸ maximal.1),?_,?_⟩
  · intro x y old
    rw [edge]; exact decide_eq_true (inc old)
  · simpa only [same] using count.1
  · simpa [same] using count.2

theorem face_certificate_iff (x : Nat) (ds : List Nat) (hn : 4 ≤ ds.length+1) :
    Planaric (x::ds) ↔ ∃ f, ∃ r : TraceCheck.Records ds.length f, TraceCheck.verify (x::ds) r :=
  ReverseTrace.certificate_iff_planaric x ds hn (augmentation hn)

end Recognition.Augment
