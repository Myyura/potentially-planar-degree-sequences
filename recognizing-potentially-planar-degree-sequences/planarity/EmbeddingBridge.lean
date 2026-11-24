import TightFaces
import FacialRotation
import GraphCounts
import Wire

/-! The full reduction now uses the two actual minor characterizations.
All graph labels survive the passage from the rotation system to the faces. -/
namespace Recognition.Wagner
open SparseBoundary LeanPool.K5MinorFreeChoosability

theorem tight_embedding : HardnessConverse.TightEmbedding := by
  intro d G valid realizes planar
  obtain ⟨M⟩ := (planar_iff_rotation G).mp planar
  obtain ⟨minDeg,edges⟩ := order_counts G valid realizes
  have pos := valid.1
  have ne : Nonempty (Fin d.length) := ⟨⟨0,by omega⟩⟩
  obtain ⟨one,three⟩ := tight_faces M (fun v => Nat.le_trans (by decide : 2≤3) (minDeg v)) ne edges
  exact Rotation.to_model G (rotation G (toSimple G) (toSimple_adj G) M minDeg one three) valid realizes

/-- The ordinary degree-realization reduction, without an embedding premise. -/
theorem planaric_reduction_iff (I : Reduction.Instance) :
    Planaric (Reduction.reduceInstance I) ↔ Reduction.Valid I ∧ Reduction.ThreePartition I :=
  Transfer.reduction_iff tight_embedding I

theorem planaric_bit_reduction (bs : List Bool) :
    Wire.degreeLanguage Planaric (Wire.reduceBits bs) ↔ Wire.UnaryThreePartition bs :=
  Wire.wire_planaric tight_embedding bs

theorem planaric_reduction_with_promises (I : Reduction.Instance) :
    let out := ComplexityCost.compile I
    (Planaric out.value ↔ Reduction.Valid I ∧ Reduction.ThreePartition I) ∧
    (Planaric out.value → HasStackedRealization out.value) ∧
    Reduction.TableValid out.value ∧ Promise.ThreeConnectedRow out.value ∧
    out.work ≤ ComplexityCost.workBound (ComplexityCost.unarySize I) := by
  dsimp only
  rw [ComplexityCost.compile_value]
  exact ⟨planaric_reduction_iff I,fun p => (stacked_reduction_iff I).mpr ((planaric_reduction_iff I).mp p),
    (Transfer.all_promises I).1,(Transfer.all_promises I).2,ComplexityCost.compile_work I⟩

end Recognition.Wagner
