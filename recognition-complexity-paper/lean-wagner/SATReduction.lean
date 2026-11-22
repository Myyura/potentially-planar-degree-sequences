import HardnessReductions.Sets.Matching3D.FromSat.Adequacy
import HardnessReductions.Numbers.Partition3.FromPartition4.Adequacy
import PartitionInput

/-! A concrete Boolean CNF reduces to the binary ordinary degree language.
The source construction is the certified SAT → 3DM → unary 4-partition →
unary 3-partition chain. -/
namespace Recognition.SATBridge
open Hardness.Cert Reduction SparseBoundary

def satToThree : CertifiedReduction Concrete.SAT Concrete.THREE_PARTITION_UNARY_WINDOW :=
  satToMatching3DCertified.comp matching3DToThreePartitionCertified

def instanceOfSAT (x : SatTy.denote) :=
  importPartition (decodeNumberTargetUnary (satToThree.code.eval x))

theorem sat_iff_partition (x : SatTy.denote) :
    Concrete.SAT x ↔ Valid (instanceOfSAT x) ∧ ThreePartition (instanceOfSAT x) :=
  (satToThree.correct x).trans (partition_input_iff _)

theorem sat_iff_unary (x : SatTy.denote) :
    Concrete.SAT x ↔ Wire.UnaryThreePartition (Wire.sourceCode (instanceOfSAT x)) := by
  simpa [Wire.UnaryThreePartition,Wire.source_round_trip] using sat_iff_partition x

theorem sat_iff_planaric (x : SatTy.denote) :
    Concrete.SAT x ↔ Planaric (reduceInstance (instanceOfSAT x)) :=
  (sat_iff_partition x).trans (Wagner.planaric_reduction_iff _).symm

private theorem unary_size (u : List Bool) : Ty.unary.size u = 2*u.length+1 := by
  induction u with
  | nil => rfl
  | cons b bs ih =>
    simp only [Ty.size_list,Ty.size_bool,List.map_cons,List.sum_cons,List.length_cons] at *
    omega

private theorem sizes (ls : List (List Bool)) :
    ((ls.map (Ty.unary.size ·)).sum) = 2*(ls.map List.length).sum+ls.length := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [ih, unary_size]
    omega

private theorem size_import (y : NumberTargetUnaryTy.denote) :
    ComplexityCost.unarySize (importPartition (decodeNumberTargetUnary y)) ≤
      11 + NumberTargetUnaryTy.size y := by
  obtain ⟨ys,b⟩ := y
  simp only [Ty.size_pair,Ty.size_list,Ty.size_bool]
  change _ ≤ 11 + (((ys.map (Ty.unary.size ·)).sum+ys.length+1) +
    ((b.map (fun _ => 1)).sum+b.length+1)+1)
  rw [sizes]
  unfold importPartition decodeNumberTargetUnary
  dsimp only
  split
  · change 11 ≤ _; omega
  · simp only [ComplexityCost.unarySize,List.length_map]
    change 1 + ys.length + (ys.map List.length).sum + ys.length / 3 + b.length ≤ _
    omega

/-- The cost of the certified SAT prefix and the size of the actual unary
input to the degree compiler have one polynomial bound in the CNF size. -/
theorem sat_prefix_polynomial :
    ∃ C d, ∀ x : SatTy.denote, satToThree.code.cost x + ComplexityCost.unarySize (instanceOfSAT x)
      ≤ 11 + C * (SatTy.size x + 1)^d := by
  obtain ⟨c,d,bound⟩ := satToThree.code.cost_size_le_polyBound
  exact ⟨c,d,fun x => by
    have hi := size_import (satToThree.code.eval x)
    have hj := bound x
    change _ ≤ c*(SatTy.size x+1)^d at hj
    change _ ≤ 11 + NumberTargetUnaryTy.size (satToThree.code.eval x) at hi
    unfold instanceOfSAT; omega⟩

end Recognition.SATBridge
