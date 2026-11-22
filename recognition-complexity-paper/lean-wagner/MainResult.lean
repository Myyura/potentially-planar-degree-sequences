import CoveredOrder
import SeparatorInput
import WitnessTable
import SATWire
import VerifierCost
import SparseCompare

/-! User-facing decision and realization theorems for ordinary planar
degree lists, with the geometric input to the compressed algorithm exposed. -/
namespace Recognition.MainResult
open SparseBoundary QuotientDP PlanarDegrees.Frontier Recognition.Wagner

theorem sat_and_certificate (bs : List Bool) :
    SATBridge.SATLanguage bs ↔ ∃ d, Wire.readDegrees (SATBridge.satWire bs)=some d ∧
      d≠[] ∧ ∃ C : RotationVerifier.Raw d.length, RotationVerifier.verify d C := by
  rw [←SATBridge.sat_wire_iff]
  simp only [Wire.degreeLanguage,RotationVerifier.verify_iff]

theorem volume {d : List Nat} (yes : Planaric d) : d.sum≤6*d.length := by
  classical
  obtain ⟨G,deg,planar⟩ := yes
  have bound := SparseOverlay.edge_bound _ (toSimple G) ((planar_iff_rotation G).mp planar)
  have sum := (toSimple G).sum_degrees_eq_twice_card_edges
  have each (i : Fin d.length) : (toSimple G).degree i=d[i] := by
    rw [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
    exact (neighbor_count G i).trans (deg i)
  have same : (∑ i : Fin d.length, d[i]) = d.sum := by
    rw [←List.sum_ofFn]; congr 1; apply List.ext_getElem <;> simp
  simp_rw [each] at sum
  rw [same] at sum
  rw [Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card,Nat.card_fin] at bound
  omega

/-- A comparator may use any algorithm for the recorded degrees, global
counters and coloured frontier isomorphism. -/
abbrev Comparator := ∀ {n : Nat}, State n → State n → Bool

def findWith (cmp : Comparator) : (d : List Nat) → Option (Graph d.length)
  | [] => Certificate.findRealization []
  | x::ds =>
    let n := ds.length+1
    if 6*n < (x::ds).sum then none
    else if n<4 then Certificate.findRealization (x::ds)
    else WitnessTable.realize cmp (ShortBoundary.catalogue (x::ds)) (x::ds) (2*n-5)

/-- Every graph actually returned is planar and realizes the input degrees
in their stated order. This direction is unconditional. -/
theorem findWith_sound (cmp : Comparator) (d : List Nat) (G : Graph d.length) (hit : findWith cmp d=some G) :
    G.Planar ∧ G.Realizes d := by
  cases d with
  | nil => exact (Certificate.findRealization_sound hit).symm
  | cons x ds =>
    simp only [findWith] at hit
    split at hit <;> rename_i cut
    · contradiction
    · split at hit <;> rename_i small
      · exact (Certificate.findRealization_sound hit).symm
      · exact WitnessTable.realize_sound _ _ _ _ _ (by omega) hit

/-- Relative to the published weighted planar separator theorem, this
executable finite-table search returns a labelled graph on every yes-input. -/
theorem findWith_iff (cmp : Comparator) (test : ∀ {n} (a b : State n),cmp a b=true ↔ Same a b)
    (sep : SeparatorInput.WeightedPlanarSeparator) (d : List Nat) :
    (findWith cmp d).isSome ↔ Planaric d := by
  constructor
  · intro hit
    obtain ⟨G,yes⟩ := Option.isSome_iff_exists.mp hit
    obtain ⟨planar,degree⟩ := findWith_sound cmp d G yes
    exact ⟨G,degree,planar⟩
  · intro yes
    cases d with
    | nil => exact (Certificate.findRealization_iff []).mpr yes
    | cons x ds =>
      have sumBound := volume yes
      change (x::ds).sum ≤ 6*(ds.length+1) at sumBound
      simp only [findWith,ite_eq_right (Nat.not_lt.mpr sumBound)]
      split
      · exact (Certificate.findRealization_iff _).mpr yes
      · rename_i large
        obtain ⟨f,r,valid⟩ := (Augment.face_certificate_iff x ds (by omega)).mp yes
        obtain ⟨_,count,_,C,degrees,_⟩ := TraceCheck.verify_sound _ r valid
        have sepC := SeparatorInput.host sep C count (fun v => cost (simpleDegree C.ledger.sealed v))
          (by intro i hi; simp [cost])
        obtain ⟨s,path,done⟩ := CoveredOrder.path x ds C count degrees sepC
        obtain ⟨G,hit,_,_⟩ := WitnessTable.realize_of_path cmp test
          (ShortBoundary.catalogue (x::ds)) (x::ds) f s count path done
        have fEq : 2*(ds.length+1)-5=f := by omega
        rw [fEq,hit]; rfl

/-- Reference implementation with the built-in exact comparison. -/
def find : (d : List Nat) → Option (Graph d.length) := findWith StateIncidence.compare

theorem find_sound (d : List Nat) (G : Graph d.length) (hit : find d=some G) :
    G.Planar ∧ G.Realizes d := findWith_sound StateIncidence.compare d G hit

theorem find_iff (sep : SeparatorInput.WeightedPlanarSeparator) (d : List Nat) :
    (find d).isSome ↔ Planaric d := findWith_iff StateIncidence.compare StateIncidence.compare_iff sep d

end Recognition.MainResult

namespace Recognition.StateIncidence
open QuotientDP

/-- Explicit GI hook on the two finite coloured incidence graphs. -/
abbrev ColorTest := ∀ {n m : Nat}, StateIso.Colored n → StateIso.Colored m → Bool

def compareUsing (gi : ColorTest) (s t : State n) : Bool :=
  decide (s.remaining=t.remaining ∧ s.used=t.used ∧ s.faces=t.faces) && gi (graph s) (graph t)

theorem compareUsing_iff (gi : ColorTest)
    (test : ∀ {n m} (A : StateIso.Colored n) (B : StateIso.Colored m),gi A B=true ↔ StateIso.Iso A B)
    (s t : State n) : compareUsing gi s t=true ↔ Same s t := by
  rw [same_iff]
  simp only [compareUsing,Bool.and_eq_true,decide_eq_true_eq,test]; tauto

end Recognition.StateIncidence
