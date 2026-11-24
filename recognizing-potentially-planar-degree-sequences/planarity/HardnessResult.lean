import RawWire
import EmbeddingBridge
import WireSearch

/-! The promised ordinary graph language, its binary certificate, and
the unrestricted CNF input all refer to the same reduction output. -/
namespace Recognition.HardnessResult
open SparseBoundary Reduction

private theorem row (bs : List Bool) : ∃ I : Instance,SATBridge.satWire bs=Wire.degrees (reduceInstance I) := by
  cases h : SATBridge.readSAT bs with
  | none =>
    let I : Instance := ⟨[],0,0⟩
    have bad : ¬Valid I := by intro v;have := v.1;change 0<0 at this;omega
    exact ⟨I,by simp only [SATBridge.satWire,h,reduce_invalid I bad];rfl⟩
  | some x =>
    exact ⟨SATBridge.instanceOfSAT x,by simp [SATBridge.satWire,h,Wire.reduceBits,Wire.reduceRow,Wire.source_round_trip]⟩

/-- For every CNF bit string, the very list written by the reduction is
Euler-tight and has a 3-connected simple realization. Positive outputs
admit a stacked triangulation, and have a bounded accepting bit certificate. -/
theorem restricted (bs : List Bool) : ∃ ds : List Nat,
    Wire.readDegrees (SATBridge.satWire bs)=some ds ∧ TableValid ds ∧
    Promise.ThreeConnectedRow ds ∧ (SATBridge.SATLanguage bs ↔ Planaric ds) ∧
    (Planaric ds → HasStackedRealization ds) ∧
    (Planaric ds ↔ ∃ w : List Bool,w.length≤5*(ds.length+1)^3 ∧ RawWire.verify ds w=true) := by
  obtain ⟨I,encoded⟩ := row bs
  let ds:=reduceInstance I
  have output : Wire.readDegrees (SATBridge.satWire bs)=some ds := encoded ▸ Wire.degrees_round_trip _
  have all:=Wagner.planaric_reduction_with_promises I
  simp only [ComplexityCost.compile_value] at all
  have non : ds≠[] := by intro e;have t:=all.2.2.1.1;change 5≤ds.length at t;simp [e] at t
  have exactSat:=SATBridge.sat_wire_iff bs
  simp only [Wire.degreeLanguage,output,Option.some.injEq,exists_eq_left'] at exactSat
  exact ⟨ds,output,all.2.2.1,all.2.2.2.1,exactSat.symm.trans (and_iff_right non),all.2.1,RawWire.bounded_certificate _⟩

/-- The ordinary NP verifier at the common bit alphabet. -/
def check (input certificate : List Bool) : Bool :=
  match WireSearch.parse input with
  | some (x::xs) => RawWire.verify (x::xs) certificate
  | _ => false

theorem positive_certificate (input : List Bool) :
    Wire.degreeLanguage Planaric input ↔
      ∃ w : List Bool,w.length≤5*(input.length+1)^3 ∧ check input w=true := by
  cases h : WireSearch.parse input with
  | none =>
    simp only [check,h,Bool.false_eq_true,and_false,exists_false,iff_false]
    rintro ⟨ds,raw,_,yes⟩
    rw [(WireSearch.parse_exact ..).mpr ⟨raw,WireSearch.degrees_fit yes⟩] at h
    contradiction
  | some ds =>
    have raw := ((WireSearch.parse_exact ..).mp h).1
    cases ds with
    | nil => simp [check,h,Wire.degreeLanguage,raw]
    | cons x xs =>
      simp only [check,h,Wire.degreeLanguage,raw,Option.some.injEq,exists_eq_left']
      constructor
      · rintro ⟨_,yes⟩
        obtain ⟨w,len,verified⟩:=(RawWire.bounded_certificate _).mp yes
        have arity := WireSearch.arity_eq input raw
        have size : (x::xs).length ≤ input.length := arity ▸ (WireSearch.count_tags input).2.2
        exact ⟨w,len.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right size 1) _)),verified⟩
      · rintro ⟨w,_,ok⟩
        exact ⟨by simp,(RawWire.verify_iff _).mp ⟨w,ok⟩⟩

end Recognition.HardnessResult
