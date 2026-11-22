import HardnessResult
import SATCost
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! The strong reduction writes a delimiter after each unary degree. Both the
transcoding algorithm and its costs are included, even on invalid CNF syntax. -/
namespace Recognition.UnaryHardness
open Reduction SparseBoundary Polynomial

private def emit : List Nat → List Bool × Nat
  | [] => ([],1)
  | n::ns =>
    let rest := emit ns
    (List.replicate n true ++ false::rest.1, rest.2+2*n+3)

private theorem emit_spec (ds : List Nat) :
    (emit ds).1=Wire.unary ds ∧ (emit ds).2=1+2*ds.sum+3*ds.length := by
  induction ds with
  | nil => simp [emit,Wire.unary]
  | cons n ns ih =>
    obtain ⟨v,w⟩ := ih
    constructor
    · change List.replicate n true ++ false::(emit ns).1 = _
      rw [v]
      simp [Wire.unary,List.append_assoc]
    · change (emit ns).2 + 2*n + 3 = _
      rw [w]; simp only [List.sum_cons,List.length_cons]; omega

def run (bs : List Bool) : List Bool × Nat :=
  let bin := SATCost.run bs
  let read := WireSearch.decode bin.1
  let unary := emit (read.1.getD [])
  (unary.1,bin.2+read.2+unary.2+2)

private theorem intermediate (bs : List Bool) : ∃ ds,
    (WireSearch.decode (SATCost.run bs).1).1=some ds ∧
    ds.length≤(SATBridge.satWire bs).length ∧ TableValid ds ∧
    Promise.ThreeConnectedRow ds ∧ (SATBridge.SATLanguage bs ↔ Planaric ds) ∧
    (Planaric ds → HasStackedRealization ds) := by
  obtain ⟨ds,raw,valid,connected,equiv,stacked,_⟩ := HardnessResult.restricted bs
  have parsed := (WireSearch.parse_exact _ _).mpr ⟨raw,fun _ h => (valid.2.2 _ h).2.le⟩
  have n := WireSearch.arity_eq _ raw
  exact ⟨ds,by rw [(WireSearch.decode_work _).1,SATCost.run_value,parsed],
    n ▸ (WireSearch.count_tags _).2.2,valid,connected,equiv,stacked⟩

/-- Exact output, including the number of bits contributed by the separators. -/
theorem restricted (bs : List Bool) : ∃ ds, Wire.fields (run bs).1=some ds ∧
    (run bs).1.length+12=7*ds.length ∧ TableValid ds ∧ Promise.ThreeConnectedRow ds ∧
    (SATBridge.SATLanguage bs ↔ Planaric ds) ∧ (Planaric ds → HasStackedRealization ds) := by
  obtain ⟨ds,dec,_,v,con,iff,stacked⟩ := intermediate bs
  have val : (run bs).1=Wire.unary ds := by simp only [run,dec,Option.getD_some,(emit_spec ds).1]
  refine ⟨ds,val ▸ Wire.fields_unary ds,?_,v,con,iff,stacked⟩
  rw [val,Wire.unary_length]; have := v.2.1; omega

theorem polynomial_cost : ∃ P : Polynomial Nat, ∀ bs : List Bool, (run bs).2≤P.eval bs.length := by
  obtain ⟨a,i,binWork⟩ := SATCost.run_work
  obtain ⟨b,j,binLength⟩ := SATBridge.sat_output_polynomial
  let z := (X : Polynomial Nat)
  let B := 13*(3^57*(5*(12+C b*(4*z+2)^j)+6)^73+6)
  refine ⟨C a*(z+1)^i+21*B+5, fun bs => ?_⟩
  obtain ⟨ds,dec,size,valid,_⟩ := intermediate bs
  have fee := (WireSearch.decode_work (SATCost.run bs).1).2
  rw [SATCost.run_value] at fee
  have ff : (emit ds).2≤1+15*ds.length := by
    rw [(emit_spec ds).2]; have := valid.2.1; omega
  simp only [run,dec,Option.getD_some]
  simp [B,z,SATCost.run_value]
  have := binWork bs; have := binLength bs
  omega

def Language (bs : List Bool) : Prop := ∃ ds, Wire.fields bs=some ds ∧ ds≠[] ∧ Planaric ds

theorem reduction : (∃ P : Polynomial Nat, ∀ bs : List Bool, (run bs).2≤P.eval bs.length) ∧
    ∀ bs : List Bool, SATBridge.SATLanguage bs ↔ Language (run bs).1 := by
  refine ⟨polynomial_cost,fun bs => ?_⟩
  obtain ⟨ds,dec,_,valid,_,iff,_⟩ := restricted bs
  have ne : ds≠[] := by intro h; have := valid.1; simp [h] at this
  simpa [Language,dec,ne] using iff

/-- Each input bit is visited once; the two possible successes either start
a fresh field or increment the current field's count. -/
def readMeter : List Bool → Option (List Nat) × Nat
  | [] => (some [],1)
  | b::bs =>
    let rest := readMeter bs
    (if b then (do
       let n::ns ← rest.1 | none
       return (n+1)::ns)
     else rest.1.map (0::·),rest.2+3)

theorem readMeter_spec (input : List Bool) :
    (readMeter input).1=Wire.fields input ∧ (readMeter input).2=3*input.length+1 := by
  induction input with
  | nil => exact ⟨rfl,rfl⟩
  | cons b bs ih =>
    cases b <;> simp only [readMeter,Wire.fields,ih.1,ih.2,List.length_cons] <;>
      constructor <;> rfl

private theorem field_count {b ds} (h : Wire.fields b=some ds) : ds.length≤b.length := by
  induction b generalizing ds with
  | nil => simp [Wire.fields] at h;subst ds;simp
  | cons bit bs ih =>
    cases rest : Wire.fields bs with
    | none => cases bit <;> simp [Wire.fields,rest] at h
    | some l =>
      have bound := ih rest
      cases bit with
      | false => simp [Wire.fields,rest] at h;subst ds;simp;omega
      | true => cases l with
        | nil => simp [Wire.fields,rest] at h
        | cons r rs => simp [Wire.fields,rest] at h;subst ds;simp at *;omega

def check (input w : List Bool) :=
  match (readMeter input).1 with
  | some (x::xs) => RawWire.verify (x::xs) w
  | _ => false

theorem positive_certificate (input : List Bool) : Language input ↔
    ∃ w : List Bool,w.length≤5*(input.length+1)^3 ∧ check input w=true := by
  simp only [check,(readMeter_spec input).1,Language]
  cases h : Wire.fields input with
  | none => simp
  | some row =>
    have size := field_count h
    cases row with
    | nil => simp
    | cons x xs =>
      simp only [Option.some.injEq,exists_eq_left']
      constructor
      · rintro ⟨_,yes⟩
        obtain ⟨w,l,v⟩ := (RawWire.bounded_certificate _).mp yes
        exact ⟨w,l.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right size 1) _)),v⟩
      · rintro ⟨w,_,v⟩
        exact ⟨by simp,(RawWire.verify_iff _).mp ⟨w,v⟩⟩

end Recognition.UnaryHardness
