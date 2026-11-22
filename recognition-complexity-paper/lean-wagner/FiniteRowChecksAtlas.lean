import FiniteRowChecks1
import FiniteRowChecks2
import FiniteRowChecks3
import FiniteRowChecks4
import FiniteRowChecks5
import FiniteRowChecks6
import FiniteRowChecks7

/-! Kernel-checked comparison with the finite degree catalogue accompanying
the paper (verification/data/atlas_summary.json, SHA-256
40133ae73f7034e77fbb33ac6597580a0e0b248a91c652883343e259b17a1ea7). At each order the first bit indexes the all-zero descending row. -/
namespace Recognition.FiniteRowChecks
open SparseBoundary

def atlas : Nat → Nat
  | 1 => atlas1 | 2 => atlas2 | 3 => atlas3 | 4 => atlas4
  | 5 => atlas5 | 6 => atlas6 | 7 => atlas7 | _ => 0

def atlasPositive (n : Nat) :=
  (candidates n).zipIdx.filterMap fun ⟨d,i⟩ => if (atlas n).testBit i then some d else none

theorem atlas_exact (n : Nat) (lo : 1≤n) (hi : n≤7) (j : Fin (candidates n).length) :
    Planaric (candidates n)[j] ↔ (atlas n).testBit j.val=true := by
  have orders : n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 ∨ n=6 ∨ n=7 := by omega
  rcases orders with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simpa only [atlas,Nat.zero_add] using audit_sound checked1 j
  · simpa only [atlas,Nat.zero_add] using audit_sound checked2 j
  · simpa only [atlas,Nat.zero_add] using audit_sound checked3 j
  · simpa only [atlas,Nat.zero_add] using audit_sound checked4 j
  · simpa only [atlas,Nat.zero_add] using audit_sound checked5 j
  · simpa only [atlas,Nat.zero_add] using audit_sound checked6 j
  · simpa only [atlas,Nat.zero_add] using audit_sound checked7 j

theorem positive_rows (n : Nat) (lo : 1≤n) (hi : n≤7) (d : List Nat) :
    d∈atlasPositive n ↔ d∈candidates n ∧ Planaric d := by
  simp only [atlasPositive,List.mem_filterMap,List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff,Prod.exists]
  constructor
  · rintro ⟨x,i,p,index⟩
    split at index
    next h =>
      have eq := Option.some.inj index
      subst d
      have ⟨bnd,entry⟩ := p
      have tr:= (atlas_exact n lo hi ⟨i,bnd⟩).mpr h
      simpa [entry] using And.intro (List.getElem_mem bnd) tr
    · contradiction
  · rintro ⟨m,yes⟩
    obtain ⟨i,hi',hit⟩ := List.mem_iff_getElem.mp m
    have occ:= (atlas_exact n lo hi ⟨i,hi'⟩).mp (hit ▸ yes)
    exact ⟨d,i,⟨hi',hit⟩,by simp [occ]⟩

/-- The labelled face-record recurrence has the same truth value at every
position. On fewer than four vertices its small-graph branch is exhaustive. -/
def labelledFace : List Nat → Prop
  | [] => False
  | x::xs => if xs.length+1<4 then (Certificate.findRealization (x::xs)).isSome=true
    else ∃ f,∃ r : TraceCheck.Records xs.length f,TraceCheck.verify (x::xs) r

theorem face_agreement (n : Nat) (lo : 1≤n) (hi : n≤7) (j : Fin (candidates n).length) :
    labelledFace (candidates n)[j] ↔ (atlas n).testBit j.val=true := by
  rw [←atlas_exact n lo hi j]
  have len := ((candidates_spec n _).mp (List.getElem_mem j.isLt)).1
  generalize e : (candidates n)[j]=d at len ⊢
  cases d with
  | nil => simp at len;omega
  | cons x xs =>
    simp only [labelledFace]
    split
    · exact Certificate.findRealization_iff _
    · exact (Augment.face_certificate_iff x xs (by omega)).symm

theorem interval_agreement (ord : CanonicalRow.CanonicalOrderingInput)
    (n : Nat) (lo : 1≤n) (hi : n≤7) (j : Fin (candidates n).length) :
    (∃ xs : List Nat,xs.Perm ((candidates n)[j].filter (fun x=>0<x)) ∧
      RowRule.NumericalTrace xs []) ↔ (atlas n).testBit j.val=true :=
  (RowRecognition.interval_iff ord _).symm.trans (atlas_exact n lo hi j)

set_option maxRecDepth 100000 in
theorem input_counts :
    ([1,2,3,4,5,6,7].map (fun n=>(candidates n).length))=[1,3,10,35,126,462,1716] ∧
    ([1,2,3,4,5].map (fun n=>(candidates n).length)).sum=175 ∧
    ([1,2,3,4,5,6,7].map (fun n=>(candidates n).length)).sum=2353 := by decide +kernel

set_option maxRecDepth 100000 in
theorem positive_counts :
    ([1,2,3,4,5,6,7].map (fun n=>(atlasPositive n).length))=[1,2,4,11,30,92,272] ∧
    ([1,2,3,4,5].map (fun n=>(atlasPositive n).length)).sum=48 := by decide +kernel

end Recognition.FiniteRowChecks
