import BagArithmetic
import Mathlib.Algebra.BigOperators.Pi

/-! Pair the homomorphism count with its arithmetic tariff as each
marginal table is produced, and pair the signed inclusion–exclusion
summands with their charges in the same traversal of target subsets. -/
namespace Recognition.BagMeter
open Finset StateIso BagHom

def run (fill : Fin m) : List (Fin n) → List (Factor n m) → Nat × Nat
  | [],fs => (weight fs (fun _ => fill),fs.length)
  | v::vs,fs =>
    let emitted := eliminate v fs fill
    let rest := run fill vs emitted
    (rest.1,m^(bag v fs).card*m*((withVar v fs).length+1)+rest.2)

theorem run_result (fill : Fin m) (order : List (Fin n)) (fs : List (Factor n m)) :
    run fill order fs =
      (weight (BagHom.run fill order fs) (fun _ => fill),BagArithmetic.arithmetic fill order fs) := by
  induction order generalizing fs with
  | nil => rfl
  | cons v vs ih => simp only [run,ih,BagArithmetic.arithmetic,BagHom.run,List.foldl_cons]

def subsets (A : Colored n) (B : Colored m) (fill : Fin m) (order : List (Fin n)) : Int × Nat :=
  ∑ Y∈(univ : Finset (Fin m)).powerset,
    let (count,fee):=run fill order (constraints A B Y)
    (((-1:Int)^Y.card*(count:Int)),fee+2)

theorem subsets_value (A : Colored n) (B : Colored m) (order : List (Fin n)) (h : 0<m) :
    (subsets A B ⟨0,h⟩ order).1=alternating (BagHom.count A B order) := by
  simp only [subsets,Prod.fst_sum,run_result,alternating,BagHom.count,dite_eq_left h]

theorem subsets_cost (A : Colored n) (B : Colored m) (fill : Fin m) (order : List (Fin n)) :
    (subsets A B fill order).2=∑Y∈(univ : Finset (Fin m)).powerset,
      (BagArithmetic.arithmetic fill order (constraints A B Y)+2) := by
  simp only [subsets,Prod.snd_sum,run_result]

def compare (A : Colored n) (B : Colored m) : Bool × Nat :=
  if h : 0<m then
    let (votes,fee):=subsets A B ⟨0,h⟩ (List.finRange n)
    (decide (n=m ∧ (arcs A).card=(arcs B).card ∧ 0<votes),fee)
  else (BagHom.compare A B (List.finRange n),2)

theorem compare_eq (A : Colored n) (B : Colored m) : (compare A B).1=BagHom.compare A B (List.finRange n) := by
  simp only [compare];split <;> rename_i h
  · rw [subsets_value _ _ _ h];rfl
  · rfl

end Recognition.BagMeter
