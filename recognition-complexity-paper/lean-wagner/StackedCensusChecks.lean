import StackedCensusDirectory
import Mathlib.Tactic.FinCases

namespace Recognition.StackedCensus
open CensusEncoding StackedQuota

def triples (a b c : Nat) := (diskDir a).every fun x _ =>
  (diskDir b).every fun y _ => (diskDir c).every fun z _ =>
    ((diskDir (1+a+b+c)).find (combine x y z)).isSome

def quadruples (a b c d : Nat) := (diskDir a).every fun x _ =>
  (diskDir b).every fun y _ => (diskDir c).every fun z _ => (diskDir d).every fun v _ =>
    ((shellDir (a+b+c+d)).find (assembled x y z v)).isSome

def validWitness (n : Nat) := (shellDir n).every fun k s =>
  decide (code s.profile = k ∧ s.profile.length = n+4)

def recognized (n : Nat) := (candidates n).filter fun d =>
  ((shellDir (n-4)).find (code d)).isSome

/- Check one certificate at a time. The largest directories are partitioned
by the sizes of the first two disks before kernel reduction. -/
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem disk_base : (diskDir 0).find 0 = some () := by decide +kernel

theorem tri0 : ∀ i j : Fin 1, i.val+j.val ≤ 0 → triples i.val j.val (0-i.val-j.val) = true := by decide +kernel
theorem tri1 : ∀ i j : Fin 2, i.val+j.val ≤ 1 → triples i.val j.val (1-i.val-j.val) = true := by decide +kernel
theorem tri2 : ∀ i j : Fin 3, i.val+j.val ≤ 2 → triples i.val j.val (2-i.val-j.val) = true := by decide +kernel
theorem tri3 : ∀ i j : Fin 4, i.val+j.val ≤ 3 → triples i.val j.val (3-i.val-j.val) = true := by decide +kernel
theorem tri4 : ∀ i j : Fin 5, i.val+j.val ≤ 4 → triples i.val j.val (4-i.val-j.val) = true := by decide +kernel
theorem tri5 : ∀ i j : Fin 6, i.val+j.val ≤ 5 → triples i.val j.val (5-i.val-j.val) = true := by decide +kernel
theorem tri6 : ∀ i j : Fin 7, i.val+j.val ≤ 6 → triples i.val j.val (6-i.val-j.val) = true := by decide +kernel
theorem tri7 : ∀ i j : Fin 8, i.val+j.val ≤ 7 → triples i.val j.val (7-i.val-j.val) = true := by decide +kernel

theorem quad0 : ∀ i j k : Fin 1, i.val+j.val+k.val ≤ 0 → quadruples i.val j.val k.val (0-i.val-j.val-k.val) = true := by decide +kernel
theorem quad1 : ∀ i j k : Fin 2, i.val+j.val+k.val ≤ 1 → quadruples i.val j.val k.val (1-i.val-j.val-k.val) = true := by decide +kernel
theorem quad2 : ∀ i j k : Fin 3, i.val+j.val+k.val ≤ 2 → quadruples i.val j.val k.val (2-i.val-j.val-k.val) = true := by decide +kernel
theorem quad3 : ∀ i j k : Fin 4, i.val+j.val+k.val ≤ 3 → quadruples i.val j.val k.val (3-i.val-j.val-k.val) = true := by decide +kernel
theorem quad4 : ∀ i j k : Fin 5, i.val+j.val+k.val ≤ 4 → quadruples i.val j.val k.val (4-i.val-j.val-k.val) = true := by decide +kernel
theorem quad5 : ∀ i j k : Fin 6, i.val+j.val+k.val ≤ 5 → quadruples i.val j.val k.val (5-i.val-j.val-k.val) = true := by decide +kernel
theorem quad6 : ∀ i j k : Fin 7, i.val+j.val+k.val ≤ 6 → quadruples i.val j.val k.val (6-i.val-j.val-k.val) = true := by decide +kernel
theorem quad7 : ∀ i j k : Fin 8, i.val+j.val+k.val ≤ 7 → quadruples i.val j.val k.val (7-i.val-j.val-k.val) = true := by decide +kernel
private theorem q00 : ∀ k : Fin 9, 0+0+k.val ≤ 8 →
    quadruples 0 0 k.val (8-0-0-k.val) = true := by decide +kernel
private theorem q01 : ∀ k : Fin 9, 0+1+k.val ≤ 8 →
    quadruples 0 1 k.val (8-0-1-k.val) = true := by decide +kernel
private theorem q02 : ∀ k : Fin 9, 0+2+k.val ≤ 8 →
    quadruples 0 2 k.val (8-0-2-k.val) = true := by decide +kernel
private theorem q03 : ∀ k : Fin 9, 0+3+k.val ≤ 8 →
    quadruples 0 3 k.val (8-0-3-k.val) = true := by decide +kernel
private theorem q04 : ∀ k : Fin 9, 0+4+k.val ≤ 8 →
    quadruples 0 4 k.val (8-0-4-k.val) = true := by decide +kernel
private theorem q05 : ∀ k : Fin 9, 0+5+k.val ≤ 8 →
    quadruples 0 5 k.val (8-0-5-k.val) = true := by decide +kernel
private theorem q06 : ∀ k : Fin 9, 0+6+k.val ≤ 8 →
    quadruples 0 6 k.val (8-0-6-k.val) = true := by decide +kernel
private theorem q07 : ∀ k : Fin 9, 0+7+k.val ≤ 8 →
    quadruples 0 7 k.val (8-0-7-k.val) = true := by decide +kernel
private theorem q08 : ∀ k : Fin 9, 0+8+k.val ≤ 8 →
    quadruples 0 8 k.val (8-0-8-k.val) = true := by decide +kernel

private theorem q10 : ∀ k : Fin 9, 1+0+k.val ≤ 8 →
    quadruples 1 0 k.val (8-1-0-k.val) = true := by decide +kernel
private theorem q11 : ∀ k : Fin 9, 1+1+k.val ≤ 8 →
    quadruples 1 1 k.val (8-1-1-k.val) = true := by decide +kernel
private theorem q12 : ∀ k : Fin 9, 1+2+k.val ≤ 8 →
    quadruples 1 2 k.val (8-1-2-k.val) = true := by decide +kernel
private theorem q13 : ∀ k : Fin 9, 1+3+k.val ≤ 8 →
    quadruples 1 3 k.val (8-1-3-k.val) = true := by decide +kernel
private theorem q14 : ∀ k : Fin 9, 1+4+k.val ≤ 8 →
    quadruples 1 4 k.val (8-1-4-k.val) = true := by decide +kernel
private theorem q15 : ∀ k : Fin 9, 1+5+k.val ≤ 8 →
    quadruples 1 5 k.val (8-1-5-k.val) = true := by decide +kernel
private theorem q16 : ∀ k : Fin 9, 1+6+k.val ≤ 8 →
    quadruples 1 6 k.val (8-1-6-k.val) = true := by decide +kernel
private theorem q17 : ∀ k : Fin 9, 1+7+k.val ≤ 8 →
    quadruples 1 7 k.val (8-1-7-k.val) = true := by decide +kernel

private theorem q20 : ∀ k : Fin 9, 2+0+k.val ≤ 8 →
    quadruples 2 0 k.val (8-2-0-k.val) = true := by decide +kernel
private theorem q21 : ∀ k : Fin 9, 2+1+k.val ≤ 8 →
    quadruples 2 1 k.val (8-2-1-k.val) = true := by decide +kernel
private theorem q22 : ∀ k : Fin 9, 2+2+k.val ≤ 8 →
    quadruples 2 2 k.val (8-2-2-k.val) = true := by decide +kernel
private theorem q23 : ∀ k : Fin 9, 2+3+k.val ≤ 8 →
    quadruples 2 3 k.val (8-2-3-k.val) = true := by decide +kernel
private theorem q24 : ∀ k : Fin 9, 2+4+k.val ≤ 8 →
    quadruples 2 4 k.val (8-2-4-k.val) = true := by decide +kernel
private theorem q25 : ∀ k : Fin 9, 2+5+k.val ≤ 8 →
    quadruples 2 5 k.val (8-2-5-k.val) = true := by decide +kernel
private theorem q26 : ∀ k : Fin 9, 2+6+k.val ≤ 8 →
    quadruples 2 6 k.val (8-2-6-k.val) = true := by decide +kernel

private theorem q30 : ∀ k : Fin 9, 3+0+k.val ≤ 8 →
    quadruples 3 0 k.val (8-3-0-k.val) = true := by decide +kernel
private theorem q31 : ∀ k : Fin 9, 3+1+k.val ≤ 8 →
    quadruples 3 1 k.val (8-3-1-k.val) = true := by decide +kernel
private theorem q32 : ∀ k : Fin 9, 3+2+k.val ≤ 8 →
    quadruples 3 2 k.val (8-3-2-k.val) = true := by decide +kernel
private theorem q33 : ∀ k : Fin 9, 3+3+k.val ≤ 8 →
    quadruples 3 3 k.val (8-3-3-k.val) = true := by decide +kernel
private theorem q34 : ∀ k : Fin 9, 3+4+k.val ≤ 8 →
    quadruples 3 4 k.val (8-3-4-k.val) = true := by decide +kernel
private theorem q35 : ∀ k : Fin 9, 3+5+k.val ≤ 8 →
    quadruples 3 5 k.val (8-3-5-k.val) = true := by decide +kernel

private theorem q40 : ∀ k : Fin 9, 4+0+k.val ≤ 8 →
    quadruples 4 0 k.val (8-4-0-k.val) = true := by decide +kernel
private theorem q41 : ∀ k : Fin 9, 4+1+k.val ≤ 8 →
    quadruples 4 1 k.val (8-4-1-k.val) = true := by decide +kernel
private theorem q42 : ∀ k : Fin 9, 4+2+k.val ≤ 8 →
    quadruples 4 2 k.val (8-4-2-k.val) = true := by decide +kernel
private theorem q43 : ∀ k : Fin 9, 4+3+k.val ≤ 8 →
    quadruples 4 3 k.val (8-4-3-k.val) = true := by decide +kernel
private theorem q44 : ∀ k : Fin 9, 4+4+k.val ≤ 8 →
    quadruples 4 4 k.val (8-4-4-k.val) = true := by decide +kernel

private theorem q50 : ∀ k : Fin 9, 5+0+k.val ≤ 8 →
    quadruples 5 0 k.val (8-5-0-k.val) = true := by decide +kernel
private theorem q51 : ∀ k : Fin 9, 5+1+k.val ≤ 8 →
    quadruples 5 1 k.val (8-5-1-k.val) = true := by decide +kernel
private theorem q52 : ∀ k : Fin 9, 5+2+k.val ≤ 8 →
    quadruples 5 2 k.val (8-5-2-k.val) = true := by decide +kernel
private theorem q53 : ∀ k : Fin 9, 5+3+k.val ≤ 8 →
    quadruples 5 3 k.val (8-5-3-k.val) = true := by decide +kernel

private theorem q60 : ∀ k : Fin 9, 6+0+k.val ≤ 8 →
    quadruples 6 0 k.val (8-6-0-k.val) = true := by decide +kernel
private theorem q61 : ∀ k : Fin 9, 6+1+k.val ≤ 8 →
    quadruples 6 1 k.val (8-6-1-k.val) = true := by decide +kernel
private theorem q62 : ∀ k : Fin 9, 6+2+k.val ≤ 8 →
    quadruples 6 2 k.val (8-6-2-k.val) = true := by decide +kernel

private theorem q70 : ∀ k : Fin 9, 7+0+k.val ≤ 8 →
    quadruples 7 0 k.val (8-7-0-k.val) = true := by decide +kernel
private theorem q71 : ∀ k : Fin 9, 7+1+k.val ≤ 8 →
    quadruples 7 1 k.val (8-7-1-k.val) = true := by decide +kernel

private theorem q80 : ∀ k : Fin 9, 8+0+k.val ≤ 8 →
    quadruples 8 0 k.val (8-8-0-k.val) = true := by decide +kernel

private theorem first0 : ∀ j k : Fin 9, 0+j.val+k.val ≤ 8 →
    quadruples 0 j.val k.val (8-0-j.val-k.val) = true := by
  intro j
  fin_cases j
  · exact q00
  · exact q01
  · exact q02
  · exact q03
  · exact q04
  · exact q05
  · exact q06
  · exact q07
  · exact q08

private theorem first1 : ∀ j k : Fin 9, 1+j.val+k.val ≤ 8 →
    quadruples 1 j.val k.val (8-1-j.val-k.val) = true := by
  intro j
  fin_cases j
  · exact q10
  · exact q11
  · exact q12
  · exact q13
  · exact q14
  · exact q15
  · exact q16
  · exact q17
  · decide +kernel

private theorem first2 : ∀ j k : Fin 9, 2+j.val+k.val ≤ 8 →
    quadruples 2 j.val k.val (8-2-j.val-k.val) = true := by
  intro j
  fin_cases j
  · exact q20
  · exact q21
  · exact q22
  · exact q23
  · exact q24
  · exact q25
  · exact q26
  · decide +kernel
  · decide +kernel

private theorem first3 : ∀ j k : Fin 9, 3+j.val+k.val ≤ 8 →
    quadruples 3 j.val k.val (8-3-j.val-k.val) = true := by
  intro j
  fin_cases j
  · exact q30
  · exact q31
  · exact q32
  · exact q33
  · exact q34
  · exact q35
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem first4 : ∀ j k : Fin 9, 4+j.val+k.val ≤ 8 →
    quadruples 4 j.val k.val (8-4-j.val-k.val) = true := by
  intro j
  fin_cases j
  · exact q40
  · exact q41
  · exact q42
  · exact q43
  · exact q44
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem first5 : ∀ j k : Fin 9, 5+j.val+k.val ≤ 8 →
    quadruples 5 j.val k.val (8-5-j.val-k.val) = true := by
  intro j
  fin_cases j
  · exact q50
  · exact q51
  · exact q52
  · exact q53
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem first6 : ∀ j k : Fin 9, 6+j.val+k.val ≤ 8 →
    quadruples 6 j.val k.val (8-6-j.val-k.val) = true := by
  intro j
  fin_cases j
  · exact q60
  · exact q61
  · exact q62
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem first7 : ∀ j k : Fin 9, 7+j.val+k.val ≤ 8 →
    quadruples 7 j.val k.val (8-7-j.val-k.val) = true := by
  intro j
  fin_cases j
  · exact q70
  · exact q71
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem first8 : ∀ j k : Fin 9, 8+j.val+k.val ≤ 8 →
    quadruples 8 j.val k.val (8-8-j.val-k.val) = true := by
  intro j
  fin_cases j
  · exact q80
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem quad8 : ∀ i j k : Fin 9, i.val+j.val+k.val ≤ 8 → quadruples i.val j.val k.val (8-i.val-j.val-k.val) = true := by
  intro i
  fin_cases i
  · exact first0
  · exact first1
  · exact first2
  · exact first3
  · exact first4
  · exact first5
  · exact first6
  · exact first7
  · exact first8

theorem sample_valid : ∀ i : Fin 9, validWitness i.val = true := by decide +kernel
theorem recognized_counts : ([4,5,6,7,8,9,10,11,12].map fun n => (recognized n).length) =
  [1,1,1,3,7,19,51,132,307] := by decide +kernel

end Recognition.StackedCensus
