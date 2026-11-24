import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Recognition.CensusEncoding

def code (d : List Nat) := (d.map fun j => 16^j).sum
private def low (d : List Nat) (k : Nat) := (d.map fun j => if j < k then 16^j else 0).sum
private def high (d : List Nat) (k : Nat) := (d.map fun j => if k ≤ j then 16^(j-k) else 0).sum

private theorem splitAt (d : List Nat) (k : Nat) : code d = low d k + 16^k * high d k := by
  induction d with
  | nil => simp [code,low,high]
  | cons j d ih =>
    simp only [code,low,high,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    by_cases h : j < k
    · simp [h,show ¬k≤j by omega,Nat.add_assoc]
    · have a : k+(j-k)=j := by omega
      simp only [ite_eq_right h,ite_eq_left (show k≤j by omega),Nat.zero_add,Nat.mul_add,←Nat.pow_add,a]
      omega

private theorem low_small (d : List Nat) (len : d.length < 16) (k : Nat) : low d k < 16^k := by
  cases k with
  | zero => simp [low]
  | succ k =>
    have bd : low d (k+1) ≤ d.length * 16^k := by
      clear len
      induction d with
      | nil => simp [low]
      | cons j d ih =>
        simp only [low,List.map_cons,List.sum_cons] at ih ⊢
        rw [List.length_cons,Nat.succ_mul]
        split
        · have := Nat.pow_le_pow_right (n:=16) (by decide) (show j≤k by omega)
          omega
        · simp only [Nat.zero_add]
          exact le_trans ih (Nat.le_add_right _ _)
    rw [pow_succ, Nat.mul_comm]
    exact lt_of_le_of_lt bd (Nat.mul_lt_mul_of_pos_right len (by positivity))

private theorem high_step (d : List Nat) (k : Nat) :
    high d k = d.count k + 16 * high d (k+1) := by
  induction d with
  | nil => simp [high]
  | cons j d ih =>
    simp only [high,List.map_cons,List.sum_cons] at ih ⊢
    rw [List.count_cons,ih]
    rcases lt_trichotomy j k with h|rfl|h
    · simp [show ¬k≤j by omega,show ¬k+1≤j by omega,ne_of_lt h]
    · simp only [Nat.le_refl,ite_true,Nat.sub_self,pow_zero,Nat.not_succ_le_self,ite_false,
        Nat.zero_add,beq_self_eq_true]
      omega
    · have a : j-k = j-(k+1)+1 := by omega
      simp only [ite_eq_left (show k≤j by omega),ite_eq_left (show k+1≤j by omega),Nat.mul_add,a,pow_succ]
      simp [ne_of_gt h]
      ring

theorem digit (d : List Nat) (len : d.length < 16) (k : Nat) :
    code d / 16^k % 16 = d.count k := by
  rw [splitAt, Nat.add_mul_div_left _ _ (by positivity),Nat.div_eq_of_lt (low_small d len k),
    Nat.zero_add,high_step,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt]
  exact lt_of_le_of_lt List.count_le_length len

theorem code_iff {d e : List Nat} (hd : d.length<16) (he : e.length<16) :
    code d = code e ↔ d.Perm e := by
  constructor
  · intro eq
    apply List.perm_iff_count.mpr
    intro k
    rw [←digit d hd,←digit e he,eq]
  · intro perm
    exact (perm.map _).sum_eq

end Recognition.CensusEncoding
