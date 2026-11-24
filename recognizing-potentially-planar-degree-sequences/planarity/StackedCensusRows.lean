import StackedQuota
import Mathlib.Data.List.Nodup

namespace Recognition.StackedCensus

/-- Descending lists of length k, of prescribed sum, with entries in [3,top].
The feasibility test prunes a branch before allocating its suffix. -/
def rows : Nat → Nat → Nat → List (List Nat)
  | 0, _, s => if s = 0 then [[]] else []
  | k+1,top,s => if 3*(k+1) ≤ s ∧ s ≤ top*(k+1) then
      (List.range (min top s + 1)).flatMap fun d => if 3 ≤ d then
        (rows k d (s-d)).map (d :: ·) else []
    else []

private theorem bounds {d : List Nat} {top : Nat} (h : ∀ j ∈ d, 3 ≤ j ∧ j ≤ top) :
    3*d.length ≤ d.sum ∧ d.sum ≤ top*d.length := by
  induction d with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hl,hu⟩ := h x (by simp)
    obtain ⟨a,b⟩ := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    simp only [List.sum_cons,List.length_cons,Nat.mul_succ]
    omega

theorem rows_iff (k top s : Nat) (d : List Nat) :
    d ∈ rows k top s ↔ d.length=k ∧ d.sum=s ∧
      (∀ j ∈ d, 3 ≤ j ∧ j ≤ top) ∧ d.Pairwise (· ≥ ·) := by
  induction k generalizing top s d with
  | zero =>
    cases d with
    | nil => by_cases h : s=0 <;> simp [rows,h,eq_comm]
    | cons x xs => by_cases h : s=0 <;> simp [rows,h]
  | succ k ih =>
    rw [rows]
    split
    next ok =>
      simp only [List.mem_flatMap,List.mem_range]
      constructor
      · rintro ⟨x,hx,mem⟩
        split at mem
        next lo =>
          obtain ⟨xs,hs,rfl⟩ := List.mem_map.mp mem
          obtain ⟨len,total,each,sort⟩ := (ih _ _ _).mp hs
          have := Nat.min_le_right top s
          have := Nat.min_le_left top s
          refine ⟨by simp [len],by simp [total]; omega,?_,List.pairwise_cons.mpr ⟨fun j hj => (each j hj).2,sort⟩⟩
          intro j hj
          rcases List.mem_cons.mp hj with rfl|hj
          · exact ⟨lo,by omega⟩
          · exact ⟨(each j hj).1,by have := (each j hj).2; omega⟩
        next bad => simp at mem
      · rintro ⟨len,total,each,sort⟩
        cases d with
        | nil => simp at len
        | cons x xs =>
          obtain ⟨rank,sort⟩ := List.pairwise_cons.mp sort
          obtain ⟨lo,hi⟩ := each x (by simp)
          simp only [List.length_cons,Nat.add_right_cancel_iff,List.sum_cons] at len total
          refine ⟨x,by omega,?_⟩
          rw [ite_eq_left lo,List.mem_map]
          exact ⟨xs,(ih _ _ _).mpr ⟨len,by omega,fun j hj =>
            ⟨(each j (List.mem_cons_of_mem _ hj)).1,rank j hj⟩,sort⟩,rfl⟩
    next no =>
      simp only [List.not_mem_nil,false_iff]
      rintro ⟨len,sum,each,_⟩
      have := bounds each
      exact no (by simpa only [len,sum] using this)

theorem rows_nodup (k top s : Nat) : (rows k top s).Nodup := by
  induction k generalizing top s with
  | zero => by_cases h : s=0 <;> simp [rows,h]
  | succ k ih =>
    rw [rows]
    split
    · apply List.nodup_flatMap.mpr
      constructor
      · intro x _
        split
        · apply List.Nodup.map _ (ih _ _)
          intro a b eq
          exact (List.cons.inj eq).2
        · simp
      · apply List.nodup_range.imp
        intro x y ne d hx hy
        dsimp only at hx hy
        by_cases px : 3 ≤ x <;> simp only [px,ite_true,ite_false] at hx <;> try contradiction
        by_cases py : 3 ≤ y <;> simp only [py,ite_true,ite_false] at hy <;> try contradiction
        obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
        obtain ⟨b,_,eq⟩ := List.mem_map.mp hy
        exact ne (List.cons.inj eq).1.symm
    · simp

def candidates (n : Nat) := rows n (n-1) (6*n-12)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem candidate_counts :
    ([4,5,6,7,8,9,10,11,12].map fun n => (candidates n).length) =
      [1,1,4,10,27,66,157,346,738] := by decide +kernel

end Recognition.StackedCensus
