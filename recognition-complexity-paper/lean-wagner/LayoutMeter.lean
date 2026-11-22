import LayoutSearch
import LayerCost

/-! Access charges for the subset ordering algorithm. The graph has n
vertices. A scan of the boundary, construction of a prefix set, appending
one vertex, or comparison of prefix sets is charged (n+1)^8 accesses.
The search scans all n extensions and visits only actual first-match cells. -/
namespace Recognition.LayoutMeter
open Recognition.LayoutSearch Recognition.LayerCost StateIso

private def fee (n : Nat) := (n+1)^8
private def rows (n : Nat) := 2^n
private def extensions (A : Colored n) (w : Nat) (xs : List (Fin n)) :=
  (grow A w xs,n*fee n)
private def search (cs : List (List (Fin n))) (S : Finset (Fin n)) :=
  seek (fun xs => (xs.toFinset==S,fee n)) cs

def run (A : Colored n) (w : Nat) : Nat → List (List (Fin n)) × Nat
  | 0 => ([[]],1)
  | k+1 =>
    let (prev,a) := run A w k
    let (cs,b) := expand (extensions A w) prev
    let (out,c) := collect (search cs) (subsets n)
    (out,a+b+c+rows n*fee n+1)

theorem output (A : Colored n) (w k : Nat) : (run A w k).1=pool A w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [run,collect_val,expand_val,extensions,ih,pool,keep,search,seek_val]

private def quota (n : Nat) :=
  rows n*(n*fee n+n+1)+1 + (rows n*(rows n*n*(fee n+1)+2)+1) + rows n*fee n+1

theorem charge (A : Colored n) (w k : Nat) : (run A w k).2≤1+k*quota n := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    let prev := (run A w k).1
    let generated := expand (extensions A w) prev
    have size : prev.length≤rows n := by rw [show prev=(run A w k).1 by rfl,output];exact pool_size ..
    have batch := expand_cost (extensions A w) prev (n*fee n) n (fun _ => le_rfl)
      (fun xs => by simpa [extensions,grow] using List.length_filter_le _ (List.finRange n))
    have a : generated.2≤rows n*(n*fee n+n+1)+1 := batch.1.trans (by gcongr)
    have cs : generated.1.length≤rows n*n := batch.2.trans (by gcongr)
    have b : (collect (search generated.1) (subsets n)).2≤rows n*(rows n*n*(fee n+1)+2)+1 := by
      apply (collect_cost _ _ (rows n*n*(fee n+1)+1) ?_).trans
      · simp [subsets,rows]
      · intro s _
        exact (seek_cost _ _ (fee n) (fun _ _ => le_rfl)).trans (by gcongr)
    change (run A w k).2+generated.2+(collect (search generated.1) (subsets n)).2+rows n*fee n+1≤_
    unfold quota at *
    rw [Nat.succ_mul]
    omega

/-- Exhaustive subset planning takes a single exponential in the graph
order, even when every order is rejected. -/
theorem single_exponential (A : Colored n) (w : Nat) : (run A w n).2≤2^(24*(n+1)) := by
  let q := 2^(n+1)
  have h : n+1≤q := (Nat.lt_two_pow_self (n:=n+1)).le
  have r : rows n≤q := Nat.pow_le_pow_right (by decide) (Nat.le_succ n)
  have f : fee n≤q^8 := Nat.pow_le_pow_left h _
  have nle : n≤q := by omega
  have q2 : 2≤q := Nat.pow_le_pow_right (n:=2) (by decide) (show 1≤n+1 by omega)
  apply (charge A w n).trans
  apply (show 1+n*quota n≤1+q*(q*(q*q^8+q+1)+1+(q*(q*q*(q^8+1)+2)+1)+q*q^8+1) by
    unfold quota;gcongr).trans
  rw [mul_comm 24, Nat.pow_mul]
  change _≤q^24
  obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le q2
  rw [hz]
  ring_nf
  omega

end Recognition.LayoutMeter
