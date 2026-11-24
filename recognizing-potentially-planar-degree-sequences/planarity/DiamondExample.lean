import TraceDeterminant
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace Recognition.DiamondExample

open LeanPool.K5MinorFreeChoosability TraceRotationFibre
open scoped BigOperators

abbrev row : List Nat := [3,3,2,2]
abbrev V := Fin 4
abbrev Flags := Fin 6 → Bool

/-- Index the six unordered pairs in lexicographic order. -/
private def index (i j : V) : Fin 6 :=
  if i = 0 then if j = 1 then 0 else if j = 2 then 1 else 2
  else if i = 1 then if j = 2 then 3 else 4 else 5

def bitsGraph (a : Flags) : SimpleGraph V where
  Adj i j := i ≠ j ∧ a (index (min i j) (max i j)) = true
  symm := ⟨by intro i j h; simpa [ne_comm,min_comm,max_comm] using h⟩
  loopless := ⟨by simp⟩

instance (a : Flags) : DecidableRel (bitsGraph a).Adj := fun i j =>
  inferInstanceAs (Decidable (i ≠ j ∧ a (index (min i j) (max i j)) = true))

def args : Fin 6 → V × V := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

noncomputable def labelled : Flags ≃ SimpleGraph V where
  toFun := bitsGraph
  invFun := fun G k => @decide (G.Adj (args k).1 (args k).2) (Classical.propDecidable _)
  left_inv := by
    intro a
    funext k
    fin_cases k <;> simp [args, bitsGraph, index]
  right_inv := by
    classical
    intro G
    ext i j
    fin_cases i <;> fin_cases j <;> simp [args,bitsGraph,index,SimpleGraph.adj_comm] <;> exact G.adj_comm _ _

def diamondFlags : Flags := ![true,true,true,true,true,false]
abbrev diamond := bitsGraph diamondFlags

def degreesOK (a : Flags) := ∀ i : V, (bitsGraph a).degree i = row[i.val]
instance (a : Flags) : Decidable (degreesOK a) :=
  inferInstanceAs (Decidable (∀ i : V, (bitsGraph a).degree i = row[i.val]))

set_option maxRecDepth 100000 in
private theorem degreeTest : ∀ a : Flags, degreesOK a ↔ a = diamondFlags := by decide +kernel

theorem unique_graph (G : SimpleGraph V)
    (deg : ∀ i : V, Nat.card {j // G.Adj i j} = row[i.val]) : G = diamond := by
  obtain ⟨a,rfl⟩ := labelled.surjective G
  change bitsGraph a = diamond
  apply congrArg bitsGraph
  apply (degreeTest a).mp
  intro i
  have hi : Nat.card ((bitsGraph a).neighborSet i) = row[i.val] := deg i
  simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using hi

private def eligible (a : Flags) := (∀ k, a k = true → diamondFlags k = true) ∧
  (bitsGraph a).Connected ∧ (bitsGraph a).edgeFinset.card + 1 = 4
private instance (a : Flags) : Decidable (eligible a) :=
  inferInstanceAs (Decidable ((∀ k, a k = true → diamondFlags k = true) ∧
    (bitsGraph a).Connected ∧ (bitsGraph a).edgeFinset.card + 1 = 4))

private theorem flags_le (a b : Flags) : bitsGraph a ≤ bitsGraph b ↔ ∀ k, a k = true → b k = true := by
  constructor
  · intro sub k hk
    have recover (c : Flags) (t : Fin 6) :
        (bitsGraph c).Adj (args t).1 (args t).2 ↔ c t = true := by
      fin_cases t <;> simp [bitsGraph,index,args]
    exact (recover b k).mp (sub ((recover a k).mpr hk))
  · intro h i j adj
    exact ⟨adj.1,h _ adj.2⟩

private theorem eligible_iff (a : Flags) : eligible a ↔ bitsGraph a ∈ MatrixTreeWeight.trees diamond := by
  have mem (T H : SimpleGraph V) : T ∈ MatrixTreeWeight.trees H ↔ T ≤ H ∧ T.IsTree := by
    classical
    simp [MatrixTreeWeight.trees]
  rw [mem,flags_le,SimpleGraph.isTree_iff_connected_and_card]
  have ec : Nat.card (bitsGraph a).edgeSet = (bitsGraph a).edgeFinset.card := by
    rw [SimpleGraph.edgeFinset_card,Nat.card_eq_fintype_card]
  rw [ec,Nat.card_fin]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem treeTest : (Finset.univ.filter eligible).card = 8 := by decide +kernel

theorem tree_count : (MatrixTreeWeight.trees diamond).card = 8 := by
  rw [←treeTest]
  apply Eq.symm
  apply Finset.card_bij' (fun a _ => bitsGraph a) (fun G _ => labelled.symm G)
  · intro a ha
    exact (eligible_iff a).mp (Finset.mem_filter.mp ha).2
  · intro G hG
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,(eligible_iff _).mpr (by simpa only [←show labelled.toFun=bitsGraph from rfl,Equiv.toFun_as_coe,Equiv.apply_symm_apply] using hG)⟩
  · intro a _
    exact labelled.symm_apply_apply a
  · intro G _
    exact labelled.apply_symm_apply G

end Recognition.DiamondExample
