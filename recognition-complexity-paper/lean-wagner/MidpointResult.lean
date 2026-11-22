import ConeLink
import RimInventory
import PolygonCompletion
import MidpointWitnesses

/-! The sorted-entry midpoint obstruction for ordinary labelled simple
graphs. Nonplanarity is deduced from the induced cyclic order at the hub. -/
namespace Recognition.MidpointResult
open SparseBoundary
open scoped BigOperators

abbrev lower : List Nat := [12,7,7,5,5,5,5,5,3,3,3,3,3]
abbrev upper : List Nat := [12,9,5,5,5,5,5,5,3,3,3,3,3]
abbrev middle : List Nat := RimInventory.profile

private theorem chords_noncrossing (G : Graph 13) (rim : List (Fin 13)) (len : rim.length=12)
    (non : ConeLink.NonCrossing (Wagner.toSimple G) rim) :
    PolygonCompletion.Noncrossing fun x y => (x,y) ∈ RimInventory.chords 12 (RimInventory.adjacency G rim) := by
  intro a b c d ab bc cd ac bd
  have E := RimInventory.mem_chords.mp ac
  have F := RimInventory.mem_chords.mp bd
  have ad : a < rim.length := by omega
  have bsize : b < rim.length := by omega
  have csize : c < rim.length := by omega
  have dsize : d < rim.length := by omega
  have attached {i j : Nat} (li : i < rim.length) (lj : j < rim.length)
      (h : RimInventory.adjacency G rim i j = true) :
      (Wagner.toSimple G).Adj (rim.get ⟨i,li⟩) (rim.get ⟨j,lj⟩) := by
    change G.adj rim[i] rim[j] = true
    simpa only [RimInventory.adjacency,List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem li,List.getElem?_eq_getElem lj,Option.getD_some] using h
  exact non ⟨a,ad⟩ ⟨b,bsize⟩ ⟨c,csize⟩ ⟨d,dsize⟩ ab bc cd
    (attached ad csize E.2.2) (attached bsize dsize F.2.2)

/-- The midpoint itself has no simple planar realization. -/
theorem middle_nonplanaric : ¬ Planaric middle := by
  intro yes
  let tail : List Nat := [8,6,5,5,5,5,5,3,3,3,3,3]
  have valid : Reduction.TableValid (tail.length :: tail) := by
    unfold Reduction.TableValid
    decide +kernel
  obtain ⟨G,deg,_,hub,rim,ring,non,len⟩ := ConeLink.table_cone_rim_with_hub tail valid yes
  obtain ⟨nd,bound,number,inventory⟩ := RimInventory.packed G deg rim len ring.1 ring.2.1 hub
  exact PolygonCompletion.exclude_tight_midpoint _ nd bound (chords_noncrossing G rim len non) number inventory

/-- The relevant slice already consists of nonincreasing graphic rows of
order thirteen and even degree sum 66, the triangulation equality. -/
def slice (d : List Nat) := d.length=13 ∧ d.sum=66 ∧ d.Pairwise (· ≥ ·) ∧
  ∃ G : Graph d.length, G.Realizes d

def inequalities {R : Type*} [Field R] [LinearOrder R] {ι : Sort*}
    (a : ι → Fin 13 → R) (bound : ι → R) (d : List Nat) :=
  ∀ j, ∑ i : Fin 13, a j i * (d[i.val]! : R) ≤ bound j

private theorem slice_of {d : List Nat} (h : d.length=13 ∧ d.sum=66 ∧ d.Pairwise (· ≥ ·))
    (real : ∃ G : Graph d.length, G.Realizes d) : slice d := ⟨h.1,h.2.1,h.2.2,real⟩

/-- No family of affine inequalities, even an infinite family, recognizes
planaricity on the Euler-tight graphic slice of sorted degree coordinates. -/
theorem no_affine_characterization {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {ι : Sort*} (a : ι → Fin 13 → R) (bound : ι → R) :
    ¬ ∀ d : List Nat, slice d → (Planaric d ↔ inequalities a bound d) := by
  intro detects
  have lp := MidpointWitnesses.low_planaric
  have hp := MidpointWitnesses.high_planaric
  have l : slice lower := slice_of (by decide +kernel) (by obtain ⟨G,h,_⟩ := lp; exact ⟨G,h⟩)
  have u : slice upper := slice_of (by decide +kernel) (by obtain ⟨G,h,_⟩ := hp; exact ⟨G,h⟩)
  have m : slice middle := slice_of (by decide +kernel) MidpointWitnesses.middle_graphic
  have lo := (detects lower l).mp lp
  have hi := (detects upper u).mp hp
  apply middle_nonplanaric ((detects middle m).mpr ?_)
  intro j
  have coord (i : Fin 13) : (middle[i.val]! : R) + (middle[i.val]! : R) =
      (lower[i.val]! : R) + (upper[i.val]! : R) := by
    have eq : ∀ k : Fin 13, middle[k.val]! + middle[k.val]! = lower[k.val]! + upper[k.val]! := by decide +kernel
    exact_mod_cast eq i
  have midpoint : (∑ i : Fin 13, a j i * (middle[i.val]! : R)) +
      (∑ i : Fin 13, a j i * (middle[i.val]! : R)) =
      (∑ i : Fin 13, a j i * (lower[i.val]! : R)) + (∑ i : Fin 13, a j i * (upper[i.val]! : R)) := by
    rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [←mul_add,←mul_add,coord]
  by_contra! fails
  exact (not_lt_of_ge (midpoint.le.trans (add_le_add (lo j) (hi j)))) (add_lt_add fails fails)

end Recognition.MidpointResult
