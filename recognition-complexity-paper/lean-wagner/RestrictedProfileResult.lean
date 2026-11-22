import GraphCounts
import SparseBoundary.BranchDegree
import SparseBoundary.InteriorRepairs
import SparseBoundary.TruncationBuild

/-! Exact recognition with one designated centre and leaves, and propagation
of positive certificates for degree lists supported on three and seven. -/
namespace Recognition.RestrictedProfile
open SparseBoundary Recognition.Wagner

private theorem graphic_even_sum {d : List Nat} (h : Graphic d) : d.sum % 2 = 0 := by
  classical
  obtain ⟨G, degrees⟩ := h
  have count := (toSimple G).sum_degrees_eq_twice_card_edges
  have each (i : Fin d.length) : (toSimple G).degree i = d[i] := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact (neighbor_count G i).trans (degrees i)
  simp_rw [each] at count
  have listSum : (∑ i : Fin d.length, d[i]) = d.sum := by
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem <;> simp
  rw [listSum] at count
  omega

private theorem star (q : Nat) : Planaric (q :: List.replicate q 1) := by
  induction q with
  | zero =>
    let Z : Graph 1 := ⟨0⟩
    exact ⟨Z, by unfold Graph.Realizes; decide, Graph.planar_of_few_high Z (by decide)⟩
  | succ q ih =>
    let d := q :: List.replicate q 1
    let center : Fin d.length := ⟨0, by simp [d]⟩
    have next := planaric_attach_leaf ih center
    have row : List.ofFn (fun i : Fin d.length => d[i] + (if i = center then 1 else 0)) =
        (q+1) :: List.replicate q 1 := by
      rw [List.ofFn_succ]
      congr 1
      · simp [center, d]
    change Planaric (1 :: List.ofFn (fun i : Fin d.length => d[i] + (if i = center then 1 else 0))) at next
    rw [row] at next
    simpa [List.replicate_succ] using (planaric_perm (List.Perm.swap _ _ _)).mp next

/-- For a prescribed centre and otherwise only leaves, the degree bound
and parity suffice. Both hold for zero leaves and an isolated centre. -/
theorem one_center_leaves_iff (q r : Nat) :
    Planaric (q :: List.replicate r 1) ↔ q ≤ r ∧ (q+r)%2=0 := by
  constructor
  · intro yes
    have gra := planaric_graphic yes
    have cap := graphic_degree_lt gra q (by simp)
    have even := graphic_even_sum gra
    simpa [List.sum_replicate_nat, Nat.add_comm] using
      (show q < (q :: List.replicate r 1).length ∧ (q :: List.replicate r 1).sum%2=0 from ⟨cap,even⟩)
  · rintro ⟨cap,even⟩
    have pad (k : Nat) : Planaric (q :: List.replicate (q + 2*k) 1) := by
      induction k with
      | zero => simpa using star q
      | succ k ih =>
        have edge : Planaric (List.replicate 2 1) := star 1
        have join := planaric_append ih edge
        rw [show q + 2*(k+1) = (q+2*k)+2 by omega, List.replicate_add]
        exact join
    have lengthEq : q + 2*((r-q)/2) = r := by omega
    simpa only [lengthEq] using pad ((r-q)/2)

/-- Truncating a degree-three vertex increases its multiplicity by two
and keeps the other degrees. Iteration fills the parity ray above a seed. -/
theorem threes_sevens_fill {r h : Nat} (positive : 0 < r)
    (seed : Planaric (List.replicate r 3 ++ List.replicate h 7)) (k : Nat) :
    Planaric (List.replicate (r+2*k) 3 ++ List.replicate h 7) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  induction k with
  | zero => simpa using seed
  | succ k ih =>
    have first : Planaric (3 :: (List.replicate (s+2*k) 3 ++ List.replicate h 7)) := by
      simpa [Nat.succ_add, List.replicate_succ] using ih
    have enlarged := Truncation.truncate_profile first
    rw [show (s+1)+2*(k+1) = ((s+2*k)+1)+1+1 by omega]
    simpa only [List.replicate_succ, List.cons_append] using enlarged

/-- The seven-cycle with an apex and the join of a single edge with three
independent edges provide the least seeds with one and two sevens. The
last label is an apex in each packed graph. -/
private theorem few_sevens_seeds :
    Planaric (List.replicate 7 3 ++ List.replicate 1 7) ∧
    Planaric (List.replicate 6 3 ++ List.replicate 2 7) := by
  let wheel : Graph 8 := ⟨267436581⟩
  let doubleFan : Graph 8 := ⟨268419105⟩
  constructor
  · exact ⟨wheel, by unfold Graph.Realizes; decide,
      RimGrowth.ordered_planar (G := wheel) (by unfold RimGrowth.Ordered; decide)⟩
  · exact ⟨doubleFan, by unfold Graph.Realizes; decide,
      RimGrowth.ordered_planar (G := doubleFan) (by unfold RimGrowth.Ordered; decide)⟩

/-- Complete recognition for three/seven lists with one or two sevens.
Degree seven forces order at least eight. The handshaking condition and
that lower bound are sufficient throughout these two parity rays. -/
theorem one_two_sevens_iff (r h : Nat) (few : h=1 ∨ h=2) :
    Planaric (List.replicate r 3 ++ List.replicate h 7) ↔
      8 ≤ r+h ∧ r%2=h%2 := by
  constructor
  · intro yes
    have gra := planaric_graphic yes
    have high : 7 ∈ List.replicate r 3 ++ List.replicate h 7 := by
      rcases few with rfl|rfl <;> simp
    have cap := graphic_degree_lt gra 7 high
    have parity := graphic_even_sum gra
    simp only [List.length_append, List.length_replicate] at cap
    simp only [List.sum_append, List.sum_replicate_nat] at parity
    omega
  · rintro ⟨cap, parity⟩
    rcases few with rfl|rfl
    · have fill := threes_sevens_fill (by decide) few_sevens_seeds.1 ((r-7)/2)
      simpa only [show 7+2*((r-7)/2)=r by omega] using fill
    · have fill := threes_sevens_fill (by decide) few_sevens_seeds.2 ((r-6)/2)
      simpa only [show 6+2*((r-6)/2)=r by omega] using fill

end Recognition.RestrictedProfile
