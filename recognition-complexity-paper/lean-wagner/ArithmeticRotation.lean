import PackedMinor
import Mathlib.Algebra.BigOperators.Fin
import SphericalTerm
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # The spherical exponent in the arithmetic test

The variables attached to dart ends are constant on the cycles of the face
permutation. The extremal exponent and its positivity are derived here from
arbitrary rotations. The determinant and differential-operator expansion
that supplies the graph weights is separate. -/
namespace Recognition.ArithmeticRotation
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability
open scoped BigOperators

/-- Assignments satisfying the trace-index identifications are exactly
colourings of permutation cycles. -/
noncomputable def cycleAssignments {D : Type*} (φ : Perm D) (q : Nat) :
    {a : D → Fin q // ∀ d, a d = a (φ d)} ≃ (Quotient (SameCycle.setoid φ) → Fin q) where
  toFun a := Quotient.lift a.val (fun x y h => sameCycle_of_step (Setoid.ker a.val) a.property h)
  invFun b := ⟨fun d => b (Quotient.mk _ d),fun d => congrArg b (Quotient.sound (show SameCycle φ d (φ d) from ⟨1,by simp⟩))⟩
  left_inv _ := rfl
  right_inv b := funext fun x => Quotient.inductionOn x (fun _ => rfl)

theorem assignment_count {D : Type*} [Finite D] (φ : Perm D) (q : Nat) :
    Nat.card {a : D → Fin q // ∀ d, a d = a (φ d)} = q ^ cycleCount φ := by
  rw [Nat.card_congr (cycleAssignments φ q),Nat.card_fun,Nat.card_fin]
  rfl

/-- Multiplying the edge permutation by a transposition changes each
of the two relevant cycle counts by one, preserving defect parity. -/
theorem defect_even {D : Type*} [Finite D] (σ α : Perm D) : eulerDefect σ α % 2 = 0 := by
  classical
  induction hm : Nat.card D - cycleCount α using Nat.strong_induction_on generalizing α with
  | _ m ih =>
    by_cases identity : α = 1
    · simp [identity,eulerDefect_one_right]
    obtain ⟨z,hz⟩ : ∃ z, α z ≠ z := by
      by_contra! h
      exact identity (Equiv.ext h)
    have sc : SameCycle α z (α z) := ⟨1,by simp⟩
    have split := cycleCount_mul_swap_of_sameCycle (Ne.symm hz) sc
    have bound := cycleCount_le_card (α * swap z (α z))
    have step := ih (Nat.card D - cycleCount (α * swap z (α z))) (by omega) _ rfl
    unfold eulerDefect at step ⊢
    rw [←mul_assoc,split] at step
    by_cases h : SameCycle (σ*α) z (α z)
    · rw [cycleCount_mul_swap_of_sameCycle (Ne.symm hz) h] at step
      omega
    · have joined := cycleCount_mul_swap_of_not_sameCycle h
      omega

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance : Finite G.Dart := by
  classical
  let := Fintype.ofFinite V
  infer_instance

abbrev Rotation := {σ : Perm G.Dart // IsRotationSystem G σ}

noncomputable def exponent (r : Rotation G) := cycleCount (r.val * dartSymm G)
noncomputable def spherePower := Nat.card G.edgeSet + 2 - Nat.card V
noncomputable def genus (r : Rotation G) := (eulerDefect r.val (dartSymm G)).toNat / 2

private theorem euler (r : Rotation G) (conn : G.Connected) (positive : ∀ v, ∃ w, G.Adj v w) :
    (Nat.card V : ℤ) + exponent G r + eulerDefect r.val (dartSymm G) = Nat.card G.edgeSet + 2 := by
  have vert : cycleCount r.val = Nat.card V := by
    rw [cycleCount_eq_card_nonisolated r.property]
    exact Nat.card_congr ⟨Subtype.val,fun x => ⟨x,positive x⟩,fun _ => rfl,fun _ => rfl⟩
  let first := Classical.choice conn.nonempty
  obtain ⟨y,hy⟩ := positive first
  let : Nonempty G.Dart := ⟨⟨(first,y),hy⟩⟩
  have one := Nat.le_antisymm (numComponents_le_one_of_connected r.property conn)
    (one_le_numComponents r.val (dartSymm G))
  unfold exponent eulerDefect
  rw [one,vert,card_dart_eq_two_mul,←card_edgeSet_eq_cycleCount]
  push_cast
  ring

/-- For every rotation of a connected graph without isolated vertices, the
face-colour exponent is the spherical exponent minus twice the genus. -/
theorem exponent_genus (r : Rotation G) (conn : G.Connected) (positive : ∀ v, ∃ w, G.Adj v w) :
    exponent G r + 2 * genus G r = spherePower G := by
  have count := euler G r conn positive
  have non := eulerDefect_nonneg r.val (dartSymm G)
  have even := defect_even r.val (dartSymm G)
  unfold genus spherePower
  omega

theorem exponent_spherical (r : Rotation G) (conn : G.Connected) (positive : ∀ v, ∃ w, G.Adj v w) :
    exponent G r = spherePower G ↔ ∃ M : PlaneMap G, M.rot=r.val := by
  have count := euler G r conn positive
  have non := eulerDefect_nonneg r.val (dartSymm G)
  unfold spherePower
  constructor
  · intro eq
    exact ⟨⟨r.val,r.property,by omega⟩,rfl⟩
  · rintro ⟨M,hm⟩
    have zero := hm ▸ M.eulerDefect_eq_zero
    omega

/-- The rotation polynomial allows an arbitrary positive integer weight
for each rotation of this graph. -/
noncomputable def inventory (w : Rotation G → Nat) : Polynomial ℤ := by
  classical
  let := Fintype.ofFinite (Rotation G)
  exact ∑ r : Rotation G, Polynomial.monomial (exponent G r) (w r : ℤ)

private theorem coefficient (w : Rotation G → Nat) (i : Nat) :
    (inventory G w).coeff i = (∑ r ∈ @Finset.univ _ (Fintype.ofFinite (Rotation G)),
      if exponent G r = i then (w r : ℤ) else 0) := by
  classical
  let := Fintype.ofFinite (Rotation G)
  simp [inventory,Polynomial.finsetSum_coeff,Polynomial.coeff_monomial,eq_comm]

/-- The extremal coefficient of the actual sum over rotations detects
planarity of the connected graph. -/
theorem positive_top_iff (w : Rotation G → Nat) (weight : ∀ r, 0 < w r)
    (conn : G.Connected) (positive : ∀ v, ∃ u, G.Adj v u) :
    0 < (inventory G w).coeff (spherePower G) ↔ IsPlanar G := by
  classical
  let := Fintype.ofFinite (Rotation G)
  rw [coefficient]
  constructor
  · intro pos
    by_contra none
    have all (r : Rotation G) : exponent G r ≠ spherePower G := by
      intro hit
      obtain ⟨M,_⟩ := (exponent_spherical G r conn positive).mp hit
      exact none ⟨M⟩
    simp [all] at pos
  · rintro ⟨M⟩
    let r : Rotation G := ⟨M.rot,M.isRotationSystem⟩
    have hit := (exponent_spherical G r conn positive).mpr ⟨M,rfl⟩
    exact Finset.sum_pos' (fun x _ => by split <;> positivity)
      ⟨r,Finset.mem_univ _, by simpa [hit] using (show (0:ℤ)<w r by exact_mod_cast weight r)⟩

/-- The alternating test, including its degree bound, specializes to the
rotation polynomial of each connected graph without isolated vertices. -/
theorem difference_iff (w : Rotation G → Nat) (weight : ∀ r, 0 < w r)
    (conn : G.Connected) (positive : ∀ v, ∃ u, G.Adj v u) :
    0 < SphericalTerm.alternating (inventory G w) (spherePower G) ↔ IsPlanar G := by
  have bound : (inventory G w).natDegree ≤ spherePower G := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coefficient]
    apply Finset.sum_eq_zero
    intro r _
    have degree := exponent_genus G r conn positive
    exact ite_eq_right (by omega)
  exact (SphericalTerm.positive_iff _ _ bound).trans (positive_top_iff G w weight conn positive)

/-! ## The sum over all labelled connected realizations -/

abbrev ConnectedRealization (ds : List Nat) := {G : SimpleGraph (Fin ds.length) //
  G.Connected ∧ ∀ i : Fin ds.length, Nat.card {j // G.Adj i j} = ds[i.val]}

private theorem row_neighbour (ds : List Nat) (positive : ∀ d ∈ ds, 0 < d)
    (G : ConnectedRealization ds) : ∀ i, ∃ j, G.val.Adj i j := by
  intro i
  have nonzero : 0 < Nat.card {j // G.val.Adj i j} := (G.property.2 i) ▸ positive _ (List.getElem_mem i.isLt)
  obtain ⟨j,h⟩ := (Nat.card_pos_iff.mp nonzero).1
  exact ⟨j,h⟩

private theorem row_power (ds : List Nat) (G : ConnectedRealization ds) :
    spherePower G.val = ds.sum / 2 + 2 - ds.length := by
  classical
  have each (i : Fin ds.length) : G.val.degree i = ds[i.val] := by
    rw [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
    exact G.property.2 i
  have twice := G.val.sum_degrees_eq_twice_card_edges
  simp_rw [each] at twice
  have sum : (∑ i : Fin ds.length, ds[i.val]) = ds.sum := by
    rw [←List.sum_ofFn]
    congr 1
    apply List.ext_getElem <;> simp
  rw [sum,SimpleGraph.edgeFinset_card] at twice
  unfold spherePower
  rw [Nat.card_fin,Nat.card_eq_fintype_card]
  omega

/-- A polynomial formed from the prescribed degrees alone, up to the
choice of positive graph/rotation weights. It sums over every connected
simple realization and every rotation on its labelled darts. -/
noncomputable def rowInventory (ds : List Nat)
    (w : (G : ConnectedRealization ds) → Rotation G.val → Nat) : Polynomial ℤ := by
  classical
  let := Fintype.ofFinite (ConnectedRealization ds)
  exact ∑ G : ConnectedRealization ds, inventory G.val (w G)

/-- The row's own Euler count gives the cutoff for the finite difference.
Its positivity is equivalent to existence of a connected planar realization
of those labelled degrees. -/
theorem row_difference_iff (ds : List Nat) (positive : ∀ d ∈ ds, 0 < d)
    (w : (G : ConnectedRealization ds) → Rotation G.val → Nat) (weight : ∀ G r, 0 < w G r) :
    0 < SphericalTerm.alternating (rowInventory ds w) (ds.sum / 2 + 2 - ds.length) ↔
      ∃ G : ConnectedRealization ds, IsPlanar G.val := by
  classical
  let := Fintype.ofFinite (ConnectedRealization ds)
  let f := ds.sum / 2 + 2 - ds.length
  have top G : 0 < (inventory G.val (w G)).coeff f ↔ IsPlanar G.val :=
    by simpa only [row_power,f] using positive_top_iff G.val (w G) (weight G) G.property.1 (row_neighbour ds positive G)
  have coeff (i : Nat) : (rowInventory ds w).coeff i = ∑ G : ConnectedRealization ds, (inventory G.val (w G)).coeff i := by
    simp [rowInventory,Polynomial.finsetSum_coeff]
  have upper : (rowInventory ds w).natDegree ≤ f := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff]
    apply Finset.sum_eq_zero
    intro G _
    rw [coefficient]
    apply Finset.sum_eq_zero
    intro r _
    have exp := exponent_genus G.val r G.property.1 (row_neighbour ds positive G)
    rw [row_power ds G] at exp
    change f < i at hi
    change _ = f at exp
    exact ite_eq_right (by omega)
  rw [SphericalTerm.positive_iff _ _ upper,coeff]
  have non (G : ConnectedRealization ds) : 0 ≤ (inventory G.val (w G)).coeff f := by
    rw [coefficient]
    apply Finset.sum_nonneg
    intro _ _
    split <;> positivity
  constructor
  · intro hit
    by_contra! none
    have zero (G : ConnectedRealization ds) : (inventory G.val (w G)).coeff f = 0 := by
      have reject := fun h => none G ((top G).mp h)
      exact le_antisymm (le_of_not_gt reject) (non G)
    change 0 < ∑ G : ConnectedRealization ds, (inventory G.val (w G)).coeff f at hit
    simp [zero] at hit
  · rintro ⟨G,planar⟩
    exact Finset.sum_pos' (fun H _ => non H) ⟨G,Finset.mem_univ _,(top G).mpr planar⟩

end Recognition.ArithmeticRotation
