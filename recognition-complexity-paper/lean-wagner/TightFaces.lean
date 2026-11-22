import LeanPool.K5MinorFreeChoosability.Planar.Examples
import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar

/-! The equality case of the spherical face bound. Each orbit of an Euler-tight
rotation on a simple graph has exactly three darts, and all darts lie in one component. -/
namespace Recognition.Wagner
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

private theorem exact_class_size {A : Type*} [Finite A] (s : Setoid A) (k : Nat)
    (lo : ∀ a, k ≤ Nat.card {b // s a b}) (mass : k * numClasses s = Nat.card A)
    (a : A) : Nat.card {b // s a b} = k := by
  classical
  let := Fintype.ofFinite A
  let size (q : Quotient s) := (Finset.univ.filter fun b => Quotient.mk s b = q).card
  have eq (v : A) : size (Quotient.mk s v) = Nat.card {b // s v b} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    unfold size
    congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Quotient.eq]
    exact ⟨fun h => s.symm h, fun h => s.symm h⟩
  have lower (q : Quotient s) : k ≤ size q := by
    induction q using Quotient.inductionOn with
    | h v => rw [eq]; exact lo v
  have total := Finset.card_eq_sum_card_fiberwise
    (f := Quotient.mk s) (s := (Finset.univ : Finset A)) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  change Finset.univ.card = ∑ q : Quotient s, size q at total
  by_contra h
  have strict : (∑ _ : Quotient s, k) < ∑ q : Quotient s, size q :=
    Finset.sum_lt_sum (fun i _ => lower i) ⟨Quotient.mk s a, Finset.mem_univ _, by
      rw [eq]; have := lo a; omega⟩
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at strict
  rw [← total, Finset.card_univ] at strict
  rw [numClasses, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at mass
  rw [Nat.mul_comm] at mass
  omega

private theorem period_three {V : Type*} [Finite V] {H : SimpleGraph V}
    (M : PlaneMap H) (minDeg : ∀v, 2 ≤ Nat.card {u // H.Adj v u})
    (size : ∀d, Nat.card {e // SameCycle M.facePerm d e} = 3) (d : H.Dart) :
    M.facePerm (M.facePerm (M.facePerm d)) = d := by
  classical
  let := Fintype.ofFinite V
  let φ := M.facePerm
  have n1 (z) : φ z ≠ z := face_ne_self M.isRotationSystem z
  have n2 (z) : φ (φ z) ≠ z := face_face_ne_self M.isRotationSystem minDeg z
  by_contra n3
  change φ (φ (φ d)) ≠ d at n3
  have lo : 4 ≤ Nat.card {e // SameCycle φ d e} := by
    apply le_natCard_of_list [d,φ d,φ (φ d),φ (φ (φ d))]
    · simp [Ne.symm (n1 d), Ne.symm (n2 d), Ne.symm n3,
        Ne.symm (n1 (φ d)), Ne.symm (n2 (φ d)), Ne.symm (n1 (φ (φ d)))]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact SameCycle.refl .. 
      · exact sameCycle_apply_right.mpr (SameCycle.refl ..)
      · exact sameCycle_apply_right.mpr (sameCycle_apply_right.mpr (SameCycle.refl ..))
      · exact sameCycle_apply_right.mpr (sameCycle_apply_right.mpr
          (sameCycle_apply_right.mpr (SameCycle.refl ..)))
  have := size d
  change Nat.card {e // SameCycle φ d e} = 3 at this
  omega

/-- The Euler-tight condition forces one dart component and exact facial period three. -/
theorem tight_faces {V : Type*} [Finite V] {H : SimpleGraph V} (M : PlaneMap H)
    (minDeg : ∀ v, 2 ≤ Nat.card {u // H.Adj v u}) (nonempty : Nonempty V)
    (hE : Nat.card H.edgeSet + 6 = 3 * Nat.card V) :
    numComponents M.rot (dartSymm H) = 1 ∧
    ∀ d, M.facePerm (M.facePerm (M.facePerm d)) = d := by
  classical
  let := Fintype.ofFinite V
  have neighbor (v : V) : ∃ u, H.Adj v u := by
    have h := minDeg v
    have pos : 0 < Nat.card {u // H.Adj v u} := by omega
    obtain ⟨u⟩ := (Nat.card_pos_iff.mp pos).1
    exact ⟨_, u.property⟩
  let : Nonempty H.Dart := by
    obtain ⟨v⟩ := nonempty
    obtain ⟨u,h⟩ := neighbor v
    exact ⟨⟨(v,u),h⟩⟩
  have vert : cycleCount M.rot = Nat.card V := by
    rw [cycleCount_eq_card_nonisolated M.isRotationSystem]
    exact Nat.card_congr ⟨Subtype.val, fun v => ⟨v, neighbor v⟩, fun _ => rfl, fun _ => rfl⟩
  have darts := card_dart_eq_two_mul H
  rw [← card_edgeSet_eq_cycleCount] at darts
  have lower (d : H.Dart) : 3 ≤ Nat.card {e // SameCycle M.facePerm d e} :=
    three_le_card_face M.isRotationSystem minDeg d
  have faceBound : 3 * M.numFaces ≤ Nat.card H.Dart :=
    mul_numClasses_le (SameCycle.setoid M.facePerm) 3 lower
  have euler := M.euler
  rw [vert] at euler
  have comp := one_le_numComponents M.rot (dartSymm H)
  refine ⟨by omega, period_three M minDeg ?_⟩
  apply exact_class_size (SameCycle.setoid M.facePerm) 3 lower
  change 3 * M.numFaces = Nat.card H.Dart
  omega

end Recognition.Wagner
