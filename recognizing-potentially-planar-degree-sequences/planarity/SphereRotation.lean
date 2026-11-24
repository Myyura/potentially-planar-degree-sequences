import PackedMinor
import Topology

/-! Oriented triangle rows exhaust all darts of a labelled simple graph.
The Euler equality forces the rotation cycles to have exactly one orbit at
each used vertex. -/
namespace Recognition.SphereRotation
open PlanarDegrees.Frontier Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

/-- Construct an upstream genus-zero rotation from a coherent dart table.
The row permutation cycles its three columns; twin darts connect the rows. -/
theorem plane_of_rows (H : SimpleGraph (Fin n)) (row : (Fin (f+1) × Fin 3) ≃ H.Dart)
    (chain : ∀ i k, (row (i,k+1)).fst=(row (i,k)).snd)
    (used : Function.Surjective (fun d : H.Dart => d.fst))
    (connected : ∀ i, Walk (fun a b => ∃ k l, (row (a,k)).symm = row (b,l)) 0 i)
    (count : (f+1)+4=2*n) :
    ∃ M : PlaneMap H, (∀ i k, M.facePerm (row (i,k))=row (i,k+1)) ∧
      ∀ a b, M.facePerm.SameCycle a b ↔ (row.symm a).1=(row.symm b).1 := by
  classical
  let φ := row.permCongr ((Equiv.refl _).prodCongr (Equiv.addRight (1 : Fin 3)))
  let α := dartSymm H
  let σ := φ*α
  have next (i k) : φ (row (i,k))=row (i,k+1) := by simp [φ, Equiv.permCongr_apply]
  have back (d : H.Dart) : (σ*α) d=φ d := by change φ d.symm.symm = _; rfl
  have mul : σ*α=φ := Equiv.ext back
  let owner (d : H.Dart) := (row.symm d).1
  have owner_row (i k) : owner (row (i,k)) = i := by simp [owner]
  have cycle (i k l) : SameCycle φ (row (i,k)) (row (i,l)) := by
    have h : ∀ (k l : Fin 3), l=k ∨ l=k+1 ∨ l=(k+1)+1 := by decide
    rcases h k l with rfl|rfl|rfl
    · exact .rfl
    · rw [← next]; exact sameCycle_apply_right.mpr .rfl
    · rw [← next, ← next]; exact sameCycle_apply_right.mpr (sameCycle_apply_right.mpr .rfl)
  have sc : ∀ a b : H.Dart, SameCycle φ a b ↔ owner a = owner b := by
    intro a b
    constructor
    · apply sameCycle_of_step (Setoid.ker owner)
      intro d
      obtain ⟨⟨i,k⟩,rfl⟩ := row.surjective d
      change owner _=owner _; rw [next,owner_row,owner_row]
    · obtain ⟨⟨i,k⟩,rfl⟩ := row.surjective a
      obtain ⟨⟨j,l⟩,rfl⟩ := row.surjective b
      simp only [owner_row]; rintro rfl; exact cycle _ _ _
  have fc : cycleCount φ=f+1 := by
    have eq : SameCycle.setoid φ = Setoid.ker owner := Setoid.ext sc
    have onto : Function.Surjective owner := fun i => ⟨row (i,0),owner_row _ _⟩
    rw [cycleCount,numClasses,eq,Nat.card_congr (Setoid.quotientKerEquivOfSurjective _ onto),Nat.card_fin]
  let S := compSetoid σ α
  have face (i k l) : S (row (i,k)) (row (i,l)) :=
    compSetoid_of_sameCycle_mul (mul ▸ cycle i k l)
  have reach (i) (k : Fin 3) : S (row (0,0)) (row (i,k)) := by
    induction connected i generalizing k with
    | refl => exact face _ _ _
    | @step a b _ edge ih =>
      obtain ⟨l,m,twin⟩ := edge
      have sw : S (row (a,l)) (row (b,m)) := by
        rw [← twin]; exact compSetoid_right σ α _
      exact S.trans (ih l) (S.trans sw (face b m k))
  have one : numComponents σ α=1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    refine ⟨⟨?_⟩,⟨Quotient.mk S (row (0,0))⟩⟩
    intro a b
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        obtain ⟨⟨i,k⟩,rfl⟩ := row.surjective a
        obtain ⟨⟨j,l⟩,rfl⟩ := row.surjective b
        exact Quotient.sound (S.trans (S.symm (reach i k)) (reach j l))
  have starts (d : H.Dart) : (φ d).fst=d.snd := by
    obtain ⟨⟨i,k⟩,rfl⟩ := row.surjective d; rw [next,chain]
  have fst (d : H.Dart) : (σ d).fst=d.fst := starts d.symm
  let proj : Quotient (SameCycle.setoid σ) → Fin n := Quotient.lift (fun d : H.Dart => d.fst)
    (fun a b h => sameCycle_of_step (Setoid.ker (fun d : H.Dart => d.fst)) (fun d => (fst d).symm) h)
  have onto : Function.Surjective proj := by
    intro x; obtain ⟨d,rfl⟩ := used x; exact ⟨Quotient.mk _ d,rfl⟩
  have lo : n ≤ cycleCount σ := by simpa [cycleCount,numClasses] using Nat.card_le_card_of_surjective proj onto
  have darts : Nat.card H.Dart = (f+1)*3 := by simpa using (Nat.card_congr row).symm
  have edges := card_dart_eq_two_mul H
  change Nat.card H.Dart=2*cycleCount α at edges
  have defeq : eulerDefect σ α = (Nat.card H.Dart : ℤ) + 2 - cycleCount σ - cycleCount α - (f+1 : ℕ) := by
    simp only [eulerDefect,mul,one,fc,Nat.cast_one,mul_one]
  have nonneg := eulerDefect_nonneg σ α
  have sz : cycleCount σ = n := by omega
  have inj := ((Nat.bijective_iff_surjective_and_card proj).mpr ⟨onto, (show Nat.card _ = n from sz).trans (Nat.card_fin n).symm⟩).1
  let P : PlaneMap H := ⟨σ,⟨fst,fun a b h =>
    Quotient.exact (inj (show proj (Quotient.mk _ a) = proj (Quotient.mk _ b) from h))⟩,
    (show eulerDefect σ α=0 by omega)⟩
  have perm : P.facePerm=φ := mul
  refine ⟨P,?_,?_⟩
  · rw [perm]; exact next
  · rw [perm]; exact sc

theorem planar_of_rows (H : SimpleGraph (Fin n)) (row : (Fin (f+1) × Fin 3) ≃ H.Dart)
    (chain : ∀ i k, (row (i,k+1)).fst=(row (i,k)).snd)
    (used : Function.Surjective (fun d : H.Dart => d.fst))
    (connected : ∀ i, Walk (fun a b => ∃ k l, (row (a,k)).symm = row (b,l)) 0 i)
    (count : (f+1)+4=2*n) : IsPlanar H := by
  obtain ⟨P,_,_⟩ := plane_of_rows H row chain used connected count
  exact ⟨P⟩

end Recognition.SphereRotation
