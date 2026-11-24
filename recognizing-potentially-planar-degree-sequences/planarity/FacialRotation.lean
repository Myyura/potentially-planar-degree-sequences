import Rotation
import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar

/-! The face permutation of a sphere map with triangular orbits gives the
labelled triangular rotation used by the degree-list compiler. -/
namespace Recognition.Wagner
open SparseBoundary Rotation Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

private theorem two_orbit {D : Type} [Finite D] (σ : Perm D) (d : D) (two : σ (σ d) = d) :
    Nat.card {e // SameCycle σ d e} ≤ 2 := by
  classical
  let P (x : D) := x = d ∨ x = σ d
  let s : Setoid D := Setoid.ker (fun x => P x)
  have stable (x : D) : s x (σ x) := by
    apply propext
    change (x = d ∨ x = σ d) ↔ σ x = d ∨ σ x = σ d
    constructor
    · rintro (rfl|rfl)
      · exact .inr rfl
      · exact .inl two
    · rintro (h|h)
      · exact .inr (σ.injective (h.trans two.symm))
      · exact .inl (σ.injective h)
  have cases' (e : {e // SameCycle σ d e}) : P e.val :=
    Eq.mp (sameCycle_of_step s stable e.property) (show P d from .inl rfl)
  let f (e : {e // SameCycle σ d e}) : Bool := decide (e.val = d)
  have bound := Nat.card_le_card_of_injective f (by
    intro x y sub
    by_cases a : x.val=d <;> by_cases b : y.val=d
    · exact Subtype.ext (a.trans b.symm)
    · simp [f,a,b] at sub
    · simp [f,a,b] at sub
    · exact Subtype.ext (((cases' x).resolve_left a).trans ((cases' y).resolve_left b).symm))
  simpa using bound

private theorem distinct_sides {H : SimpleGraph (Fin n)} (M : PlaneMap H)
    (minDeg : ∀ v, 3 ≤ Nat.card {u // H.Adj v u})
    (three : ∀ d, M.facePerm (M.facePerm (M.facePerm d)) = d) (d : H.Dart) :
    (M.facePerm d).snd ≠ (M.facePerm d.symm).snd := by
  classical
  intro eq
  let φ := M.facePerm
  have start (t : H.Dart) : (φ t).fst=t.snd := facePerm_fst M.isRotationSystem t
  have close (t : H.Dart) : (φ (φ t)).snd=t.fst :=
    (start (φ (φ t))).symm.trans (congrArg (fun x : H.Dart => x.fst) (three t))
  have revEq : (φ d.symm).symm = φ (φ d) := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · change (φ d.symm).snd = (φ (φ d)).fst
      exact eq.symm.trans (start (φ d)).symm
    · change (φ d.symm).fst = (φ (φ d)).snd
      exact (start d.symm).trans (close d).symm
  have two : M.rot (M.rot d)=d := by
    change φ (φ d.symm).symm=d
    rw [revEq]; exact three d
  have lo := minDeg d.fst
  have hi := card_neighbor_le_card_sameCycle M.isRotationSystem d
  have size := two_orbit M.rot d two
  omega

variable {n : Nat} (G : Graph n) (H : SimpleGraph (Fin n))
    (adj : ∀ i j, H.Adj i j ↔ G.adj i j=true)

private def toDart (d : Dart G) : H.Dart := ⟨(d.src,d.dst),(adj ..).mpr d.edge⟩
private def fromDart (d : H.Dart) : Dart G := ⟨d.fst,d.snd,(adj ..).mp d.adj⟩

private theorem to_from (d : H.Dart) : toDart G H adj (fromDart G H adj d) = d := rfl
private theorem from_to (d : Dart G) : fromDart G H adj (toDart G H adj d) = d := rfl

/-- Component count and facial period are supplied by the tight Euler count.
The conversion also proves the two distinct third corners on every edge. -/
noncomputable def rotation (M : PlaneMap H) (minDeg : ∀ v, 3 ≤ Nat.card {u // H.Adj v u})
    (one : numComponents M.rot (dartSymm H) = 1)
    (three : ∀ d, M.facePerm (M.facePerm (M.facePerm d))=d) : TriangularRotation G := by
  classical
  let back := fromDart G H adj
  let toch := toDart G H adj
  let turn (d : Dart G) := back (M.facePerm (toch d))
  have step (d : H.Dart) : turn (back d) = back (M.facePerm d) := rfl
  have tri (d : Dart G) : turn (turn (turn d))=d := by
    change back (M.facePerm (M.facePerm (M.facePerm (toch d))))=d
    rw [three]; rfl
  refine ⟨turn,fun d => facePerm_fst M.isRotationSystem (toch d),tri,?_,?_⟩
  · intro d; exact distinct_sides M minDeg three (toch d)
  · intro d e
    let K := compSetoid M.rot (dartSymm H)
    have one' : Nat.card (Quotient K) = 1 := one
    have sub := (Nat.card_eq_one_iff_unique.mp one').1
    have rel : K (toch d) (toch e) :=
      Quotient.exact (@Subsingleton.elim _ sub (Quotient.mk K (toch d)) (Quotient.mk K (toch e)))
    let r : Setoid H.Dart := {
      r := fun x y => Reach turn (back x) (back y)
      iseqv := ⟨fun _ => .base,fun h => Reach.symm tri h,fun h j => h.trans j⟩
    }
    apply compSetoid_le r (σ := M.rot) (α := dartSymm H) ?_ ?_ rel
    · intro z
      change Reach turn (back z) (back (M.facePerm z.symm))
      rw [← step]
      exact .face (.reverse .base)
    · intro z
      exact Reach.reverse Reach.base

end Recognition.Wagner
