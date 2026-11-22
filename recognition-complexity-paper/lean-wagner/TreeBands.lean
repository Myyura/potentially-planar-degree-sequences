import Bouquet

/-! Contract a spanning tree in an arbitrary connected planar multimap.
Both the contracted tree bands and the remaining bands form genus-zero
bouquets in the same rotation. The original permutations can be recovered
from these two pairings. -/
namespace Recognition.TreeBands
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

structure Bands {D : Type} [Finite D] (σ α θ T C : Perm D) : Prop where
  rotation : θ*T=σ
  pairing : T*C=α
  treeUndo : ∀ x, T (T x)=x
  cotreeUndo : ∀ x, C (C x)=x
  disjoint : ∀ x, T x=x ∨ C x=x
  internal : ∀ x, SameCycle θ x (T x)
  rank : cycleCount θ + Nat.card D = cycleCount σ + cycleCount T
  cotreeSphere : eulerDefect θ C = 0

private theorem square {D : Type} (f : Perm D) (undo : ∀ x, f (f x)=x) : f*f=1 := by
  ext x
  exact undo x

private theorem fused {D : Type} [Finite D] [DecidableEq D] {σ α θ T C : Perm D}
    (h : Bands σ α θ T C) {x y : D} (pair : C x=y) (cross : ¬ SameCycle θ x y) :
    Bands σ α (θ * swap x y) (T * swap x y) (C * swap x y) := by
  let S := swap x y
  have ne : x≠y := fun e => cross (e ▸ SameCycle.refl _ _)
  have back : C y=x := pair ▸ h.cotreeUndo x
  have tx : T x=x := (h.disjoint x).resolve_right (pair ▸ ne.symm)
  have ty : T y=y := (h.disjoint y).resolve_right (back ▸ ne)
  have tcomm : T*S=S*T := by simpa [S,tx,ty] using mul_swap_eq_swap_mul T x y
  have ccomm : C*S=S*C := by
    simpa [S,pair,back,swap_comm y x] using mul_swap_eq_swap_mul C x y
  have ss : S*S=1 := swap_mul_self _ _
  have cancel (B P : Perm D) (comm : P*S=S*P) : (B*S)*(P*S)=B*P := by
    rw [mul_assoc,comm,← mul_assoc S S,ss,one_mul]
  have ntInv := cancel T T tcomm
  have ncInv := cancel C C ccomm
  rw [square _ h.treeUndo] at ntInv
  rw [square _ h.cotreeUndo] at ncInv
  have xy := sameCycle_mulSwap_of_not cross
  have inclusion {a b : D} (old : SameCycle θ a b) : SameCycle (θ*S) a b :=
    sameCycle_of_sameCycle_mulSwap xy (by rwa [mulSwap_mulSwap])
  constructor
  · exact (cancel θ T tcomm).trans h.rotation
  · exact (cancel T C ccomm).trans h.pairing
  · exact fun z => congrArg (fun f : Perm D => f z) ntInv
  · exact fun z => congrArg (fun f : Perm D => f z) ncInv
  · intro z
    by_cases a : z=x
    · exact .inr (by simp [a,back])
    by_cases b : z=y
    · exact .inr (by simp [b,pair])
    simpa [swap_apply_of_ne_of_ne a b] using h.disjoint z
  · intro z
    by_cases a : z=x
    · subst z; simpa [ty] using xy
    by_cases b : z=y
    · subst z; simpa [tx] using xy.symm
    simpa [swap_apply_of_ne_of_ne a b] using inclusion (h.internal z)
  · have ht := cycleCount_mul_swap_of_not_sameCycle (π := T) (x := x) (y := y)
      (fun g => ne (g.eq_of_left tx))
    have hv := cycleCount_mul_swap_of_not_sameCycle cross
    have := h.rank
    omega
  · have ge := eulerDefect_nonneg (θ*S) (C*S)
    have le := eulerDefect_merge (σ := θ) ne pair back cross
    exact le_antisymm (le.trans (le_of_eq h.cotreeSphere)) ge

private theorem tree_sphere {D : Type} [Finite D] {σ α θ T C : Perm D} (h : Bands σ α θ T C) :
    eulerDefect θ T=0 := by
  have same : numComponents θ T=cycleCount θ :=
    numClasses_congr (fun x y => ⟨fun g => compSetoid_le (SameCycle.setoid θ)
      (fun z => sameCycle_apply_right.mpr (SameCycle.refl _ z)) h.internal g,
      compSetoid_of_sameCycle_left⟩)
  have := h.rank
  unfold eulerDefect
  rw [same,h.rotation]
  omega

/-- The root rotation of the contracted tree is transitive on all original
darts. Each dart is used by at most one of the two pairings. -/
theorem decompose {D : Type} [Finite D] (σ α : Perm D) (undo : ∀ x, α (α x)=x)
    (planar : eulerDefect σ α=0) (connected : ∀ a b, compSetoid σ α a b) :
    ∃ θ T C : Perm D, Bands σ α θ T C ∧ (∀ a b, SameCycle θ a b) ∧
      eulerDefect θ T=0 := by
  classical
  have descend (r : Nat) : ∀ θ T C : Perm D, cycleCount θ=r → Bands σ α θ T C →
      ∃ η U V : Perm D, Bands σ α η U V ∧ (∀ a b, SameCycle η a b) ∧ eulerDefect η U=0 := by
    induction r using Nat.strongRecOn with
    | ind r ih =>
      intro θ T C rank h
      by_cases all : ∀ a, SameCycle θ a (C a)
      · refine ⟨θ,T,C,h,?_,tree_sphere h⟩
        intro a b
        apply compSetoid_le (SameCycle.setoid θ) _ _ (connected a b)
        · intro z
          rw [← h.rotation]
          change SameCycle θ z (θ (T z))
          exact sameCycle_apply_right.mpr (h.internal z)
        · intro z
          rw [← h.pairing]
          exact (all z).trans (h.internal (C z))
      · obtain ⟨x,edge⟩ := Classical.not_forall.mp all
        have smaller := cycleCount_mul_swap_of_not_sameCycle edge
        exact ih _ (by omega) _ _ _ rfl (fused h rfl edge)
  apply descend _ σ 1 α rfl
  exact ⟨by simp,by simp,fun _ => rfl,undo,fun _ => Or.inl rfl,
    fun _ => SameCycle.refl _ _,by rw [cycleCount_one],planar⟩

#print axioms decompose
end Recognition.TreeBands
