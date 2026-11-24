import LeanPool.K5MinorFreeChoosability.Wagner.WagnerA
import Mathlib.Order.Preorder.Finite

namespace Recognition.Augment
open LeanPool.K5MinorFreeChoosability

theorem exists_maximal {V : Type*} [Finite V] (G : SimpleGraph V) (h : IsPlanar G) :
    ∃ H, G ≤ H ∧ Maximal IsPlanar H := Finite.exists_le_maximal h

private def part (G : SimpleGraph V) (p : V → Prop) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ p x ∧ p y
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem maximal_connected {V : Type*} [Finite V] [Nonempty V] {H : SimpleGraph V}
    (hm : Maximal IsPlanar H) : H.Connected := by
  classical
  let := Fintype.ofFinite V
  refine ⟨?_⟩
  intro u v
  by_contra notJoined
  have hu : H.Reachable u u := .refl _
  have ne : u ≠ v := fun eq => notJoined (eq ▸ hu)
  let P := H.Reachable u
  let A := part H P
  let B := part H (fun x => ¬P x)
  let E := addEdgeGraph (⊥ : SimpleGraph V) u v
  let X := Finset.univ.filter P
  let Y := Finset.univ.filter (fun x => ¬ P x)
  let Z : Finset V := {u,v}
  have inX (a) : a ∈ X ↔ P a := by simp [X]
  have inY (a) : a ∈ Y ↔ ¬ P a := by simp [Y]
  have inZ (a) : a ∈ Z ↔ a = u ∨ a = v := by simp [Z]
  have pa : IsPlanar A := hm.1.mono (fun _ _ h => h.1)
  have pb : IsPlanar B := hm.1.mono (fun _ _ h => h.1)
  have ax (x y) (h : A.Adj x y) : x ∈ X := (inX _).mpr h.2.1
  have by' (x y) (h : B.Adj x y) : x ∈ Y := (inY _).mpr h.2.1
  have ez (x y) (h : E.Adj x y) : x ∈ Z := by
    apply (inZ _).mpr
    rcases (addEdgeGraph_adj ne _ _).mp h with h|h|h
    · exact h.elim
    · exact .inl h.1
    · exact .inr h.1
  have pe : IsPlanar E := isPlanar_of_card_le_four ez (by
    have h := Finset.card_insert_le u {v}; simp only [Finset.card_singleton] at h
    change (insert u ({v} : Finset V)).card ≤ 4; omega)
  have xu (t : V) (mem : t ∈ X ∩ Z) : t=u := by
    obtain ⟨hx,hz⟩ := Finset.mem_inter.mp mem
    rcases (inZ _).mp hz with rfl|rfl
    · rfl
    · exact False.elim (notJoined ((inX _).mp hx))
  obtain ⟨ma⟩ := pa
  obtain ⟨mb⟩ := pb
  obtain ⟨me⟩ := pe
  obtain ⟨mae⟩ := isPlanar_sup_of_le_one ax ez ma me (fun p hp q hq => (xu _ hp).trans (xu _ hq).symm)
  have ae (x y) (h : (A ⊔ E).Adj x y) : x ∈ X ∪ Z :=
    h.elim (fun ha => Finset.mem_union_left Z (ax _ _ ha)) (fun he => Finset.mem_union_right X (ez _ _ he))
  have yv (t : V) (mem : t ∈ (X ∪ Z) ∩ Y) : t=v := by
    obtain ⟨hx,hy⟩ := Finset.mem_inter.mp mem
    have hh := (inY t).mp hy
    rcases Finset.mem_union.mp hx with x|z
    · exact False.elim (hh ((inX t).mp x))
    · rcases (inZ _).mp z with rfl|rfl
      · exact False.elim (hh hu)
      · rfl
  have large := isPlanar_sup_of_le_one ae by' mae mb (fun p hp q hq => (yv _ hp).trans (yv _ hq).symm)
  have le : H ≤ (A ⊔ E) ⊔ B := by
    intro a b h
    have step : P a ↔ P b := ⟨fun p => p.trans h.reachable,fun p => p.trans h.symm.reachable⟩
    by_cases inside : P a
    · exact .inl (.inl ⟨h,inside,step.mp inside⟩)
    · exact .inr ⟨h,inside,fun k => inside (step.mpr k)⟩
  have newedge : ((A ⊔ E) ⊔ B).Adj u v := .inl (.inr ((addEdgeGraph_adj ne u v).mpr (.inr (.inl ⟨rfl,rfl⟩))))
  exact notJoined ((hm.2 large le) newedge).reachable
end Recognition.Augment
