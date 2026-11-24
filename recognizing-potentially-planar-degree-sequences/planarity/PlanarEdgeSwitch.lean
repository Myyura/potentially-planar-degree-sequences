import PackedMinor
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Connecting distinct components by a degree-preserving planar edge switch.
The two deleted edges and the two new links lie in one four-vertex patch.
The retained-edge 2-sum theorem supplies its planar rotation. -/
namespace Recognition.PlanarEdgeSwitch
open LeanPool.K5MinorFreeChoosability Equiv

variable {V : Type*} [Finite V]

private def inside (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ a∈S ∧ b∈S
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

private def pair (u v a b : V) := (a=u ∧ b=v) ∨ (a=v ∧ b=u)

private def switched (G : SimpleGraph V) (u v x y : V) : SimpleGraph V where
  Adj a b := (G.Adj a b ∧ ¬pair u v a b ∧ ¬pair x y a b) ∨
      ((pair u x a b ∨ pair v y a b) ∧ a≠b)
  symm := ⟨fun a b h => by
    have rev (i j) : pair i j a b ↔ pair i j b a := by unfold pair; tauto
    simpa only [←rev,G.adj_comm b a,ne_comm (a:=b)] using h⟩
  loopless := ⟨fun a h => h.elim (fun g => G.irrefl g.1) (fun g => g.2 rfl)⟩

private theorem patch (G : SimpleGraph V) (plane : IsPlanar G) {u v x y : V}
    (uv : G.Adj u v) (xy : G.Adj x y) (apart : ¬G.Reachable u x) : IsPlanar (switched G u v x y) := by
  classical
  let _ := Fintype.ofFinite V
  let A := Finset.univ.filter (G.Reachable u)
  let B := Finset.univ \ A
  let C : Finset V := {u,v,x,y}
  let L := inside G A
  let R := inside G B
  let K := inside (⊤ : SimpleGraph V) C
  have inA (a : V) : a∈A ↔ G.Reachable u a := by simp [A]
  have inB (a : V) : a∈B ↔ ¬G.Reachable u a := by simp [B,inA]
  have isolated : ¬G.Reachable u y := fun h => apart (h.trans xy.reachable.symm)
  have U : u∈A := (inA _).mpr .rfl
  have V' : v∈A := (inA _).mpr uv.reachable
  have X : x∈B := (inB _).mpr apart
  have Y : y∈B := (inB _).mpr isolated
  have subsetL : L ≤ G := fun _ _ h => h.1
  have subsetR : R ≤ G := fun _ _ h => h.1
  obtain ⟨lp⟩ := plane.mono subsetL
  obtain ⟨rp⟩ := plane.mono subsetR
  have lLab : ∀ a b, L.Adj a b → a∈A := fun _ _ h => h.2.1
  have rLab : ∀ a b, R.Adj a b → a∈B := fun _ _ h => h.2.1
  have kLab : ∀ a b, K.Adj a b → a∈C := fun _ _ h => h.2.1
  have size : C.card ≤ 4 := by simp only [C]; calc
    _ ≤ ({v,x,y} : Finset V).card+1 := Finset.card_insert_le _ _
    _ ≤ ({x,y} : Finset V).card+1+1 := by have := Finset.card_insert_le v ({x,y} : Finset V);omega
    _ ≤ _ := by have := Finset.card_insert_le x ({y} : Finset V); simp at this;omega
  obtain ⟨kp⟩ := isPlanar_of_card_le_four kLab size
  have first : A ∩ C = {u,v} := by
    ext t; simp [C,inA,uv.reachable,apart,isolated]
  have fused := isPlanar_sup_of_two lLab kLab lp kp uv.ne first ⟨uv,U,V'⟩
    (show K.Adj u v from ⟨uv.ne,by simp [C],by simp [C]⟩)
  obtain ⟨lk⟩ := fused
  have lkLab : ∀ a b, (L⊔K).Adj a b → a∈A∪C := fun a b h =>
    h.elim (fun h => Finset.mem_union_left _ (lLab _ _ h)) (fun h => Finset.mem_union_right _ (kLab _ _ h))
  have second : (A∪C) ∩ B = {x,y} := by
    ext t
    simp [C,inA,inB]
    grind [show G.Reachable u u from .rfl, uv.reachable]
  have all := isPlanar_sup_of_two lkLab rLab lk rp xy.ne second
    (Or.inr (show K.Adj x y from ⟨xy.ne,by simp [C],by simp [C]⟩)) ⟨xy,X,Y⟩
  apply all.mono
  intro a b h
  rcases h with keep | ⟨add,ne⟩
  · by_cases ar : G.Reachable u a
    · exact Or.inl (Or.inl ⟨keep.1,(inA _).mpr ar,(inA _).mpr (ar.trans keep.1.reachable)⟩)
    · exact Or.inr ⟨keep.1,(inB _).mpr ar,(inB _).mpr fun br => ar (br.trans keep.1.symm.reachable)⟩
  · apply Or.inl; apply Or.inr
    refine ⟨ne,?_,?_⟩ <;> rcases add with ((⟨rfl,rfl⟩|⟨rfl,rfl⟩)|(⟨rfl,rfl⟩|⟨rfl,rfl⟩)) <;> simp [C]

omit [Finite V] in
private theorem degrees (G : SimpleGraph V) {u v x y : V}
    (uv : G.Adj u v) (xy : G.Adj x y) (apart : ¬G.Reachable u x) (a : V) :
    Nat.card {b // (switched G u v x y).Adj a b} = Nat.card {b // G.Adj a b} := by
  classical
  let H := switched G u v x y
  have disjoint (i j) (hi : i=u ∨ i=v) (hj : j=x ∨ j=y) : i≠j ∧ ¬G.Adj i j := by
    have left : G.Reachable u i := hi.elim (fun e => e ▸ .rfl) (fun e => e ▸ uv.reachable)
    have right : G.Reachable j x := hj.elim (fun e => e ▸ .rfl) (fun e => e ▸ xy.reachable.symm)
    exact ⟨fun e => apart (left.trans (e ▸ right)),fun h => apart (left.trans (h.reachable.trans right))⟩
  have ux := disjoint u x (Or.inl rfl) (Or.inl rfl)
  have uy := disjoint u y (Or.inl rfl) (Or.inr rfl)
  have vx := disjoint v x (Or.inr rfl) (Or.inl rfl)
  have vy := disjoint v y (Or.inr rfl) (Or.inr rfl)
  let σ : Equiv.Perm V := if a=u then swap v x else if a=v then swap u y else
    if a=x then swap y u else if a=y then swap x v else 1
  have neighbours (b : V) : G.Adj a b ↔ H.Adj a (σ b) := by
    have vu := uv.symm
    have yx := xy.symm
    have xu : ¬G.Adj x u := fun h => ux.2 h.symm
    have yu : ¬G.Adj y u := fun h => uy.2 h.symm
    have xv : ¬G.Adj x v := fun h => vx.2 h.symm
    have yv : ¬G.Adj y v := fun h => vy.2 h.symm
    by_cases au : a=u <;> by_cases av : a=v <;> by_cases ax : a=x <;> by_cases ay : a=y <;>
      simp_all [H,σ,switched,pair,Equiv.swap_apply_def] <;> split_ifs <;> grind [G.irrefl,uv.ne,xy.ne]
  exact (Nat.card_congr (σ.subtypeEquiv neighbours)).symm

omit [Finite V] in
private theorem old_paths (G : SimpleGraph V) {u v x y : V} (uv : G.Adj u v) (xy : G.Adj x y)
    (apart : ¬G.Reachable u x) (nonbridge : ¬G.IsBridge s(u,v)) :
    (∀ a b, G.Reachable a b → (switched G u v x y).Reachable a b) ∧
      (switched G u v x y).Reachable u x := by
  let H := switched G u v x y
  have ux : H.Adj u x := Or.inr ⟨Or.inl (Or.inl ⟨rfl,rfl⟩),fun e => apart (e ▸ .rfl)⟩
  have vy : H.Adj v y := Or.inr ⟨Or.inr (Or.inl ⟨rfl,rfl⟩),fun e => apart (uv.reachable.trans (e ▸ xy.reachable.symm))⟩
  have isolated : ¬G.Reachable u y := fun h => apart (h.trans xy.reachable.symm)
  obtain ⟨alt⟩ := uv.reachable.reachable_deleteEdges_of_not_isBridge nonbridge
  have carry {a b : V} (p : (G.deleteEdges {s(u,v)}).Walk a b) (ha : G.Reachable u a) : H.Reachable a b := by
    induction p with
    | nil => exact .rfl
    | @cons a b c first rest ih =>
      obtain ⟨adj,neq⟩ := SimpleGraph.deleteEdges_adj.mp first
      have ne : s(a,b) ≠ s(u,v) := neq
      have noOld : ¬pair u v a b := by
        intro same; apply ne; exact Sym2.eq_iff.mpr same
      have noOther : ¬pair x y a b := by
        rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩) <;> contradiction
      exact (show H.Adj a b from Or.inl ⟨adj,noOld,noOther⟩).reachable.trans (ih (ha.trans adj.reachable))
  have uvPath := carry alt .rfl
  have xyPath := ux.symm.reachable.trans (uvPath.trans vy.reachable)
  have edge {a b : V} (h : G.Adj a b) : H.Reachable a b := by
    by_cases first : pair u v a b
    · rcases first with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> first | exact uvPath | exact uvPath.symm
    by_cases second : pair x y a b
    · rcases second with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> first | exact xyPath | exact xyPath.symm
    exact (show H.Adj a b from Or.inl ⟨h,first,second⟩).reachable
  refine ⟨?_,ux.reachable⟩
  rintro a b ⟨p⟩
  induction p with
  | nil => exact .rfl
  | cons h _ ih => exact (edge h).trans ih

/-- A nonbridge and an edge in a different component can be replaced on
exactly the original labels, decreasing the number of components. -/
theorem merge (G : SimpleGraph V) (plane : IsPlanar G) {u v x y : V}
    (uv : G.Adj u v) (xy : G.Adj x y) (apart : ¬G.Reachable u x) (nonbridge : ¬G.IsBridge s(u,v)) :
    ∃ H : SimpleGraph V, IsPlanar H ∧
      (∀ i, Nat.card {j // H.Adj i j} = Nat.card {j // G.Adj i j}) ∧
      Nat.card H.ConnectedComponent < Nat.card G.ConnectedComponent := by
  classical
  let H := switched G u v x y
  obtain ⟨old,join⟩ := old_paths G uv xy apart nonbridge
  let q : G.ConnectedComponent → H.ConnectedComponent := Quot.lift H.connectedComponentMk (fun a b h => SimpleGraph.ConnectedComponent.sound (old a b h))
  have surj : Function.Surjective q := by
    intro c; exact Quot.inductionOn c (fun a => ⟨G.connectedComponentMk a,rfl⟩)
  have fail : ¬Function.Injective q := by
    intro injective
    exact apart (SimpleGraph.ConnectedComponent.exact (injective (show q (G.connectedComponentMk u) = q (G.connectedComponentMk x) from SimpleGraph.ConnectedComponent.sound join)))
  let := Fintype.ofFinite G.ConnectedComponent
  let := Fintype.ofFinite H.ConnectedComponent
  exact ⟨H,patch G plane uv xy apart,degrees G uv xy apart,
    by simpa only [Nat.card_eq_fintype_card] using Fintype.card_lt_of_surjective_not_injective q surj fail⟩

end Recognition.PlanarEdgeSwitch
