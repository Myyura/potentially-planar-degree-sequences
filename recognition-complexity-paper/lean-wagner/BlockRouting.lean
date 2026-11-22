import MinorWidth

/-! Restore the separated primal and dual incidence lanes. Base vertices use
their original sites. A block centre occupies one connected dual component.
The original bound on base-site multiplicity increases by exactly one. -/
namespace Recognition.BlockRouting
open StateIso SparseCompare MinorWidth Finset PlanarDegrees.Frontier

structure Routes (A : Colored n) (H : Colored m) (c : Nat) where
  site : Fin n → Fin m
  live : Fin n → Prop
  link : Fin m → Fin m → Prop
  symm : ∀x y,link x y → link y x
  step : ∀x y, link x y → H.edge x y=true ∨ H.edge y x=true
  direct : ∀i j,arc A (.inl i) (.inl j)=true → site i=site j ∨ H.edge (site i) (site j)=true ∨ H.edge (site j) (site i)=true
  rows : ∀i j,j∈row A i ↔ live i ∧ live j ∧ Walk link (site i) (site j)
  load : ∀x,(univ.filter (fun i => site i=x)).card≤c

private theorem witness (A : Colored n) (b : Fin (blocks A).length) :
    ∃i,row A i=(blocks A).get b := ((block_mem A _).mp (List.get_mem ..)).2

theorem model (A : Colored n) (H : Colored m) (P : Routes A H c) :
    Nonempty (MinorWidth.Model (graph A) H (c+1)) := by
  classical
  let pick (b : Fin (blocks A).length) := (witness A b).choose
  have picked (b) : row A (pick b)=(blocks A).get b := (witness A b).choose_spec
  have used (b) : P.live (pick b) := by
    have nonempty := ((block_mem A _).mp (List.get_mem (blocks A) b)).1
    obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr nonempty
    rw [←picked] at hj; exact ((P.rows _ _).mp hj).1
  let region (b : Fin (blocks A).length) := univ.filter fun v => Walk P.link (P.site (pick b)) v
  have uniqueRegion {b d} (hit : Walk P.link (P.site (pick b)) (P.site (pick d))) : b=d := by
    apply (List.nodup_iff_injective_get.mp (List.nodup_dedup _))
    change (blocks A).get b=(blocks A).get d
    rw [←picked,←picked];ext j
    rw [P.rows,P.rows]
    exact ⟨fun h => ⟨used d,h.2.1,(hit.symm P.symm).trans h.2.2⟩,
      fun h => ⟨used b,h.2.1,hit.trans h.2.2⟩⟩
  let bag : Node A → Finset (Fin m) := Sum.elim (fun i => {P.site i}) region
  let pos := (@finSumFinEquiv n (blocks A).length).symm
  refine ⟨⟨fun v => bag (pos v),?_,?_,?_,?_⟩⟩
  · intro v
    cases eq : pos v with
    | inl i => exact Finset.singleton_nonempty _
    | inr b => exact ⟨_,mem_filter.mpr ⟨mem_univ _,.refl⟩⟩
  · intro v x hx y hy
    cases q : pos v with
    | inl i =>
      change x∈bag (pos v) at hx;change y∈bag (pos v) at hy
      rw [q] at hx hy
      exact (Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm ▸ Walk.refl
    | inr b =>
      change x∈bag (pos v) at hx;change y∈bag (pos v) at hy
      rw [q] at hx hy
      have wx := (mem_filter.mp hx).2
      have wy := (mem_filter.mp hy).2
      have lift {a} (w : Walk P.link (P.site (pick b)) a) :
          Walk (fun i j => i∈region b ∧ j∈region b ∧ (H.edge i j=true ∨ H.edge j i=true)) (P.site (pick b)) a := by
        induction w with
        | refl => exact .refl
        | step h e ih => exact .step ih ⟨mem_filter.mpr ⟨mem_univ _,h⟩,mem_filter.mpr ⟨mem_univ _,h.step e⟩,P.step _ _ e⟩
      exact ((lift wx).symm (fun _ _ h => ⟨h.2.1,h.1,h.2.2.symm⟩)).trans (lift wy)
  · intro v w edge
    change arc A (pos v) (pos w)=true at edge
    cases x : pos v with
    | inl i =>
      cases y : pos w with
      | inl j =>
        exact ⟨_,mem_singleton_self _,_,mem_singleton_self _,P.direct _ _ (x ▸ y ▸ edge)⟩
      | inr b =>
        rw [x,y] at edge
        have eq := of_decide_eq_true edge
        have self : pick b ∈ row A (pick b) := (P.rows ..).mpr ⟨used b,used b,.refl⟩
        rw [picked,←eq] at self
        have w := ((P.rows ..).mp self).2.2
        exact ⟨_,mem_singleton_self _,_,mem_filter.mpr ⟨mem_univ _,w.symm P.symm⟩,.inl rfl⟩
    | inr b =>
      cases y : pos w with
      | inl j =>
        rw [x,y] at edge
        have mem := of_decide_eq_true edge
        have w := ((P.rows _ _).mp ((picked b) ▸ mem)).2.2
        exact ⟨_,mem_filter.mpr ⟨mem_univ _,w⟩,_,mem_singleton_self _,.inl rfl⟩
      | inr b' => rw [x,y] at edge; contradiction
  · intro x
    let left := univ.filter (fun i => P.site i=x)
    let right := univ.filter (fun b => x∈region b)
    have one : right.card≤1 := Finset.card_le_one.mpr (fun b hb d hd =>
      uniqueRegion (((mem_filter.mp (mem_filter.mp hb).2).2).trans (((mem_filter.mp (mem_filter.mp hd).2).2).symm P.symm)))
    have sub : (univ.filter fun v => x∈bag (pos v)) ⊆ (left.disjSum right).map pos.symm.toEmbedding := by
      intro i mem
      have hb := (mem_filter.mp mem).2
      obtain ⟨i,rfl⟩ := pos.symm.surjective i
      simp only [Equiv.apply_symm_apply] at hb
      apply mem_map.mpr;refine ⟨i,?_,rfl⟩
      cases i with
      | inl v => exact Finset.inl_mem_disjSum.mpr (mem_filter.mpr ⟨mem_univ _,(mem_singleton.mp hb).symm⟩)
      | inr b => exact Finset.inr_mem_disjSum.mpr (mem_filter.mpr ⟨mem_univ _,hb⟩)
    exact (card_le_card sub).trans (by simpa using Nat.add_le_add (P.load x) one)

end Recognition.BlockRouting
