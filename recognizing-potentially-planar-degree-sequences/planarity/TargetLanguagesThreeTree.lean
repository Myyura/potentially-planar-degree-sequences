import TargetLanguagesWire
import TargetStackedBridge
import Mathlib.Data.List.NodupEquivFin

/-! The abstract graph predicate is given by an elimination order, independent
of the choice of a surface. The graph-class identification, on orders at least
four, is the classical structural fact recorded by Kratochvíl and Vaner,
"A note on planar partial 3-trees", section 2 (arXiv:1210.8113). Its interface
requires an isomorphism on every vertex and every edge, before any degrees
are taken. -/
namespace Recognition.ThreeTreeClass
open SparseBoundary SourceMap Recognition.TargetLanguages

def ThreeTree (G : Graph n) : Prop :=
  3≤n ∧ ∃ σ : Equiv.Perm (Fin n),
    (∀ i j : Fin n, i.val < 3 → j.val < 3 → i≠j → G.adj (σ i) (σ j)=true) ∧
    ∀ i : Fin n, 3 ≤ i.val →
      let old := (List.finRange n).filter (fun j => decide (j < i) && G.adj (σ i) (σ j))
      old.length=3 ∧ ∀ a∈old,∀ b∈old,a≠b → G.adj (σ a) (σ b)=true

/-- A copy of the very same graph in a mesh, including every isolated
label were one present. The constructor does not mention degrees. -/
structure Copy (G : Graph n) (M : Mesh) where
  name : Fin n ≃ {v // M.vertex v}
  edge : ∀ i j,G.adj i j=true ↔ (name j).val∈M.neighbors (name i).val

private theorem degree_copy {G : Graph n} {M} (r : SourceBridge.Regular M) (c : Copy G M)
    (v : Fin n) : G.degree v=(M.neighbors (c.name v).val).length := by
  let lab := fun i : Fin n => (c.name i).val
  let ns := (List.finRange n).filter (G.adj v)
  have inj : Function.Injective lab := fun _ _ h => c.name.injective (Subtype.ext h)
  have nd : (ns.map lab).Nodup :=
    ((List.nodup_finRange n).filter (G.adj v)).map inj
  have eq : (ns.map lab).Perm (M.neighbors (lab v)) := by
    apply List.perm_of_nodup_nodup_toFinset_eq nd (r.nodup _ (c.name v).property)
    ext x
    simp only [List.mem_toFinset,List.mem_map,ns,List.mem_filter,List.mem_finRange,true_and]
    constructor
    · rintro ⟨i,h,rfl⟩; exact (c.edge v i).mp h
    · intro h
      have vx := r.neighbor _ _ (c.name v).property h
      obtain ⟨i,hi⟩ := c.name.surjective ⟨x,vx⟩
      have hh : lab i=x := congrArg Subtype.val hi
      exact ⟨i,(c.edge v i).mpr (by change lab i∈M.neighbors (lab v);rw [hh];exact h),hh⟩
  simpa only [List.length_map,ns,Graph.degree,lab] using eq.length_eq

/-- The quoted graph-class equivalence. The second direction ranges over
arbitrary graph copies and does not postulate any degree-row assertion. -/
def KratochvilVaner : Prop := ∀ {n} (G : Graph n),4≤n →
    (G.Planar ∧ ThreeTree G ↔ ∃ M : Mesh,Stacked M ∧ Nonempty (Copy G M))

def Row (ds : List Nat) : Prop := ∃ n, ∃ G : Graph n,
    G.Planar ∧ ThreeTree G ∧ (List.ofFn G.degree : Multiset Nat)=(ds : Multiset Nat)

private theorem serial_graph {M : Mesh} (h : Stacked M) (ns : List Nat) (nd : ns.Nodup)
    (seen : ∀v,M.vertex v ↔ v∈ns) :
    ∃ (G : Graph ns.length) (c : Copy G M),∀ i : Fin ns.length,(c.name i).val=ns[i] := by
  classical
  let bij := (nd.getEquiv ns).trans (Equiv.subtypeEquivProp (funext fun x => propext (seen x).symm))
  let rel (a b : Fin ns.length) := decide ((bij b).val∈M.neighbors (bij a).val)
  obtain ⟨B⟩ := SourceBridge.stacked_bridge h
  have comm (a b) : rel a b=rel b a := by
    obtain ⟨i,hi⟩ := (B.hits _).mp (bij a).property
    obtain ⟨j,hj⟩ := (B.hits _).mp (bij b).property
    apply decide_eq_decide.mpr
    rw [←hi,←hj,←B.edge,←B.edge]
    exact ⟨fun ⟨z,h⟩ => ⟨z,B.map.flip h⟩,fun ⟨z,h⟩ => ⟨z,B.map.flip h⟩⟩
  have irr (a) : rel a a=false := by
    obtain ⟨i,hi⟩ := (B.hits _).mp (bij a).property
    apply decide_eq_false_iff_not.mpr
    rw [←hi,←B.edge]
    rintro ⟨_,e⟩
    exact B.map.distinct e rfl
  exact ⟨Graph.ofRelation rel, ⟨bij,fun a b => by
    rw [Graph.adj_ofRelation rel comm irr];simp only [rel,decide_eq_true_eq]⟩,fun _ => rfl⟩

theorem serial_iff (K : KratochvilVaner) (ds : List Nat) (large : 4≤ds.length) :
    Row ds ↔ StackedHistory.SequentialRealization (ds : Multiset Nat) := by
  constructor
  · rintro ⟨n,G,p,t,degs⟩
    have len : n=ds.length := by simpa using congrArg Multiset.card degs
    obtain ⟨M,stacked,⟨c⟩⟩ := (K G (len ▸ large)).mp ⟨p,t⟩
    let lab := fun i : Fin n => (c.name i).val
    have inj : Function.Injective lab := fun _ _ h => c.name.injective (Subtype.ext h)
    refine ⟨M,stacked,(List.finRange n).map lab,(List.nodup_finRange n).map inj,?_,?_⟩
    · intro x
      constructor
      · intro hx;obtain ⟨i,h⟩ := c.name.surjective ⟨x,hx⟩
        exact List.mem_map.mpr ⟨i,List.mem_finRange i,congrArg Subtype.val h⟩
      · intro h; obtain ⟨i,_,rfl⟩ := List.mem_map.mp h; exact (c.name i).property
    · rw [List.map_map,←List.ofFn_eq_map]
      convert degs using 2
      apply congrArg List.ofFn
      funext i
      exact (degree_copy (SourceBridge.regular stacked) c i).symm
  · rintro ⟨M,s,ns,nd,all,degs⟩
    obtain ⟨G,c,lab⟩ := serial_graph s ns nd all
    have len : ns.length=ds.length := by simpa using congrArg Multiset.card degs
    have good := (K G (len ▸ large)).mpr ⟨M,s,⟨c⟩⟩
    refine ⟨_,G,good.1,good.2,?_⟩
    rw [←degs]
    apply congrArg (fun l : List Nat => (l : Multiset Nat))
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_ofFn,List.getElem_map]
      exact (degree_copy (SourceBridge.regular s) c ⟨i,by simpa using hi⟩).trans
        (congrArg (fun x => (M.neighbors x).length) (lab _))

theorem stacked_row_iff (K : KratochvilVaner) (ds : List Nat) (large : 4≤ds.length) :
    Row ds ↔ HasStackedRealization ds :=
  (serial_iff K ds large).trans (TargetStackedBridge.sequential_iff ds).symm

private def K₃ : Graph 3 := Graph.ofRelation (fun i j => decide (i≠j))

private theorem triangle_shape (G : Graph 3) (h : ThreeTree G) :
    List.ofFn G.degree=[2,2,2] := by
  obtain ⟨_,σ,clique,_⟩ := h
  have all (i j : Fin 3) : G.adj i j=decide (i≠j) := by
    by_cases diff : i=j
    · subst j;simp [Graph.adj_self]
    · have step := clique (σ.symm i) (σ.symm j) (σ.symm i).isLt (σ.symm j).isLt
          (σ.symm.injective.ne diff)
      simpa [diff] using step
  have val (i : Fin 3) : G.degree i=2 := by
    unfold Graph.degree
    rw [funext (all i)]
    fin_cases i <;> decide
  simp only [funext val]
  rfl

private theorem triangle_row : Row [2,2,2] := by
  have tree : ThreeTree K₃ := by
    refine ⟨by decide,Equiv.refl _,?_,?_⟩
    · decide
    · intro i hi;exact False.elim (Nat.not_le.mpr i.isLt hi)
  have flat : K₃.Planar := (Wagner.planar_iff_rotation _).mpr
    (LeanPool.K5MinorFreeChoosability.isPlanar_of_card_le_four
     (S:=Finset.univ) (fun _ _ _ => Finset.mem_univ _) (by decide))
  exact ⟨3,K₃,flat,tree,by rw [triangle_shape _ tree]⟩

theorem small_iff (ds : List Nat) (small : ds.length<4) :
    Row ds ↔ ds.Perm [2,2,2] := by
  constructor
  · rintro ⟨n,G,_,tree,shape⟩
    have len : n=ds.length := by simpa using congrArg Multiset.card shape
    have lower := tree.1
    have eq : n=3 := by omega
    clear len
    subst n
    rw [triangle_shape _ tree] at shape
    exact Quotient.exact shape.symm
  · intro perm
    obtain ⟨n,G,p,tree,shape⟩ := triangle_row
    exact ⟨n,G,p,tree,shape.trans (Quotient.sound perm.symm)⟩

def ordinaryCheck (ds : List Nat) (bs : List Bool) : Bool :=
  if ds.length<4 then ds.isPerm [2,2,2] else (StackedCertificate.verify ds bs).value

theorem full_certificate (K : KratochvilVaner) (ds : List Nat) :
    Row ds ↔ ∃ bs : List Bool,bs.length≤3*ds.length ∧ ordinaryCheck ds bs=true := by
  by_cases small : ds.length<4
  · rw [small_iff ds small]
    simp only [ordinaryCheck,small,ite_true,List.isPerm_iff]
    exact ⟨fun good => ⟨[],Nat.zero_le _,good⟩,fun ⟨_,_,good⟩ => good⟩
  · simpa only [ordinaryCheck,small,ite_false] using
      (serial_iff K ds (by omega)).trans (StackedCertificate.certificate ds)

theorem sat_reduction (K : KratochvilVaner) (bs : List Bool) :
    SATBridge.SATLanguage bs ↔ Wire.degreeLanguage Row (SATCost.run bs).1 := by
  obtain ⟨ds,parsed,valid,_⟩ := HardnessResult.restricted bs
  have n:=valid.1
  have sat := (TargetLanguages.reductions bs).2.1
  rw [SATCost.run_value] at sat ⊢
  simp only [Wire.degreeLanguage,parsed,Option.some.injEq,exists_eq_left',
    stacked_row_iff K ds (by omega)] at sat ⊢
  exact sat

end Recognition.ThreeTreeClass
