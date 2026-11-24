import Combined.FixedBudget
import Connectivity
import Mathlib.Logic.Equiv.Basic

/-! Cyclic allocation of each face generation on an arbitrary simple
realization. Renaming the first generation supplies prescribed nonedges. -/
namespace Combined.FixedBudget
open SparseBoundary SparseBoundary.Graph Recognition

private theorem avoid_rows {n b k : Nat} (rs : Fin n → List (Fin b)) (kn : k≤n) (kb : k≤b)
    (room : ∀ x, (rs x).length+k≤b) : ∃ σ : Equiv.Perm (Fin b),
      ∀ i (hi : i<k), σ ⟨i,by omega⟩ ∉ rs ⟨i,by omega⟩ := by
  induction k with
  | zero => exact ⟨Equiv.refl _,by omega⟩
  | succ k ih =>
    obtain ⟨σ,good⟩ := ih (by omega) (by omega) (fun x => by have := room x; omega)
    let old : List (Fin b) := List.ofFn (fun i : Fin k => σ ⟨i.val,by omega⟩)
    let x : Fin n := ⟨k,by omega⟩
    let y : Fin b := ⟨k,by omega⟩
    have fresh : ∃ c : Fin b, c ∉ (rs x++old) := by
      apply Classical.byContradiction; intro no
      have sub : List.finRange b ⊆ rs x++old := fun a _ => Classical.byContradiction (fun h => no ⟨a,h⟩)
      have cap := (List.nodup_finRange b).length_le_of_subset sub
      have bound := room x; simp [old] at cap; omega
    obtain ⟨c,hc⟩ := fresh
    have cc : c ∉ rs x ∧ c ∉ old := by simpa using hc
    refine ⟨σ.trans (Equiv.swap (σ y) c),fun i hi => ?_⟩
    by_cases eq : i=k
    · subst i; simpa [y,x] using cc.1
    · have ik : i<k := by omega
      have notY : σ ⟨i,by omega⟩≠σ y := fun e => eq (congrArg Fin.val (σ.injective e))
      have noC : σ ⟨i,by omega⟩ ≠ c := by
        intro e; apply cc.2; exact List.mem_ofFn.mpr ⟨⟨i,ik⟩,e⟩
      simpa [Equiv.swap_apply_of_ne_of_ne notY noC] using good i ik

private def wire (G : Graph n) (rows : Fin n → List (Fin b)) (σ : Equiv.Perm (Fin b)) :
    Fin (n+b) → Fin (n+b) → Bool :=
  Fin.addCases (fun x => Fin.addCases (G.adj x) (fun j => (rows x).contains (σ j)))
    (fun j => Fin.addCases (fun x => (rows x).contains (σ j)) (fun _ => false))

private def circuit (G : Graph n) (rs : Fin n → List (Fin b)) (σ : Equiv.Perm (Fin b)) :=
  ofRelation (wire G rs σ)

private theorem circuit_adj (G : Graph n) (rs : Fin n → List (Fin b)) (σ : Equiv.Perm (Fin b))
    (i j : Fin (n+b)) : (circuit G rs σ).adj i j=wire G rs σ i j := by
  apply adj_ofRelation
  · intro u v
    refine Fin.addCases ?_ ?_ u <;> intro x <;> refine Fin.addCases ?_ ?_ v <;> intro y <;>
      simp [wire,G.adj_comm]
  · intro v; refine Fin.addCases ?_ ?_ v <;> intro x <;> simp [wire]

private theorem circuit_pair (G : Graph n) (rs : Fin n → List (Fin b)) (σ : Equiv.Perm (Fin b)) (x y : Fin n) :
    (circuit G rs σ).adj (x.castAdd b) (y.castAdd b)=G.adj x y := by rw [circuit_adj]; simp [wire]

private theorem circuit_cross (G : Graph n) (rs : Fin n → List (Fin b)) (σ : Equiv.Perm (Fin b)) (x : Fin n) (j : Fin b) :
    (circuit G rs σ).adj (x.castAdd b) (j.natAdd n)=(rs x).contains (σ j) := by rw [circuit_adj]; simp [wire]

private theorem circuit_old (G : Graph n) (rs : Fin n → List (Fin b)) (σ : Equiv.Perm (Fin b))
    (x : Fin n) (nd : (rs x).Nodup) :
    (circuit G rs σ).degree (x.castAdd b)=G.degree x+(rs x).length := by
  have perm : ((List.finRange b).map σ).Perm (List.finRange b) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange b).map σ.injective) (List.nodup_finRange _)).mpr
    intro i; simpa using σ.surjective i
  have members : ((List.finRange b).filter (rs x).contains).Perm (rs x) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange b).filter _) nd).mpr; simp
  have size := ((perm.filter (rs x).contains).trans members).length_eq
  rw [List.filter_map,List.length_map] at size
  unfold Graph.degree; rw [union_range n b]
  simpa [List.filter_map,Function.comp_def,circuit_adj,wire] using congrArg (G.degree x+·) size

private theorem circuit_new (G : Graph n) (rs : Fin n → List (Fin b)) (σ : Equiv.Perm (Fin b))
    (j : Fin b) : (circuit G rs σ).degree (j.natAdd n)=
      ((List.finRange n).filter (fun x => (rs x).contains (σ j))).length := by
  unfold Graph.degree; rw [union_range n b]; simp [List.filter_map,Function.comp_def,circuit_adj,wire]

private theorem rows_of_allocation {d : List Nat} (dv : Reduction.TableValid d) :
    ∃ rs : Fin d.length → List (Fin (2*d.length-4)), (∀ i, (rs i).length=d[i] ∧ (rs i).Nodup) ∧
      ∀ j, ((List.finRange d.length).filter (fun i => (rs i).contains j)).length=3 := by
  have n := dv.1
  obtain ⟨R,size,nd,c⟩ := Connectivity.cyclic_allocation (2*d.length-4) (by omega) d
    (fun x hx => by have := (dv.2.2 x hx).2; omega) (by have := dv.2.1; omega)
  have len : R.length=d.length := by simpa using congrArg List.length size
  let rs (i : Fin d.length) := R[i.val]'(by omega)
  have same : (List.finRange d.length).map rs=R := by
    apply List.ext_getElem; · simp [len]
    intros; simp [rs]
  refine ⟨rs,fun i => ⟨?_,nd _ (List.getElem_mem _)⟩,fun j => ?_⟩
  · have h := congrArg (fun s : List Nat => s[i.val]?) size
    simpa [rs,List.getElem?_map,List.getElem?_eq_getElem (by omega : i.val<R.length),List.getElem?_eq_getElem i.isLt] using h
  · have h := c j; rw [←same,List.filter_map,List.length_map] at h; exact h

/-- Natural-number lookup for transporting old edges through dimension changes. -/
def adjAt (G : Graph n) (i j : Nat) : Bool := if h : i<n ∧ j<n then G.adj ⟨i,h.1⟩ ⟨j,h.2⟩ else false

theorem adjAt_fin (G : Graph n) (u v : Fin n) : adjAt G u.val v.val=G.adj u v := by simp [adjAt,u.isLt,v.isLt]

private theorem cast_graph {k m : Nat} (eq : m=k) (G : Graph m) (f : Nat → Nat) (deg : ∀ i : Fin m, G.degree i=f i.val) :
   ∃ H : Graph k, (∀ i, H.degree i=f i.val) ∧ ∀ i j, adjAt H i j=adjAt G i j := by
  subst k; exact ⟨G,deg,fun _ _ => rfl⟩

private theorem full_graph_step {d : List Nat} (dv : Reduction.TableValid d) (r : Nat)
    (fit : r+3≤d.length) (G : Graph d.length) (rg : G.Realizes d) :
    ∃ H : Graph (full d).length, H.Realizes (full d) ∧
      (∀ i<d.length, ∀ j<d.length, adjAt H i j=adjAt G i j) ∧
      ∀ i<r, adjAt H i (d.length+i)=false := by
  let b := 2*d.length-4
  obtain ⟨rs,rows,cols⟩ := rows_of_allocation dv
  have len := full_length d
  obtain ⟨σ,avoid⟩ := avoid_rows rs (by omega : r≤d.length) (by omega : r≤2*d.length-4)
    (fun x => by have := (rows x).1; have hd : d[x]<d.length := (dv.2.2 _ (List.getElem_mem x.isLt)).2; omega)
  let H := circuit G rs σ
  let f (i : Nat) := (full d)[i]?.getD 0
  have degrees (i : Fin (d.length+b)) : H.degree i=f i.val := by
    refine Fin.addCases ?_ ?_ i
    · intro x
      have lo : x.val<(full d).length := by omega
      rw [show H.degree (x.castAdd b)=G.degree x+(rs x).length from circuit_old G rs σ x (rows x).2,rg,(rows x).1]
      simp [f,full,List.getElem?_append]
      omega
    · intro y
      rw [show H.degree (y.natAdd d.length)=_ from circuit_new G rs σ y,cols]
      have high : d.length+y.val<(full d).length := by have := y.isLt; dsimp [b] at *; omega
      simp [f,full,List.getElem?_append,List.getElem?_replicate,y.isLt,b]
  obtain ⟨K,deg,ex⟩ := cast_graph len.symm H f degrees
  refine ⟨K,fun i => by simpa [f,List.getElem?_eq_getElem i.isLt] using deg i,?_,?_⟩
  · intro i hi j hj; rw [ex]
    let x : Fin d.length := ⟨i,hi⟩; let y : Fin d.length := ⟨j,hj⟩
    change adjAt H (x.castAdd b).val (y.castAdd b).val=adjAt G x.val y.val
    rw [adjAt_fin,adjAt_fin]; exact circuit_pair G rs σ x y
  · intro i hi; rw [ex]
    let x : Fin d.length := ⟨i,by omega⟩; let y : Fin b := ⟨i,by dsimp [b]; omega⟩
    change adjAt H (x.castAdd b).val (y.natAdd d.length).val=false
    rw [adjAt_fin,circuit_cross G rs σ x y]; simpa [x,y] using avoid i hi

/-- A complete incidence round preserves ordinary graphicality, independently
of planarity or connectivity of the starting realization. -/
theorem full_graphic {d : List Nat} (valid : Reduction.TableValid d) (gr : Graphic d) :
    Graphic (full d) := by
  obtain ⟨G,rg⟩ := gr
  obtain ⟨H,rh,_,_⟩ := full_graph_step valid 0 (by have := valid.1; omega) G rg
  exact ⟨H,rh⟩

/-- An ordinary labelled simple realization of three full rounds with paired
original/first-generation labels absent, for every graphic source. -/
theorem three_full_nonedges {d : List Nat} {r : Nat} (valid : Reduction.TableValid d)
    (fit : r+3≤d.length) (graphic : Graphic d) :
    ∃ G : Graph (full (full (full d))).length, G.Realizes (full (full (full d))) ∧
      ∀ i<r, adjAt G i (d.length+i)=false := by
  obtain ⟨G,rg⟩ := graphic
  obtain ⟨A,ra,_,na⟩ := full_graph_step valid r fit G rg
  have va := full_valid valid
  obtain ⟨B,rb,keepB,_⟩ := full_graph_step va 0 (by have := va.1; omega) A ra
  have vb := full_valid va
  obtain ⟨C,rc,keepC,_⟩ := full_graph_step vb 0 (by have := vb.1; omega) B rb
  refine ⟨C,rc,fun i hi => ?_⟩
  have s := full_length d; have ss := full_length (full d)
  rw [keepC _ (by omega) _ (by omega),keepB _ (by omega) _ (by omega)]
  exact na i hi

end Combined.FixedBudget
