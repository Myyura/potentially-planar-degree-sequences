import RecognizingPotentiallyPlanarDegreeSequences.SupportCore

namespace RecognizingPotentiallyPlanarDegreeSequences.Support
open SparseBoundary SparseBoundary.Graph

 theorem vsum_term (f : Fin n → Nat) (i : Fin n) : f i≤vsum f := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [vsum_succ]; refine Fin.cases (by omega) (fun j => ?_) i
    have := ih (fun x => f x.succ) j; omega

theorem vsum_eq_zero {f : Fin n → Nat} (h : vsum f=0) : f=fun _ => 0 := by
  funext i; have := vsum_term f i; omega

theorem vsum_peel {f : Fin n → Nat} {m : Nat} (h : vsum f=m+1) :
    ∃ x g, f=(fun i => g i+hit i x) ∧ vsum g=m := by
  have hx : ∃ x, 0<f x := by
    apply Classical.byContradiction; intro no
    have z : f=fun _ => 0 := funext (fun i => by have ni : ¬ 0<f i := fun h => no ⟨i,h⟩; omega)
    rw [z,vsum_zeros] at h; omega
  obtain ⟨x,hx⟩ := hx
  let g i := f i-hit i x
  have eqn : f=(fun i => g i+hit i x) := by
    funext i; by_cases eq : i=x <;> simp_all [g,hit] <;> omega
  refine ⟨x,g,eqn,?_⟩
  have e := congrArg vsum eqn; rw [vsum_add,vsum_hit] at e; omega

theorem row_two_units {f : Fin n → Nat} (h : vsum f=2) :
  ∃ a b, f=(fun i => hit i a+hit i b) := by
  obtain ⟨b,g,eqn,g1⟩ := vsum_peel (m:=1) h
  obtain ⟨a,z,eqg,z0⟩ := vsum_peel (m:=0) g1
  rw [vsum_eq_zero z0] at eqg
  exact ⟨a,b,by simpa [eqg] using eqn⟩

namespace Multi

def ofGraph : {n : Nat} → Graph n → Multi n
 | 0,_ => .nil
 | _+1,G => .cons 0 (fun i => (G.adj 0 i.succ).toNat) (ofGraph (G.restrict Fin.succ))

@[simp] theorem ofGraph_support (G : Graph n) : (ofGraph G).support=G := by
  induction n with
  | zero => apply eq_of_adj; intro i; exact i.elim0
  | succ n ih =>
    apply eq_of_adj; intro i j
    refine Fin.cases ?_ (fun u => ?_) i <;> refine Fin.cases ?_ (fun v => ?_) j <;>
      simp [ofGraph,support,incident,ih,G.adj_comm _ 0] <;> grind

@[simp] theorem ofGraph_cost (G : Graph n) : (ofGraph G).cost=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have z (i : Fin n) : (G.adj 0 i.succ).toNat-present (G.adj 0 i.succ).toNat=0 := by
      cases G.adj 0 i.succ <;> rfl
    simp [ofGraph,cost,ih,z]

theorem count_true (r : Fin n → Bool) : vsum (fun i => (r i).toNat)=((List.finRange n).filter r).length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [vsum_succ,List.finRange_succ,List.filter_cons,List.filter_map]
    have t := ih (fun i => r i.succ)
    cases h : r 0 <;> simp [Function.comp_def,t,Nat.add_comm]

private theorem pos_toNat (b : Bool) : decide (0<b.toNat)=b := by cases b <;> rfl

@[simp] theorem ofGraph_degree (G : Graph n) (i : Fin n) : (ofGraph G).degree i=G.degree i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    have eqn := congrArg (fun g : Graph (n+1) => g.degree i) (ofGraph_support G)
    rw [ofGraph,support,ofGraph_support] at eqn
    rw [← eqn]
    refine Fin.cases ?_ (fun v => ?_) i
    · simp [ofGraph,degree,degree_adjoin_zero,count_true,pos_toNat]
    · simp [ofGraph,degree,degree_adjoin_succ,ih,pos_toNat]

theorem addEdge_pairs_mono (M : Multi n) (a b : Fin n) : M.pairs≤(M.addEdge a b).pairs := by
  induction M with
  | nil => exact Fin.elim0 a
  | cons L row rest ih =>
    have up (x) := vsum_le (fun i => present (row i)) (fun i => present (bump row x i))
      (fun i => by unfold present bump; omega)
    refine Fin.cases ?_ (fun x => ?_) a <;> refine Fin.cases ?_ (fun y => ?_) b <;>
      simp [addEdge,pairs] <;> first | exact up _ | exact ih ..

theorem addEdge_cost_le (M : Multi n) (a b : Fin n) :
  (M.addEdge a b).cost≤M.cost+1+hit a b := by
  have h := M.cost_identity
  have u := (M.addEdge a b).cost_identity
  rw [addEdge_edges,addEdge_loops] at u
  have := addEdge_pairs_mono M a b; omega

theorem tail_planar {M : Multi n} {L : Nat} {r : Fin n → Nat}
    (hp : (cons L r M).support.Planar) : M.support.Planar :=
  planar_subgraph_map hp Fin.succ (fun _ _ => Fin.succ_inj.mp)
    (fun i j e => by simpa [support,incident] using e)

/-- Smooth a weighted degree-two vertex. Two copies to the same neighbour
become a loop, and a component that has become a single loop disappears. -/
theorem suppress_one (M : Multi (n+1)) (hp : M.support.Planar) (deg : M.degree 0=2) :
  ∃ K : Multi n, K.support.Planar ∧ (∀ i, K.degree i=M.degree i.succ) ∧ K.cost≤M.cost+1 := by
  cases M with | cons L row rest =>
    change 2*L+vsum row=2 at deg
    by_cases hz : L=0
    · subst L
      obtain ⟨a,b,eqn⟩ := row_two_units (by omega : vsum row=2)
      subst row
      refine ⟨rest.addEdge a b,?_,fun i => by simp [addEdge_degree,degree,Nat.add_assoc],?_⟩
      · apply contract_planar hp a
        · simp [support,incident,hit]; omega
        intro i j e
        have choice := Bool.or_eq_true_iff.mp ((rest.addEdge_adj a b i j).symm ▸ e)
        rcases choice with old|new
        · exact ⟨i.succ,Or.inl rfl,j.succ,Or.inl rfl,by simpa [support,incident] using old⟩
        · simp [linked] at new
          rcases new.2 with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
          · exact ⟨0,Or.inr ⟨rfl,rfl⟩,_,Or.inl rfl,by simp [support,incident,hit]⟩
          · exact ⟨_,Or.inl rfl,0,Or.inr ⟨rfl,rfl⟩,by simp [support,incident,hit]⟩
      · have h := addEdge_cost_le rest a b
        simp only [cost,Nat.mul_zero,Nat.zero_add]
        by_cases eq : a=b
        · subst b
          have k := vsum_term (fun i => (hit i a+hit i a)-present (hit i a+hit i a)) a
          simp [hit,present] at k h ⊢; omega
        · simp [hit,eq] at h; omega
    · have z : vsum row=0 := by omega
      rw [vsum_eq_zero z] at *
      exact ⟨rest,tail_planar hp,fun _ => by simp [degree],by simp [cost]; omega⟩

/-- Suppression proceeds on actual ordinary graphs, without a presumed path
partition, suppressing pure degree-two components as part of the same induction. -/
theorem suppress_twos (t : Nat) (d : List Nat) (P : Planaric (List.replicate t 2++d)) :
  ∃ M : Multi d.length, M.support.Planar ∧ (∀ i, M.degree i=d[i]) ∧ M.cost≤t := by
  obtain ⟨G,real,plan⟩ := P
  let S := ofGraph G
  have general (k : Nat) (M : Multi (List.replicate k 2++d).length) (hp : M.support.Planar)
      (hd : ∀ i : Fin _, M.degree i=(List.replicate k 2++d)[i]) :
      ∃ R : Multi d.length, R.support.Planar ∧ (∀ i, R.degree i=d[i]) ∧ R.cost≤M.cost+k := by
    induction k with
    | zero => exact ⟨M,hp,hd,by omega⟩
    | succ k ih =>
      simp only [List.replicate_succ,List.cons_append] at M hd hp ⊢
      obtain ⟨K,pk,dk,ck⟩ := suppress_one M hp (hd 0)
      obtain ⟨R,pr,dr,cr⟩ := ih K pk (fun i => (dk i).trans (hd i.succ))
      exact ⟨R,pr,dr,by omega⟩
  simpa [S] using general t S (by simpa [S] using plan) (fun i => by simpa [S] using real i)

end Multi
end RecognizingPotentiallyPlanarDegreeSequences.Support
