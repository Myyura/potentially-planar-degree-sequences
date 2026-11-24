import Combined.SupportSuppress

namespace Combined.Support
open SparseBoundary SparseBoundary.Graph

/-- Select exactly `k` of the incidences in a finite row. -/
theorem take_row (f : Fin n → Nat) (k : Nat) (le : k≤vsum f) :
  ∃ g : Fin n → Nat, (∀ i, g i≤f i) ∧ vsum g=k := by
  generalize hm : vsum f=m at *
  induction m generalizing f with
  | zero => exact ⟨f,fun _ => Nat.le_refl _,by omega⟩
  | succ m ih =>
    by_cases hk : k=m+1
    · exact ⟨f,fun _ => Nat.le_refl _,by omega⟩
    obtain ⟨x,g,e,hg⟩ := vsum_peel hm
    obtain ⟨r,hr,hs⟩ := ih g hg (by omega)
    exact ⟨r,fun i => by rw [e]; exact Nat.le_trans (hr i) (Nat.le_add_right ..),hs⟩

namespace Multi

/-- Submultigraph of the same labelled vertex set, keeping arbitrary
multiplicities of the original nonloop classes and loops. -/
def Sub : (M K : Multi n) → Prop
 | .nil, .nil => True
 | .cons L r M, .cons A s K => L≤A ∧ (∀ i, r i≤s i) ∧ M.Sub K

theorem sub_degree {M K : Multi n} (le : M.Sub K) (i : Fin n) : M.degree i≤K.degree i := by
  induction M with
  | nil => exact i.elim0
  | cons L r rest ih => cases K with | cons A s tail =>
    obtain ⟨ll,rs,sub⟩ := le
    refine Fin.cases ?_ (fun i => ?_) i
    · change 2*L+vsum r≤2*A+vsum s; have := vsum_le r s rs; omega
    · exact Nat.add_le_add (ih sub i) (rs i)

theorem sub_cost {M K : Multi n} (le : M.Sub K) : M.cost≤K.cost := by
  induction M with
  | nil => cases K; omega
  | cons L r rest ih => cases K with | cons A s tail =>
    obtain ⟨ll,rs,sub⟩ := le
    have c := ih sub
    have z := vsum_le (fun i => r i-present (r i)) (fun i => s i-present (s i))
      (fun i => by have := rs i; unfold present; omega)
    simp only [cost]; omega

theorem sub_adj {M K : Multi n} (le : M.Sub K) (i j : Fin n) (e : M.support.adj i j=true) :
  K.support.adj i j=true := by
  induction M with
  | nil => exact i.elim0
  | cons L r rest ih => cases K with | cons A s tail =>
    obtain ⟨_,rs,sub⟩ := le
    revert e
    refine Fin.cases ?_ (fun x => ?_) i <;> refine Fin.cases ?_ (fun y => ?_) j <;>
      simp [support,incident] <;> first | exact fun e => ih sub _ _ e | grind

theorem sub_planar {M K : Multi n} (le : M.Sub K) (pk : K.support.Planar) : M.support.Planar :=
  planar_subgraph_map pk id (fun _ _ e => e) (sub_adj le)

/-- Any prescribed number of edge occurrences may be retained. In
particular deleting a sole adjacency costs zero, deleting a parallel copy
saves one subdivision, and deleting a loop saves two. -/
theorem take_edges (M : Multi n) (k : Nat) (le : k≤M.edges) :
  ∃ K : Multi n, K.Sub M ∧ K.edges=k := by
  induction M generalizing k with
  | nil => exact ⟨.nil,True.intro,by simp [edges] at le ⊢; omega⟩
  | cons L row rest ih =>
    let l := min L k
    let s := min (vsum row) (k-l)
    have ll : l≤L := Nat.min_le_left ..
    obtain ⟨r,rr,rs⟩ := take_row row s (Nat.min_le_left ..)
    have left : k-l-s≤rest.edges := by simp only [edges] at le; dsimp [l,s]; omega
    obtain ⟨T,st,ts⟩ := ih _ left
    refine ⟨.cons l r T,⟨ll,rr,st⟩,?_⟩
    simp only [edges,rs,ts]; dsimp [s,l]; omega

/-- Strip labelled leaves. A leaf whose neighbour was removed earlier may
already be isolated. At each step at most one edge occurrence is lost,
and the remaining vertices' degrees and the subdivision cost only fall. -/
theorem strip_leaves (ell : Nat) (h : List Nat) (M : Multi (List.replicate ell 1++h).length)
    (hp : M.support.Planar) (dh : ∀ i : Fin _, M.degree i≤(List.replicate ell 1++h)[i]) :
    ∃ K : Multi h.length, K.support.Planar ∧ (∀ i, K.degree i≤h[i]) ∧
      K.cost≤M.cost ∧ M.edges≤K.edges+ell := by
  induction ell with
  | zero => exact ⟨M,hp,dh,by omega,by omega⟩
  | succ l ih =>
    simp only [List.replicate_succ,List.cons_append] at M dh hp ⊢
    cases M with | cons L row rest =>
      have head := dh 0
      change 2*L+vsum row≤1 at head
      have dr (i : Fin ((List.replicate l (1 : Nat)++h).length)) : rest.degree i≤(List.replicate l 1++h)[i.val]'i.isLt := by
        have hh := dh i.succ
        change rest.degree i+row i≤(List.replicate l 1++h)[i] at hh; exact Nat.le_trans (Nat.le_add_right ..) hh
      obtain ⟨K,pk,dk,ck,ek⟩ := ih rest (tail_planar hp) dr
      exact ⟨K,pk,dk,by simp only [cost]; omega,by simp only [edges]; omega⟩

/-- A precise certificate for the paper's normalized core. After removal
of all leaves, every excess remaining core edge corresponds to one isolated
leaf pair. Erasing that many edges preserves the capacities and planarity;
reattaching the deficits supplies two pendant leaves for each erased edge. -/
structure Candidate (h : List Nat) (ell : Nat) where
  graph : Multi h.length
  planar : graph.support.Planar
  capacity : ∀ i, graph.degree i≤h[i]
  balance : 2*graph.edges+ell=h.sum

 theorem normalize {h : List Nat} {ell t : Nat} (enough : ell≤h.sum)
    (even : (h.sum+ell)%2=0)
    (P : Planaric (List.replicate t 2++h++List.replicate ell 1)) :
    ∃ C : Candidate h ell, C.graph.cost≤t := by
  have perm := (List.perm_append_comm (l₁:=h) (l₂:=List.replicate ell 1)).append_left (List.replicate t 2)
  rw [List.append_assoc] at P
  obtain ⟨M,pl,deg,cm⟩ := suppress_twos t (List.replicate ell 1++h) ((planaric_perm perm).mp P)
  obtain ⟨K,pk,dk,ck,ek⟩ := strip_leaves ell h M pl (fun i => Nat.le_of_eq (deg i))
  have hs := M.handshake
  have dl : List.ofFn M.degree=List.replicate ell 1++h := by
    apply List.ext_getElem; · simp
    intro i hi hj; simpa using deg ⟨i,hj⟩
  unfold vsum at hs
  rw [dl,List.sum_append,List.sum_replicate_nat] at hs
  let e := (h.sum-ell)/2
  have le : e≤K.edges := by dsimp [e]; omega
  obtain ⟨Q,sq,qe⟩ := take_edges K e le
  refine ⟨⟨Q,sub_planar sq pk,fun i => Nat.le_trans (sub_degree sq i) (dk i),?_⟩,
    Nat.le_trans (sub_cost sq) (Nat.le_trans ck cm)⟩
  rw [qe]; dsimp [e]; omega

end Multi
end Combined.Support
