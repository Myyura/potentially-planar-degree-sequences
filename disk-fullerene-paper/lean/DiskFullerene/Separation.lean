import Std

/-! Finite edge separation on the sphere. The shortest-path tree and
complementary-tree argument adapt the workspace's Frontier.lean and
Topology.lean. Here the first tree can be prescribed to avoid a specified
edge set. This proves a separation result for that set, as opposed to
the existence of some tree-cotree partition. -/
namespace DiskFullerene.Separation

inductive Walk {α : Type} (R : α → α → Prop) (a : α) : α → Prop
  | refl : Walk R a a
  | step {b c : α} : Walk R a b → R b c → Walk R a c

namespace Walk

theorem trans {α : Type} {R : α → α → Prop} {a b c : α} (h : Walk R a b)
    (k : Walk R b c) : Walk R a c := by
  induction k with
  | refl => exact h
  | step _ edge ih => exact ih.step edge

theorem symm {α : Type} {R : α → α → Prop} (rs : ∀ a b, R a b → R b a)
    {a b : α} (p : Walk R a b) : Walk R b a := by
  induction p with
  | refl => exact .refl
  | step _ edge ih => exact (Walk.step Walk.refl (rs _ _ edge)).trans ih

end Walk

def Across {V E : Type} (ends : E → V × V) (e : E) (x y : V) : Prop :=
  ends e = (x,y) ∨ ends e = (y,x)

def incident {V E : Type} (ends : E → V × V) (e : E) (x : V) : Prop :=
  (ends e).1 = x ∨ (ends e).2 = x

def Adj {V E : Type} (ends : E → V × V) (keep : E → Prop) (x y : V) : Prop :=
  ∃ e, keep e ∧ Across ends e x y

private theorem adjSymm {V E : Type} {ends : E → V × V} {keep : E → Prop}
    {x y : V} (h : Adj ends keep x y) : Adj ends keep y x := by
  obtain ⟨e, he, hxy⟩ := h
  exact ⟨e, he, hxy.symm⟩

inductive Steps {V : Type} (R : V → V → Prop) (r : V) : Nat → V → Prop
  | zero : Steps R r 0 r
  | next {n a b} : Steps R r n a → R a b → Steps R r (n+1) b

private theorem steps_exist {V : Type} {R : V → V → Prop} {r x : V} (h : Walk R r x) :
    ∃ n, Steps R r n x := by
  induction h with
  | refl => exact ⟨_,.zero⟩
  | step _ e ih =>
    obtain ⟨n,hn⟩ := ih
    exact ⟨_,.next hn e⟩

private theorem minimum {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ k, P k → n ≤ k := by
  classical
  obtain ⟨n,hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases less : ∃ k, k<n ∧ P k
    · obtain ⟨k,hk,hp⟩ := less
      exact ih k hk hp
    · exact ⟨n, hn, fun k hp => by
        by_cases hk : k<n
        · exact False.elim (less ⟨k,hk,hp⟩)
        · omega⟩

structure Tree {k : Nat} {E : Type} (ends : E → Fin (k+1) × Fin (k+1)) (keep : E → Prop) where
  height : Fin (k+1) → Nat
  pick : Fin k → E
  choice : ∀ i, keep (pick i) ∧ ∃ p, Across ends (pick i) i.succ p ∧ height p < height i.succ

noncomputable def makeTree {k : Nat} {E : Type}
    (ends : E → Fin (k+1) × Fin (k+1)) (keep : E → Prop)
    (conn : ∀ x, Walk (Adj ends keep) 0 x) : Tree ends keep := by
  classical
  let has := fun x => minimum (steps_exist (conn x))
  let height := fun x => (has x).choose
  have hd (x) : Steps (Adj ends keep) 0 (height x) x ∧
      ∀ t, Steps (Adj ends keep) 0 t x → height x ≤ t := (has x).choose_spec
  have child (i : Fin k) : ∃ e, keep e ∧ ∃ p, Across ends e i.succ p ∧ height p < height i.succ := by
    generalize hh : height i.succ = n
    have hp := (hd i.succ).1
    rw [hh] at hp
    generalize hx : i.succ = x at hp
    cases hp with
    | zero => exact False.elim (i.succ_ne_zero hx)
    | @next t p u prev adj =>
      obtain ⟨e,he,ha⟩ := adj
      exact ⟨e,he,p,ha.symm,by have := (hd p).2 t prev; omega⟩
  exact ⟨height, fun i => (child i).choose, fun i => (child i).choose_spec⟩

theorem Tree.injective {k : Nat} {E : Type} {ends : E → Fin (k+1) × Fin (k+1)}
    {keep : E → Prop} (T : Tree ends keep) : Function.Injective T.pick := by
  intro i j he
  obtain ⟨_,p,hp,lp⟩ := T.choice i
  obtain ⟨_,q,hq,lq⟩ := T.choice j
  rw [he] at hp
  rcases hp with h|h <;> rcases hq with g|g <;> rw [h] at g <;>
    simp only [Prod.mk.injEq] at g <;> grind [Fin.succ_inj]

/-- Local condition supplied by a polygonal face: after deleting any one of
its sides, its other sides still give a walk between that side's endpoints. -/
def FaceBypass {V F E : Type}
    (primal : E → V × V)
    (dual : E → F × F) : Prop :=
  ∀ face edge, incident dual edge face →
    Walk (Adj primal (fun d => d ≠ edge ∧ incident dual d face))
      (primal edge).1 (primal edge).2

private theorem walk_substitute {V : Type} {R S : V → V → Prop}
    (sub : ∀ a b, R a b → Walk S a b) {a b} (p : Walk R a b) : Walk S a b := by
  induction p with
  | refl => exact .refl
  | step _ he ih => exact ih.trans (sub _ _ he)

private theorem le_sum {x : Nat} {xs : List Nat} (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h with eq|hin
    · omega
    · have := ih hin; omega

private theorem as_walk {V E : Type} {ends : E → V × V} {keep : E → Prop}
    {e : E} {x y : V} (a : Across ends e x y)
    (p : Walk (Adj ends keep) (ends e).1 (ends e).2) : Walk (Adj ends keep) x y := by
  rcases a with h|h <;> rw [h] at p
  · exact p
  · exact p.symm (fun _ _ h => adjSymm h)

private theorem tree_complement {v f e : Nat}
    {primal : Fin e → Fin (v+1) × Fin (v+1)} {dual : Fin e → Fin (f+1) × Fin (f+1)}
    {allowed : Fin e → Prop} (htri : FaceBypass primal dual) (T : Tree dual allowed) :
    ∀ edge, Walk (Adj primal (fun d => ∀ i, T.pick i ≠ d)) (primal edge).1 (primal edge).2 := by
  classical
  let keep := fun d => ∀ i, T.pick i ≠ d
  let bound := ((List.finRange (f+1)).map T.height).sum
  have hb (x : Fin (f+1)) : T.height x ≤ bound :=
    le_sum (List.mem_map.mpr ⟨x, List.mem_finRange x, rfl⟩)
  have subtree (i : Fin f) :
      Walk (Adj primal keep) (primal (T.pick i)).1 (primal (T.pick i)).2 := by
    generalize hs : bound - T.height i.succ = n
    induction n using Nat.strongRecOn generalizing i with
    | ind n ih =>
      obtain ⟨_,p,hep,_⟩ := T.choice i
      have hi : incident dual (T.pick i) i.succ := by
        rcases hep with hh|hh <;> simp [incident,hh]
      apply walk_substitute _ (htri i.succ (T.pick i) hi)
      intro a b h
      obtain ⟨d,⟨hne,hinc⟩,hadj⟩ := h
      by_cases hd : keep d
      · exact .step .refl ⟨d,hd,hadj⟩
      · have hused : ∃ j, T.pick j = d := by simpa [keep] using hd
        obtain ⟨j,rfl⟩ := hused
        obtain ⟨_,q,hq,hlt⟩ := T.choice j
        have hji : j ≠ i := by intro he; subst j; exact hne rfl
        have hqeq : q = i.succ := by
          rcases hq with hh|hh <;> simp [incident,hh,Fin.succ_inj,hji] at hinc <;> exact hinc
        rw [hqeq] at hlt
        have hsmall : bound - T.height j.succ < n := by have := hb j.succ; omega
        exact as_walk hadj (ih _ hsmall j rfl)
  intro edge
  by_cases hd : keep edge
  · exact .step .refl ⟨edge,hd,Or.inl rfl⟩
  · have hused : ∃ j, T.pick j = edge := by simpa [keep] using hd
    obtain ⟨j,rfl⟩ := hused
    exact subtree j

/-- Every edge left out of the first tree belongs to a single complementary
tree if the Euler characteristic is two. -/
theorem complement_spans {v f e : Nat}
    {primal : Fin e → Fin (v+1) × Fin (v+1)} {dual : Fin e → Fin (f+1) × Fin (f+1)}
    {keep : Fin e → Prop} (T : Tree primal keep)
    (dc : ∀ x, Walk (Adj dual (fun _ => True)) 0 x)
    (vb : FaceBypass dual primal) (sphere : v+f=e) :
    ∃ D : Tree dual (fun d => ∀ i, T.pick i ≠ d),
      ∀ edge, (∃ i, T.pick i = edge) ∨ ∃ j, D.pick j = edge := by
  classical
  let allowed := fun d => ∀ i, T.pick i ≠ d
  have conn (x) : Walk (Adj dual allowed) 0 x := by
    apply walk_substitute _ (dc x)
    rintro a b ⟨d,_,h⟩
    exact as_walk h (tree_complement vb T d)
  let D := makeTree dual allowed conn
  refine ⟨D,?_⟩
  have distinct {k} (g : Fin k → Fin e) (inj : Function.Injective g) :
      ((List.finRange k).map g).Nodup :=
    List.pairwise_map.mpr ((List.nodup_finRange _).imp (fun h eq => h (inj eq)))
  let allEdges := (List.finRange v).map T.pick ++ (List.finRange f).map D.pick
  have unique : allEdges.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨distinct T.pick T.injective,distinct D.pick D.injective,?_⟩
    intro a ha b hb hab
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
    exact (D.choice j).1 i hab
  intro d
  have full : d ∈ allEdges := by
    apply Classical.byContradiction
    intro missing
    have nd := List.nodup_cons.mpr ⟨missing,unique⟩
    have bound := nd.length_le_of_subset (l₂ := List.finRange e) (fun x _ => List.mem_finRange x)
    simp [allEdges] at bound
    omega
  simpa [allEdges] using full

/-- A nonempty subset of a tree's edges has a leaf, even when the ambient
multigraph has other edges between the same two vertices. -/
theorem Tree.hasLeaf {n e} {ends : Fin e → Fin (n+1) × Fin (n+1)} {keep}
    (T : Tree ends keep) (S : Fin e → Prop) (nonempty : ∃ t, S t)
    (used : ∀ t, S t → ∃ i, T.pick i = t) :
    ∃ t x, S t ∧ incident ends t x ∧ ∀ u, S u → incident ends u x → u=t := by
  classical
  let bound := ((List.finRange (n+1)).map T.height).sum
  have hb (x) : T.height x ≤ bound :=
    le_sum (List.mem_map.mpr ⟨x,List.mem_finRange _,rfl⟩)
  obtain ⟨t,ht⟩ := nonempty
  obtain ⟨i,hi⟩ := used t ht
  let deficit := fun (a : Fin n) => bound - T.height a.succ
  have existsDef : ∃ d, ∃ a : Fin n, S (T.pick a) ∧ deficit a = d :=
    ⟨deficit i,i,hi ▸ ht,rfl⟩
  obtain ⟨d,⟨a,ha,had⟩,least⟩ := minimum existsDef
  obtain ⟨_,p,hp,lt⟩ := T.choice a
  refine ⟨T.pick a,a.succ,ha,by rcases hp with h|h <;> simp [incident,h],?_⟩
  intro u hu atA
  obtain ⟨j,rfl⟩ := used u hu
  by_cases eq : j=a
  · exact congrArg T.pick eq
  · have ne : j.succ ≠ a.succ := fun h => eq (Fin.succ_inj.mp h)
    obtain ⟨_,q,hq,ltj⟩ := T.choice j
    have qeq : q=a.succ := by rcases hq with h|h <;> simpa [incident,h,ne] using atA
    rw [qeq] at ltj
    have lower := least (deficit j) ⟨j,hu,rfl⟩
    have := hb j.succ
    dsimp [deficit] at had lower
    omega

/-- A dual cycle separates. The hypothesis on marked edges also permits
unions of cycles and, in particular, the cycle of two parallel edges.
The conclusion is failure of primal connectivity after removal. -/
theorem separates {v f e : Nat}
    {primal : Fin e → Fin (v+1) × Fin (v+1)} {dual : Fin e → Fin (f+1) × Fin (f+1)}
    (sphere : v+f=e) (dc : ∀ x, Walk (Adj dual (fun _ => True)) 0 x)
    (vb : FaceBypass dual primal) {S : Fin e → Prop} (has : ∃ d, S d)
    (two : ∀ d, S d → ∀ x, incident dual d x → ∃ d', S d' ∧ incident dual d' x ∧ d'≠d) :
    ¬ (∀ x, Walk (Adj primal (fun d => ¬ S d)) 0 x) := by
  intro pc
  let T := makeTree primal (fun d => ¬ S d) pc
  obtain ⟨D,cover⟩ := complement_spans T dc vb sphere
  have marked (d) (hd : S d) : ∃ j, D.pick j = d := by
    rcases cover d with ⟨i,rfl⟩ | h
    · exact False.elim ((T.choice i).1 hd)
    · exact h
  obtain ⟨d,x,hd,inc,unique⟩ := D.hasLeaf S has marked
  obtain ⟨d',hd',inc',ne⟩ := two d hd x inc
  exact ne (unique d' hd' inc')

theorem parallel_edges_separate {v f e : Nat}
    {primal : Fin e → Fin (v+1) × Fin (v+1)} {dual : Fin e → Fin (f+1) × Fin (f+1)}
    (sphere : v+f=e) (dc : ∀ x, Walk (Adj dual (fun _ => True)) 0 x)
    (vb : FaceBypass dual primal) {a b : Fin e} (ne : a ≠ b)
    (same : ∀ x, incident dual a x ↔ incident dual b x) :
    ¬ (∀ x, Walk (Adj primal (fun d => ¬(d=a ∨ d=b))) 0 x) := by
  apply separates sphere dc vb (S := fun d => d=a ∨ d=b) ⟨a,Or.inl rfl⟩
  rintro d (rfl|rfl) x inc
  · exact ⟨b,Or.inr rfl,(same x).mp inc,Ne.symm ne⟩
  · exact ⟨a,Or.inl rfl,(same x).mpr inc,ne⟩

theorem separates_on_sphere {v f e : Nat}
    {primal : Fin e → Fin v × Fin v} {dual : Fin e → Fin f × Fin f}
    (nv : 0 < v) (nf : 0 < f) (chi : v+f=e+2)
    (dc : ∀ i j, Walk (Adj dual (fun _ => True)) i j)
    (vb : FaceBypass dual primal) {S : Fin e → Prop} (has : ∃ d, S d)
    (two : ∀ d, S d → ∀ x, incident dual d x → ∃ d', S d' ∧ incident dual d' x ∧ d'≠d) :
    ¬ (∀ i j, Walk (Adj primal (fun d => ¬ S d)) i j) := by
  cases v with
  | zero => omega
  | succ v =>
    cases f with
    | zero => omega
    | succ f =>
      intro conn
      exact separates (by omega) (dc 0) vb has two (conn 0)

theorem parallel_of_sphere {v f e : Nat}
    {primal : Fin e → Fin v × Fin v} {dual : Fin e → Fin f × Fin f}
    (nv : 0 < v) (nf : 0 < f) (chi : v+f=e+2)
    (dc : ∀ i j, Walk (Adj dual (fun _ => True)) i j)
    (vb : FaceBypass dual primal) {a b : Fin e} (ne : a ≠ b)
    (same : ∀ x, incident dual a x ↔ incident dual b x) :
    ¬ (∀ i j, Walk (Adj primal (fun d => ¬(d=a ∨ d=b))) i j) := by
  cases v with
  | zero => omega
  | succ v =>
    cases f with
    | zero => omega
    | succ f =>
      intro conn
      exact parallel_edges_separate (by omega) (dc 0) vb ne same (conn 0)

end DiskFullerene.Separation
