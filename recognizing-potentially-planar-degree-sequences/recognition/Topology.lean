import Frontier

/-!
A tree--cotree proof of the Euler inequality using only finite graphs.
Both the primal and dual edges carry permanent edge identifiers, so multiple
edges of the dual are harmless.
-/
namespace PlanarDegrees.Topology
open Frontier

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

private noncomputable def makeTree {k : Nat} {E : Type}
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

private theorem Tree.injective {k : Nat} {E : Type} {ends : E → Fin (k+1) × Fin (k+1)}
    {keep : E → Prop} (T : Tree ends keep) : Function.Injective T.pick := by
  intro i j he
  obtain ⟨_,p,hp,lp⟩ := T.choice i
  obtain ⟨_,q,hq,lq⟩ := T.choice j
  rw [he] at hp
  rcases hp with h|h <;> rcases hq with g|g <;> rw [h] at g <;>
    simp only [Prod.mk.injEq] at g <;> grind [Fin.succ_inj]

/-- Local condition supplied by a polygonal face: after deleting any one of
its sides, its other sides still give a walk between that side's endpoints. -/
def FaceBypass {v f e : Nat}
    (primal : Fin e → Fin (v+1) × Fin (v+1))
    (dual : Fin e → Fin (f+1) × Fin (f+1)) : Prop :=
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
    (htri : FaceBypass primal dual) (T : Tree dual (fun _ => True)) :
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

/-- Choose a dual tree and construct a primal tree entirely in its complement. -/
private theorem tree_pair {v f e : Nat}
    (primal : Fin e → Fin (v+1) × Fin (v+1)) (dual : Fin e → Fin (f+1) × Fin (f+1))
    (pc : ∀ x, Walk (Adj primal (fun _ => True)) 0 x)
    (dc : ∀ x, Walk (Adj dual (fun _ => True)) 0 x) (htri : FaceBypass primal dual) :
    ∃ D : Tree dual (fun _ => True), ∃ P : Tree primal (fun d => ∀ i, D.pick i ≠ d),
      ((List.finRange v).map P.pick ++ (List.finRange f).map D.pick).Nodup := by
  classical
  let D := makeTree dual _ dc
  let keep := fun d => ∀ i, D.pick i ≠ d
  have conn (x) : Walk (Adj primal keep) 0 x := by
    apply walk_substitute _ (pc x)
    intro a b h
    obtain ⟨edge,_,hadj⟩ := h
    exact as_walk hadj (tree_complement htri D edge)
  let P := makeTree primal keep conn
  have distinct {k : Nat} (g : Fin k → Fin e) (hi : Function.Injective g) :
      ((List.finRange k).map g).Nodup := by
    apply List.pairwise_map.mpr
    exact (List.nodup_finRange _).imp (fun h e => h (hi e))
  let selected := (List.finRange v).map P.pick ++ (List.finRange f).map D.pick
  have nd : selected.Nodup := by
    apply List.nodup_append.mpr
    refine ⟨distinct _ P.injective, distinct _ D.injective, ?_⟩
    intro a ha b hb eq
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
    exact (P.choice i).1 j eq.symm
  exact ⟨D,P,nd⟩

/-- Finite primal/dual Euler bound. The assumptions describe incidence and
connectivity. No Euler inequality or classification of surfaces is assumed. -/
theorem cellular_euler_bound {v f e : Nat}
    (primal : Fin e → Fin (v+1) × Fin (v+1)) (dual : Fin e → Fin (f+1) × Fin (f+1))
    (pc : ∀ x, Walk (Adj primal (fun _ => True)) 0 x)
    (dc : ∀ x, Walk (Adj dual (fun _ => True)) 0 x) (htri : FaceBypass primal dual) :
    (v+1) + (f+1) ≤ e+2 := by
  obtain ⟨_,_,nd⟩ := tree_pair primal dual pc dc htri
  have h := nd.length_le_of_subset (l₂ := List.finRange e) (fun x _ => List.mem_finRange _)
  simp at h
  omega

/-- At characteristic two the two selected trees exhaust every edge. -/
theorem tree_cotree_cover {v f e : Nat}
    (primal : Fin e → Fin (v+1) × Fin (v+1)) (dual : Fin e → Fin (f+1) × Fin (f+1))
    (pc : ∀ x, Walk (Adj primal (fun _ => True)) 0 x)
    (dc : ∀ x, Walk (Adj dual (fun _ => True)) 0 x) (htri : FaceBypass primal dual)
    (equality : (v+1)+(f+1) = e+2) :
    ∃ D : Tree dual (fun _ => True), ∃ P : Tree primal (fun d => ∀ i, D.pick i ≠ d),
      ∀ edge, (∃ i, P.pick i = edge) ∨ (∃ i, D.pick i = edge) := by
  classical
  obtain ⟨D,P,nd⟩ := tree_pair primal dual pc dc htri
  refine ⟨D,P,fun edge => ?_⟩
  let selected := (List.finRange v).map P.pick ++ (List.finRange f).map D.pick
  have hmem : edge ∈ selected := by
    apply Classical.byContradiction
    intro absent
    have hn := List.nodup_cons.mpr ⟨absent,nd⟩
    have h := hn.length_le_of_subset (l₂ := List.finRange e) (fun x _ => List.mem_finRange _)
    simp [selected] at h
    omega
  simpa [selected] using hmem

end PlanarDegrees.Topology

namespace PlanarDegrees.Topology
open Frontier

/-- A face with three vertex labels and three permanent edge identifiers. -/
structure Triangle (V E : Type) where
  a : V
  b : V
  c : V
  ab : E
  bc : E
  ca : E

def Triangle.sides {V E : Type} (t : Triangle V E) : List E := [t.ab,t.bc,t.ca]
def Triangle.corners {V E : Type} (t : Triangle V E) : List V := [t.a,t.b,t.c]

/-- All data of the closed triangular gluing are finite. The dual endpoint
of an edge is the face instance on that side; duplicate triangles with
different face identities are allowed. -/
structure Gluing (v f e : Nat) where
  primal : Fin e → Fin (v+1) × Fin (v+1)
  dual : Fin e → Fin (f+1) × Fin (f+1)
  tri : Fin (f+1) → Triangle (Fin (v+1)) (Fin e)
  sidesDistinct : ∀ z, (tri z).sides.Nodup
  abEnds : ∀ z, Across primal (tri z).ab (tri z).a (tri z).b
  bcEnds : ∀ z, Across primal (tri z).bc (tri z).b (tri z).c
  caEnds : ∀ z, Across primal (tri z).ca (tri z).c (tri z).a
  used : ∀ x, ∃ z, x ∈ (tri z).corners
  faceSide : ∀ z d, incident dual d z ↔ d ∈ (tri z).sides
  twoFaces : ∀ d, (dual d).1 ≠ (dual d).2
  dualConnected : ∀ z, Walk (Adj dual (fun _ => True)) 0 z

private theorem via_two {V E : Type} {ends : E → V × V} {keep : E → Prop}
    {e₁ e₂ : E} {x y z : V} (ha : Across ends e₁ x y) (hb : Across ends e₂ y z)
    (h₁ : keep e₁) (h₂ : keep e₂) : Walk (Adj ends keep) x z :=
  (Walk.refl.step ⟨_, h₁, ha⟩).step ⟨_, h₂, hb⟩

private theorem along_edge {V E : Type} {ends : E → V × V} {keep : E → Prop}
    {d : E} {x y : V} (ha : Across ends d x y) (p : Walk (Adj ends keep) x y) :
    Walk (Adj ends keep) (ends d).1 (ends d).2 := by
  rcases ha with h|h <;> rw [h]
  · exact p
  · exact p.symm (fun _ _ h => adjSymm h)

theorem Gluing.bypass {v f e : Nat} (G : Gluing v f e) : FaceBypass G.primal G.dual := by
  intro z d hd
  have hab := G.abEnds z
  have hbc := G.bcEnds z
  have hca := G.caEnds z
  have nd := G.sidesDistinct z
  simp [Triangle.sides] at nd
  have side := (G.faceSide z d).mp hd
  simp only [Triangle.sides, List.mem_cons, List.not_mem_nil, or_false] at side
  rcases side with rfl|rfl|rfl
  · apply along_edge hab.symm
    apply via_two hbc hca <;> simp_all [G.faceSide, Triangle.sides] <;> grind
  · apply along_edge hbc.symm
    apply via_two hca hab <;> simp_all [G.faceSide, Triangle.sides] <;> grind
  · apply along_edge hca.symm
    apply via_two hab hbc <;> simp_all [G.faceSide, Triangle.sides] <;> grind

private theorem Gluing.cornerWalk {v f e : Nat} (G : Gluing v f e) (z : Fin (f+1))
    {x : Fin (v+1)} (hx : x ∈ (G.tri z).corners) :
    Walk (Adj G.primal (fun _ => True)) (G.tri z).a x := by
  simp [Triangle.corners] at hx
  rcases hx with rfl|rfl|rfl
  · exact .refl
  · exact .step .refl ⟨_,trivial,G.abEnds z⟩
  · exact .step .refl ⟨_,trivial,(G.caEnds z).symm⟩

private theorem Gluing.common_corner {v f e : Nat} (G : Gluing v f e) (z : Fin (f+1))
    (d : Fin e) (hd : incident G.dual d z) : (G.primal d).1 ∈ (G.tri z).corners := by
  have side := (G.faceSide z d).mp hd
  simp only [Triangle.sides, List.mem_cons, List.not_mem_nil, or_false] at side
  rcases side with rfl|rfl|rfl
  · rcases G.abEnds z with hh|hh <;> simp [hh,Triangle.corners]
  · rcases G.bcEnds z with hh|hh <;> simp [hh,Triangle.corners]
  · rcases G.caEnds z with hh|hh <;> simp [hh,Triangle.corners]

theorem Gluing.primalConnected {v f e : Nat} (G : Gluing v f e) (x : Fin (v+1)) :
    Walk (Adj G.primal (fun _ => True)) 0 x := by
  have faces (z : Fin (f+1)) :
      Walk (Adj G.primal (fun _ => True)) (G.tri 0).a (G.tri z).a := by
    have w := G.dualConnected z
    induction w with
    | refl => exact .refl
    | @step i j _ edge ih =>
      obtain ⟨d,_,hh⟩ := edge
      have hits : incident G.dual d i ∧ incident G.dual d j := by
        rcases hh with hh|hh <;> simp [incident,hh]
      have p := G.cornerWalk i (G.common_corner i d hits.1)
      have q := G.cornerWalk j (G.common_corner j d hits.2)
      exact (ih.trans p).trans (q.symm (fun _ _ h => adjSymm h))
  have all (y : Fin (v+1)) : Walk (Adj G.primal (fun _ => True)) (G.tri 0).a y := by
    obtain ⟨z,hz⟩ := G.used y
    exact (faces z).trans (G.cornerWalk z hz)
  exact ((all 0).symm (fun _ _ h => adjSymm h)).trans (all x)

theorem Gluing.euler_le_two {v f e : Nat} (G : Gluing v f e) :
    (v+1) + (f+1) ≤ e+2 :=
  cellular_euler_bound G.primal G.dual G.primalConnected G.dualConnected G.bypass

private theorem sum_const {α : Type} (xs : List α) (k : Nat) :
    (xs.map (fun _ => k)).sum = k*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.mul_add,Nat.add_comm]

private theorem sum_counts {α : Type} [DecidableEq α] (ys xs : List α) :
    (xs.map (fun a => ys.count a)).sum = (ys.map (fun a => xs.count a)).sum := by
  induction ys with
  | nil => simp [sum_const]
  | cons y ys ih =>
    have addOne (xs : List α) :
        (xs.map (fun a => (y::ys).count a)).sum =
          xs.count y + (xs.map (fun a => ys.count a)).sum := by
      induction xs with
      | nil => simp
      | cons x xs ih' =>
        by_cases he : x=y <;> simp_all [List.count_cons, Ne.symm, Nat.add_left_comm,
          Nat.add_assoc]
    rw [addOne,ih]
    simp

private theorem Gluing.sides_count {v f e : Nat} (G : Gluing v f e) (d : Fin e) :
    ((List.finRange (f+1)).flatMap (fun z => (G.tri z).sides)).count d = 2 := by
  let zs := List.finRange (f+1)
  rw [List.count_flatMap]
  have key (z : Fin (f+1)) :
      ((G.tri z).sides.count d) = ([(G.dual d).1, (G.dual d).2].count z) := by
    have hnd : [(G.dual d).1,(G.dual d).2].Nodup := by simp [G.twoFaces d]
    rw [(G.sidesDistinct z).count, hnd.count]
    simp only [← G.faceSide, incident, List.mem_cons, List.not_mem_nil, or_false]
    grind
  change (zs.map (fun z => (G.tri z).sides.count d)).sum = 2
  simp only [key]
  rw [sum_counts]
  simp [zs,(List.nodup_finRange _).count_of_mem (List.mem_finRange _)]

/-- Three triangle sides per face and exactly two incident faces per edge. -/
theorem Gluing.incidence_count {v f e : Nat} (G : Gluing v f e) : 3*(f+1) = 2*e := by
  let sides := (List.finRange (f+1)).flatMap (fun z => (G.tri z).sides)
  have length3 (zs : List (Fin (f+1))) :
      (zs.flatMap (fun z => (G.tri z).sides)).length = 3*zs.length := by
    induction zs with
    | nil => simp
    | cons z zs ih =>
      simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, Nat.mul_add]
      simp [Triangle.sides, Nat.add_comm]
  have len := length3 (List.finRange (f+1))
  change sides.length = _ at len
  simp only [List.length_finRange] at len
  have c (d : Fin e) : sides.count d = 2 := G.sides_count d
  have h := sum_counts sides (List.finRange e)
  simp [c,(List.nodup_finRange _).count_of_mem (List.mem_finRange _),sum_const] at h
  omega

/-- An accepted Euler count leaves no room for extra vertices in a gluing
with split links. This theorem derives the surface inequality and the
edge/face count from triangular incidence data. -/
theorem no_extra_vertices {n extra v f e : Nat} (G : Gluing v f e)
    (order : v+1 = n+extra) (faces : (f+1)+4 = 2*n) : extra = 0 := by
  have := G.euler_le_two
  have := G.incidence_count
  omega

end PlanarDegrees.Topology

namespace PlanarDegrees.Topology
open Frontier

/-- Link adjacency on face instances around a vertex: the two faces meet
along a side incident with that vertex. -/
def Gluing.link {v f e : Nat} (G : Gluing v f e) (x : Fin (v+1))
    (a b : Fin (f+1)) : Prop :=
  ∃ d, incident G.primal d x ∧ Across G.dual d a b

def Triangle.mapCorners {V V' E : Type} (t : Triangle V E) (φ : V → V') :
    Triangle V' E := ⟨φ t.a,φ t.b,φ t.c,t.ab,t.bc,t.ca⟩

private theorem mapCorners_mem {V V' E : Type} {t : Triangle V E} {u : V}
    (φ : V → V') (h : u ∈ t.corners) : φ u ∈ (t.mapCorners φ).corners := by
  simp [Triangle.corners] at h
  rcases h with rfl|rfl|rfl <;> simp [Triangle.mapCorners,Triangle.corners]

/-- Splitting the chosen vertex according to a proper cut in its link.
Every side keeps exactly the same two incident faces. -/
private noncomputable def splitVertex {v f e : Nat} (G : Gluing v f e)
    (x : Fin (v+1)) (marked : Fin (f+1) → Prop)
    (stable : ∀ a b, G.link x a b → (marked a ↔ marked b))
    {z₀ z₁ : Fin (f+1)} (hz₀ : x ∈ (G.tri z₀).corners) (h₀ : marked z₀)
    (hz₁ : x ∈ (G.tri z₁).corners) (h₁ : ¬marked z₁) : Gluing (v+1) f e := by
  classical
  let lift (z : Fin (f+1)) (y : Fin (v+1)) : Fin ((v+1)+1) :=
    if y = x ∧ marked z then Fin.last _ else y.castSucc
  let primal (d : Fin e) := Prod.map (lift (G.dual d).1) (lift (G.dual d).1) (G.primal d)
  let tri (z : Fin (f+1)) := (G.tri z).mapCorners (lift z)
  have agree {d z u} (hd : incident G.dual d z) (hu : incident G.primal d u) :
      lift (G.dual d).1 u = lift z u := by
    by_cases eq : u = x
    · subst u
      rcases hd with h|h
      · rw [h]
      · subst z
        have hmark := stable _ _ (show G.link x (G.dual d).1 (G.dual d).2 from ⟨d,hu,Or.inl rfl⟩)
        simp only [lift, true_and, hmark]
    · simp [lift,eq]
  have ends {d z u w} (hd : d ∈ (G.tri z).sides) (hw : Across G.primal d u w) :
      Across primal d (lift z u) (lift z w) := by
    have hi := (G.faceSide _ _).mpr hd
    have hu : incident G.primal d u := by rcases hw with h|h <;> simp [incident,h]
    have hv : incident G.primal d w := by rcases hw with h|h <;> simp [incident,h]
    rcases hw with h|h
    · exact Or.inl (by simp [primal,h,agree hi hu,agree hi hv])
    · exact Or.inr (by simp [primal,h,agree hi hu,agree hi hv])
  refine {
    primal := primal, dual := G.dual, tri := tri
    sidesDistinct := G.sidesDistinct
    abEnds := fun z => ends (by simp [tri,Triangle.mapCorners,Triangle.sides]) (G.abEnds z)
    bcEnds := fun z => ends (by simp [tri,Triangle.mapCorners,Triangle.sides]) (G.bcEnds z)
    caEnds := fun z => ends (by simp [tri,Triangle.mapCorners,Triangle.sides]) (G.caEnds z)
    used := ?_, faceSide := G.faceSide, twoFaces := G.twoFaces, dualConnected := G.dualConnected }
  intro y
  refine Fin.lastCases ?_ (fun u => ?_) y
  · exact ⟨z₀,by simpa [tri,lift,h₀] using mapCorners_mem (lift z₀) hz₀⟩
  · by_cases same : u = x
    · subst u
      exact ⟨z₁,by simpa [tri,lift,h₁] using mapCorners_mem (lift z₁) hz₁⟩
    · obtain ⟨z,hz⟩ := G.used u
      exact ⟨z,by simpa [tri,lift,same] using mapCorners_mem (lift z) hz⟩

/-- At the accepting face count, all faces incident to a vertex lie in a
single component of its link. The proof constructs the split gluing and
uses the tree--cotree bound, without a surface-classification hypothesis. -/
theorem Gluing.links_connected {v f e : Nat} (G : Gluing v f e)
    (terminal : (f+1)+4 = 2*(v+1)) (x : Fin (v+1)) (a b : Fin (f+1))
    (ha : x ∈ (G.tri a).corners) (hb : x ∈ (G.tri b).corners) :
    Walk (G.link x) a b := by
  classical
  apply Classical.byContradiction
  intro bad
  let marked := fun z => Walk (G.link x) a z
  have stable (i j) (h : G.link x i j) : marked i ↔ marked j := by
    obtain ⟨d,hi,he⟩ := h
    exact ⟨fun p => p.step ⟨_,hi,he⟩, fun p => p.step ⟨_,hi,he.symm⟩⟩
  let split := splitVertex G x marked stable ha Walk.refl hb bad
  have hu := split.euler_le_two
  have hc := G.incidence_count
  omega

end PlanarDegrees.Topology

namespace PlanarDegrees.Topology
open Frontier

def sideNames (F : Face) := F.sides.map Event.edge
def cornerNames (F : Face) := [F.x,F.y,F.z]

def sideTrace {f : Nat} (faces : Fin (f+1) → Face) :=
  (List.finRange (f+1)).flatMap (fun i => (faces i).sides)

def shared {f : Nat} (faces : Fin (f+1) → Face) (i j : Fin (f+1)) : Prop :=
  i ≠ j ∧ ∃ d, d ∈ sideNames (faces i) ∧ d ∈ sideNames (faces j)

theorem face_fiber_length {f : Nat} (faces : Fin (f+1) → Face) (d : Edge) :
    ((List.finRange (f+1)).filter (fun i => decide (d ∈ sideNames (faces i)))).length =
      occurrences (sideTrace faces) d := by
  have H (zs : List (Fin (f+1))) :
      (zs.filter (fun i => decide (d ∈ sideNames (faces i)))).length =
      occurrences (zs.flatMap (fun i => (faces i).sides)) d := by
    induction zs with
    | nil => simp [occurrences]
    | cons i zs ih =>
      have hnd : (sideNames (faces i)).Nodup := (faces i).distinct_sides
      simp only [occurrences, List.flatMap_cons, List.map_append, List.count_append] at *
      change _ = (sideNames (faces i)).count d + _
      by_cases h : d ∈ sideNames (faces i) <;> simp [h, hnd.count, ih, Nat.add_comm]
  exact H _

/-- Data extracted from a closed, face-connected labelled trace. The first
two conditions on the vertex names say exactly that its used vertices are
0 through v. The replay checks all open and sealed edge transitions. -/
structure ClosedTrace (v f : Nat) where
  faces : Fin (f+1) → Face
  bounded : ∀ i, (faces i).z < v+1
  used : ∀ x : Fin (v+1), ∃ i, x.val ∈ cornerNames (faces i)
  connected : ∀ i, Walk (shared faces) 0 i
  ledger : Inventory
  accepted : replay (sideTrace faces) = some ledger
  closed : ledger.pending = []

private theorem ClosedTrace.seen_iff {v f} (C : ClosedTrace v f) (d : Edge) :
    d ∈ C.ledger.sealed ↔ ∃ z, d ∈ sideNames (C.faces z) := by
  have acc := replay_accurate C.accepted
  rw [acc.sealed]
  have no1 := acc.pending d
  simp [C.closed] at no1
  have cap := acc.cap d
  have m : d ∈ (sideTrace C.faces).map Event.edge ↔ ∃ z, d ∈ sideNames (C.faces z) := by
    simp [sideTrace, sideNames, List.mem_flatMap]
    grind
  rw [← m, ← List.count_pos_iff]
  change occurrences _ _ = 2 ↔ 0 < occurrences _ _
  omega

private theorem exactly_two {α : Type} {xs : List α} (h : xs.length = 2) (nd : xs.Nodup) :
    ∃ a b, a ≠ b ∧ xs = [a,b] := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs =>
      have he : xs.length = 0 := by simp only [List.length_cons] at h; omega
      have := List.length_eq_zero_iff.mp he
      subst xs
      exact ⟨a,b,by simpa using nd,rfl⟩

private theorem ClosedTrace.dual_ends {v f} (C : ClosedTrace v f) {d : Edge}
    (hd : d ∈ C.ledger.sealed) :
    ∃ p : Fin (f+1) × Fin (f+1), p.1 ≠ p.2 ∧
      ∀ z, (p.1=z ∨ p.2=z) ↔ d ∈ sideNames (C.faces z) := by
  let zs := (List.finRange (f+1)).filter (fun i => decide (d ∈ sideNames (C.faces i)))
  have hl : zs.length = 2 := (face_fiber_length C.faces d).trans (((replay_accurate C.accepted).sealed d).mp hd)
  have hn : zs.Nodup := (List.nodup_finRange _).filter _
  obtain ⟨a,b,hab,hs⟩ := exactly_two hl hn
  refine ⟨(a,b),hab,?_⟩
  intro z
  have mem : z ∈ zs ↔ d ∈ sideNames (C.faces z) := by simp [zs]
  rw [hs] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  grind

/-- Extract finite primal and dual incidences from the actual side trace.
Vertex names and the endpoint pairs in the accepted ledger are preserved. -/
theorem ClosedTrace.gluing {v f} (C : ClosedTrace v f) :
    ∃ G : Gluing v f C.ledger.sealed.length,
      (∀ z, (G.tri z).corners.map Fin.val = cornerNames (C.faces z)) ∧
      (∀ d, ((G.primal d).1.val,(G.primal d).2.val) =
        ((C.ledger.sealed[d.val]).lo,(C.ledger.sealed[d.val]).hi)) := by
  classical
  let keys := C.ledger.sealed
  have nd : keys.Nodup := (inventory_counts C.accepted).2.1
  let code (d : Edge) (hd : d ∈ keys) : Fin keys.length := ⟨keys.idxOf d, List.idxOf_lt_length_of_mem hd⟩
  let key (d : Fin keys.length) : Edge := keys[d.val]
  have decode (d : Edge) (hd : d ∈ keys) : key (code d hd) = d := List.getElem_idxOf _
  have named (d : Fin keys.length) : key d ∈ C.ledger.sealed := List.getElem_mem _
  have keyinj {i j} (h : key i = key j) : i = j := by
    have hi := nd.idxOf_getElem i.val i.isLt
    have hj := nd.idxOf_getElem j.val j.isLt
    apply Fin.ext
    change keys.idxOf (key i) = i.val at hi
    change keys.idxOf (key j) = j.val at hj
    rw [h] at hi
    omega
  let namedSide (z) (d : Edge) (hd : d ∈ sideNames (C.faces z)) := code d ((C.seen_iff _).mpr ⟨z,hd⟩)
  let F := C.faces
  let xy (z) : Edge := ⟨(F z).x, (F z).y, (F z).xy⟩
  let yz (z) : Edge := ⟨(F z).y, (F z).z, (F z).yz⟩
  let xz (z) : Edge := ⟨(F z).x, (F z).z, Nat.lt_trans (F z).xy (F z).yz⟩
  have names (z) : sideNames (C.faces z) = [xy z,xz z,yz z] := rfl
  have bound (d : Fin keys.length) : (key d).hi < v+1 := by
    obtain ⟨z,hz⟩ := (C.seen_iff _).mp (named d)
    rw [names] at hz
    have bz := C.bounded z
    have hy := (F z).yz
    change (F z).z < v+1 at bz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with hh|hh|hh <;> rw [hh] <;> first | exact bz | exact Nat.lt_trans hy bz
  let primal (d : Fin keys.length) : Fin (v+1) × Fin (v+1) :=
    (⟨(key d).lo,Nat.lt_trans (key d).increasing (bound d)⟩,⟨(key d).hi,bound d⟩)
  let de := fun d => C.dual_ends (named d)
  let dual := fun d => (de d).choose
  have inc (d z) : incident dual d z ↔ key d ∈ sideNames (C.faces z) := (de d).choose_spec.2 z
  let tri (z) : Triangle (Fin (v+1)) (Fin keys.length) := {
    a := ⟨(F z).x,Nat.lt_trans (Nat.lt_trans (F z).xy (F z).yz) (C.bounded z)⟩
    b := ⟨(F z).y,Nat.lt_trans (F z).yz (C.bounded z)⟩
    c := ⟨(F z).z,C.bounded z⟩
    ab := namedSide z (xy z) (by simp [names])
    bc := namedSide z (yz z) (by simp [names])
    ca := namedSide z (xz z) (by simp [names]) }
  have ab (z) : key (tri z).ab = xy z := decode _ ((C.seen_iff _).mpr ⟨z,by simp [names]⟩)
  have bc (z) : key (tri z).bc = yz z := decode _ ((C.seen_iff _).mpr ⟨z,by simp [names]⟩)
  have ca (z) : key (tri z).ca = xz z := decode _ ((C.seen_iff _).mpr ⟨z,by simp [names]⟩)
  have sideEq (z d) : key d ∈ sideNames (C.faces z) ↔ d ∈ (tri z).sides := by
    rw [names, ← ab z, ← ca z, ← bc z]
    simp [Triangle.sides]
    grind
  have corners (z) : (tri z).corners.map Fin.val = cornerNames (C.faces z) := rfl
  refine ⟨{
    primal := primal, dual := dual, tri := tri
    sidesDistinct := ?_, abEnds := ?_, bcEnds := ?_, caEnds := ?_, used := ?_,
    faceSide := fun z d => (inc _ _).trans (sideEq _ _), twoFaces := fun d => (de d).choose_spec.1,
    dualConnected := ?_ },corners,fun _ => rfl⟩
  · intro z
    have n := (C.faces z).distinct_sides
    change (sideNames (C.faces z)).Nodup at n
    rw [names, ← ab z, ← ca z, ← bc z] at n
    simp [Triangle.sides] at *
    grind
  · intro z
    left
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Edge.lo (ab z)
    · exact congrArg Edge.hi (ab z)
  · intro z
    left
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Edge.lo (bc z)
    · exact congrArg Edge.hi (bc z)
  · intro z
    right
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Edge.lo (ca z)
    · exact congrArg Edge.hi (ca z)
  · intro x
    obtain ⟨z,hz⟩ := C.used x
    rw [← corners z] at hz
    obtain ⟨u,hu,equ⟩ := List.mem_map.mp hz
    exact ⟨z,Fin.ext equ ▸ hu⟩
  · intro z
    apply walk_substitute _ (C.connected z)
    intro i j ⟨hne,d,hi,hj⟩
    let ix := namedSide i d hi
    have hh : key ix = d := decode _ ((C.seen_iff _).mpr ⟨i,hi⟩)
    have h₁ := (inc ix i).mpr (hh ▸ hi)
    have h₂ := (inc ix j).mpr (hh ▸ hj)
    have ha : Across dual ix i j := by
      rcases h₁ with a|a <;> rcases h₂ with b|b <;> simp [Across,Prod.ext_iff] <;> grind
    exact .step .refl ⟨ix,trivial,ha⟩

end PlanarDegrees.Topology

namespace PlanarDegrees.Topology
open Frontier

/-- A vertex that has already appeared and will appear again meets an open
side for every prefix of a terminal gluing. Here `read` may be any set of
face instances, so the statement covers every ordering and every prefix. -/
theorem Gluing.live_corner {v f e : Nat} (G : Gluing v f e)
    (terminal : (f+1)+4 = 2*(v+1)) (read : Fin (f+1) → Prop)
    (x : Fin (v+1)) {a b : Fin (f+1)}
    (ha : x ∈ (G.tri a).corners) (hb : x ∈ (G.tri b).corners) (ra : read a) (rb : ¬read b) :
    ∃ d, incident G.primal d x ∧
      ((read (G.dual d).1 ∧ ¬read (G.dual d).2) ∨
       (read (G.dual d).2 ∧ ¬read (G.dual d).1)) := by
  classical
  have h := G.links_connected terminal x a b ha hb
  apply Classical.byContradiction
  intro hn
  apply rb
  clear rb hb
  induction h with
  | refl => exact ra
  | @step i j _ edge ih =>
    obtain ⟨d,inc,hh⟩ := edge
    by_cases hread : read j
    · exact hread
    · apply False.elim
      apply hn
      refine ⟨d,inc,?_⟩
      rcases hh with eq|eq <;> simp [eq,ih,hread]

/-- The terminal trace has the same red degrees as its simple red edge list.
Its triangles admit incidence tables with the original labels, two faces per
edge, and connected links at every vertex. -/
theorem ClosedTrace.terminal_certificate {v f : Nat} (C : ClosedTrace v f)
    (terminal : (f+1)+4 = 2*(v+1)) :
    (∀ x, C.ledger.redDegree x = simpleDegree (reds (sideTrace C.faces)) x) ∧
    (reds (sideTrace C.faces)).Nodup ∧
    ∃ G : Gluing v f C.ledger.sealed.length,
      (∀ z, (G.tri z).corners.map Fin.val = cornerNames (C.faces z)) ∧
      (∀ d, ((G.primal d).1.val,(G.primal d).2.val) =
        ((C.ledger.sealed[d.val]).lo,(C.ledger.sealed[d.val]).hi)) ∧
      (∀ x a b, x ∈ (G.tri a).corners → x ∈ (G.tri b).corners → Walk (G.link x) a b) := by
  obtain ⟨G,hf,he⟩ := C.gluing
  exact ⟨(replay_accurate C.accepted).redDegree, reds_nodup _, G, hf, he, G.links_connected terminal⟩

/-- For a sequence of labelled faces, pairing each appearing side exactly
twice is equivalent to successful edge replay with no open edges. -/
theorem paired_iff_closed {p : List Event} :
    (∀ e, occurrences p e = 0 ∨ occurrences p e = 2) ↔
    ∃ s, replay p = some s ∧ s.pending = [] := by
  constructor
  · intro paired
    obtain ⟨s,hs⟩ := (replay_succeeds_iff p).mpr (fun e => by rcases paired e with h|h <;> omega)
    refine ⟨s,hs,?_⟩
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    have h₁ := ((replay_accurate hs).pending e).mp he
    rcases paired e with h|h <;> omega
  · intro ⟨s,hs,hclosed⟩ e
    have h₁ := (replay_accurate hs).pending e
    have h₂ := (replay_accurate hs).cap e
    simp [hclosed] at h₁
    omega

end PlanarDegrees.Topology
