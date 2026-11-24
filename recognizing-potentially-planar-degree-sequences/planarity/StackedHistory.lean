import StackedQuota
import StackedReduction

/-! A shell accepted by the three-corner rule can be replayed as genuine
face insertions in the source project's labelled tetrahedral mesh. -/

namespace Recognition.StackedHistory

open SourceMap StackedQuota

/-- The disk coordinates can orient a face differently from the
representative stored by the mesh. -/
private def Fits (f : Face) (a b c : Nat) :=
  f = ⟨a,b,c⟩ ∨ f = ⟨a,c,b⟩ ∨ f = ⟨b,a,c⟩ ∨
  f = ⟨b,c,a⟩ ∨ f = ⟨c,a,b⟩ ∨ f = ⟨c,b,a⟩

private theorem Fits.rotate {f a b c} (h : Fits f a b c) : Fits f b c a := by
  unfold Fits at *
  tauto

private theorem Fits.hit {f a b c} (h : Fits f a b c) (v) :
    f.hit v ↔ v = a ∨ v = b ∨ v = c := by
  rcases h with h|h|h|h|h|h <;> subst f <;> simp [Face.hit] <;> tauto

private theorem children {M f a b c} (fit : Fits f a b c) (u : Nat) :
    ∃ g, (stack M f u).face g ∧ Fits g a b u ∧ g.c = u := by
  rcases fit with h|h|h|h|h|h <;> subst f
  · exact ⟨_, .inr (.inl rfl), .inl rfl, rfl⟩
  · exact ⟨_, .inr (.inr (.inl rfl)), .inl rfl, rfl⟩
  · exact ⟨_, .inr (.inl rfl), .inr (.inr (.inl rfl)), rfl⟩
  · exact ⟨_, .inr (.inr (.inl rfl)), .inr (.inr (.inl rfl)), rfl⟩
  · exact ⟨_, .inr (.inr (.inr rfl)), .inl rfl, rfl⟩
  · exact ⟨_, .inr (.inr (.inr rfl)), .inr (.inr (.inl rfl)), rfl⟩

private theorem distinct {f g a b c u} (first : Fits f a b u) (next : Fits g b c u)
    (ab : a ≠ b) (ac : a ≠ c) (au : a ≠ u) : f ≠ g := by
  intro eq
  have hit := (first.hit a).2 (.inl rfl)
  rw [eq, next.hit] at hit
  tauto

private structure Bounded (M : Mesh) (u : Nat) : Prop where
  hist : Stacked M
  verts : ∀ v, M.vertex v ↔ v < u
  faces : ∀ g, M.face g → g.a < u ∧ g.b < u ∧ g.c < u
  fresh : ∀ v, u ≤ v → (M.neighbors v).length = 0

private theorem push {M u f} (b : Bounded M u) (hf : M.face f) :
    Bounded (stack M f u) (u+1) := by
  obtain ⟨ha,hb,hc⟩ := b.faces f hf
  refine ⟨.insert b.hist hf (fun h => (Nat.lt_irrefl _) ((b.verts _).1 h)), ?_, ?_, ?_⟩
  · intro v
    change v = u ∨ M.vertex v ↔ v < u+1
    rw [b.verts]
    omega
  · intro g face
    rcases face with ⟨old,_⟩ | eq | eq | eq
    · obtain ⟨_,_,_⟩ := b.faces g old
      omega
    all_goals subst g; simp_all; omega
  · intro v hv
    have old := b.fresh v (by omega)
    have skip : ¬ f.hit v := by unfold Face.hit; omega
    simp [stack, show v ≠ u by omega, skip, old]

private theorem inc_add (xs ys : List (Nat × Nat)) (v : Nat) :
    incident (xs ++ ys) v = incident xs v + incident ys v := by
  simp [incident]

private theorem push_degrees {M u f a b c} (bm : Bounded M u) (fit : Fits f a b c)
    (ha : a<u) (hb : b<u) (hc : c<u) (ab : a≠b) (ac : a≠c) (bc : b≠c) (v) :
    ((stack M f u).neighbors v).length =
      (M.neighbors v).length + incident [(a,u),(b,u),(c,u)] v := by
  rw [show incident [(a,u),(b,u),(c,u)] v =
      (if v=a then 1 else 0)+(if v=u then 1 else 0)+
      ((if v=b then 1 else 0)+(if v=u then 1 else 0))+
      ((if v=c then 1 else 0)+(if v=u then 1 else 0)) by
        unfold incident
        let k := fun x => if v=x then 1 else 0
        change (k a+k u) + ((k b+k u) + ((k c+k u) + 0)) = (k a+k u)+(k b+k u)+(k c+k u)
        omega]
  by_cases eq : v=u
  · subst v
    simp [stack,bm.fresh u le_rfl, Nat.ne_of_gt ha, Nat.ne_of_gt hb, Nat.ne_of_gt hc]
  by_cases e1 : v=a <;> by_cases e2 : v=b <;> by_cases e3 : v=c <;>
    simp_all [stack, fit.hit]

/-- Fill an arbitrarily oriented current face. The procedure preserves
every other old face and records the degree change at every name. -/
private theorem fill (t : Disk) {M f a b c u} (bm : Bounded M u) (hf : M.face f)
    (fit : Fits f a b c) (ha : a<u) (hb : b<u) (hc : c<u)
    (ab : a≠b) (ac : a≠c) (bc : b≠c) :
    ∃ N : Mesh, Bounded N (u+t.size) ∧
      (∀ g, M.face g → g≠f → N.face g) ∧
      ∀ v, (N.neighbors v).length = (M.neighbors v).length + incident (t.edges a b c u) v := by
  induction t generalizing M f a b c u with
  | empty => exact ⟨M, bm, fun _ h _ => h, fun _ => by simp [Disk.edges, incident]⟩
  | split l m r ihl ihm ihr =>
    obtain ⟨fl,hfl,cl,el⟩ := children (M := M) fit u
    obtain ⟨fm,hfm,cm,em⟩ := children (M := M) fit.rotate u
    obtain ⟨fr,hfr,cr,er⟩ := children (M := M) fit.rotate.rotate u
    have lm := distinct cl cm ab ac (Nat.ne_of_lt ha)
    have mr := distinct cm cr bc ab.symm (Nat.ne_of_lt hb)
    have rl := distinct cr cl ac.symm bc.symm (Nat.ne_of_lt hc)
    obtain ⟨L, gl, kl, dl⟩ := ihl (push bm hf) hfl cl (by omega) (by omega)
      (by omega) ab (by omega) (by omega)
    obtain ⟨P, gp, kp, dp⟩ := ihm gl (kl _ hfm lm.symm) cm (by omega) (by omega)
      (by omega) bc (by omega) (by omega)
    obtain ⟨R, gr, kr, dr⟩ := ihr gp (kp _ (kl _ hfr rl) mr.symm) cr (by omega)
      (by omega) (by omega) ac.symm (by omega) (by omega)
    refine ⟨R, ?_, ?_, ?_⟩
    · simpa [Disk.size, Nat.add_assoc] using gr
    · intro g old different
      have bound := (bm.faces g old).2.2
      have away {x : Face} (endAt : x.c = u) : g ≠ x := by
        intro eq
        have := congrArg Face.c eq
        omega
      exact kr _ (kp _ (kl _ (.inl ⟨old, different⟩) (away el)) (away em)) (away er)
    · intro v
      rw [dr,dp,dl,push_degrees bm fit ha hb hc ab ac bc,Disk.edges,inc_add,inc_add,inc_add]
      omega

private theorem base : Bounded tetra 4 := by
  refine ⟨.tetra, fun _ => Iff.rfl, ?_, ?_⟩
  · intro f h
    change f.a < f.b ∧ f.b < f.c ∧ f.c < 4 at h
    omega
  · intro v hv
    simp [tetra, Nat.not_lt_of_ge hv]

private def baseEdges : List (Nat × Nat) := [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

private theorem baseDegree (v : Nat) : (tetra.neighbors v).length = incident baseEdges v := by
  cases v with
  | zero => rfl
  | succ v => cases v with
    | zero => rfl
    | succ v => cases v with
      | zero => rfl
      | succ v => cases v <;> rfl

def order (s : Shell) := 4 + s.abc.size + s.abd.size + s.acd.size + s.bcd.size

/-- Replay all four disks in their tetrahedral faces. Labels are consecutive
and the *actual* source mesh degree at each label is its incidence count in
the quota construction. This also covers four empty disks. -/
theorem shell_history (s : Shell) : ∃ M : Mesh, Stacked M ∧
    (∀ v, M.vertex v ↔ v < order s) ∧
    ∀ v, (M.neighbors v).length = incident s.edges v := by
  let abc : Face := ⟨0,1,2⟩
  let abd : Face := ⟨0,1,3⟩
  let acd : Face := ⟨0,2,3⟩
  let bcd : Face := ⟨1,2,3⟩
  have a : tetra.face abc := by simp [tetra, abc]
  have b : tetra.face abd := by simp [tetra, abd]
  have c : tetra.face acd := by simp [tetra, acd]
  have d : tetra.face bcd := by simp [tetra, bcd]
  obtain ⟨A,ga,ka,da⟩ := fill s.abc base a (.inl rfl) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨B,gb,kb,db⟩ := fill s.abd ga (ka _ b (by decide)) (.inl rfl) (by omega)
    (by omega) (by omega) (by decide) (by decide) (by decide)
  obtain ⟨C,gc,kc,dc⟩ := fill s.acd gb (kb _ (ka _ c (by decide)) (by decide)) (.inl rfl)
    (by omega) (by omega) (by omega) (by decide) (by decide) (by decide)
  obtain ⟨D,gd,_,dd⟩ := fill s.bcd gc (kc _ (kb _ (ka _ d (by decide)) (by decide)) (by decide))
    (.inl rfl) (by omega) (by omega) (by omega) (by decide) (by decide) (by decide)
  refine ⟨D, gd.hist, gd.verts, ?_⟩
  intro v
  rw [dd,dc,db,da,baseDegree,Shell.edges,inc_add,inc_add,inc_add,inc_add]
  rfl

private theorem rangeJoin (u m n : Nat) :
    List.range' u m ++ List.range' (u+m) n = List.range' u (m+n) := by
  have h := List.range'_append (s := u) (m := m) (n := n) (step := 1)
  rw [Nat.one_mul] at h
  exact h

private theorem disk_names (t : Disk) (u : Nat) : t.names u = List.range' u t.size := by
  induction t generalizing u with
  | empty => rfl
  | split l m r ihl ihm ihr =>
    simp only [Disk.names, Disk.size, ihl, ihm, ihr]
    rw [rangeJoin, show u+1+l.size+m.size = u+1+(l.size+m.size) by omega, rangeJoin,
      show 1+l.size+m.size+r.size = (l.size+m.size+r.size)+1 by omega, List.range'_succ]

theorem shell_names (s : Shell) : s.names = List.range (order s) := by
  simp only [Shell.names, disk_names, List.range_eq_range', order]
  change List.range' 0 4 ++ _ ++ _ ++ _ ++ _ = _
  have zeroJoin (m n : Nat) : List.range' 0 m ++ List.range' m n = List.range' 0 (m+n) := by
    simpa using rangeJoin 0 m n
  rw [zeroJoin, zeroJoin, zeroJoin, zeroJoin]

/-- The quota shell gives a model of the existing stacked-realization predicate
on the degree *list*, and not merely a tree or an abstract profile. -/
theorem shell_realization (s : Shell) :
    HasStackedRealization (s.names.map (incident s.edges)) := by
  classical
  obtain ⟨M, hist, verts, degree⟩ := shell_history s
  obtain ⟨B⟩ := SourceBridge.stacked_bridge hist
  let ds := s.names.map (incident s.edges)
  have length : ds.length = order s := by simp [ds, shell_names]
  let R : Layers.Model ds := {
    V := B.V
    map := B.map
    vertices := B.enum
    label := B.label
    inj := fun _ _ eq => B.inj eq
    hits := fun i => by rw [length, ← verts i]; exact B.hits i
    value := by
      intro v
      have bound := (verts _).1 ((B.hits _).2 ⟨v,rfl⟩)
      rw [B.degree_eq (SourceBridge.regular hist),degree]
      simp [ds, shell_names, List.getElem?_range bound] }
  exact ⟨R, B.origin⟩

/-- Every multiset accepted by the recurrence is realized by a labelled
stacked triangulation, read in its insertion order. -/
theorem accepted_has_stacked {d : Multiset Nat} (h : Accepts d) :
    ∃ ds : List Nat, (ds : Multiset Nat) = d ∧ HasStackedRealization ds := by
  obtain ⟨s, rfl⟩ := (acceptance_iff d).1 h
  exact ⟨_, rfl, shell_realization s⟩

/-- A chronological label can be arbitrary; subtree lists need not consist
of consecutive numbers. Their three children use the quota model's cyclic
order of sides, including the face opposite the second corner. -/
inductive NamedDisk where
  | leaf
  | fork (name : Nat) (ab bc ca : NamedDisk)

def NamedDisk.shape : NamedDisk → Disk
  | .leaf => .empty
  | .fork _ l m r => .split l.shape m.shape r.shape

def NamedDisk.names : NamedDisk → List Nat
  | .leaf => []
  | .fork x l m r => x :: (l.names ++ m.names ++ r.names)

private def child1 (f : Face) (x : Nat) : Face := ⟨f.a,f.b,x⟩
private def child2 (f : Face) (x : Nat) : Face := ⟨f.b,f.c,x⟩
private def child3 (f : Face) (x : Nat) : Face := ⟨f.c,f.a,x⟩

def NamedDisk.faces : NamedDisk → Face → List Face
  | .leaf, f => [f]
  | .fork x l m r, f =>
      l.faces (child1 f x) ++ m.faces (child2 f x) ++ r.faces (child3 f x)

def NamedDisk.edges : NamedDisk → Face → List (Nat × Nat)
  | .leaf, _ => []
  | .fork x l m r, f =>
      [(f.a,x),(f.b,x),(f.c,x)] ++ l.edges (child1 f x) ++
      m.edges (child2 f x) ++ r.edges (child3 f x)

private abbrev forestNames (ts : List (Face × NamedDisk)) :=
  ts.flatMap (fun p => p.2.names)

private abbrev forestFaces (ts : List (Face × NamedDisk)) :=
  ts.flatMap (fun p => p.2.faces p.1)

private abbrev forestEdges (ts : List (Face × NamedDisk)) :=
  ts.flatMap (fun p => p.2.edges p.1)

private def Replaced (before after : List Face) (g : Face) (x : Nat) :=
  (∀ f ∈ before, f ≠ g → f ∈ after) ∧
  ∀ f ∈ [child1 g x,child2 g x,child3 g x], f ∈ after

private theorem disk_insert (t : NamedDisk) (f g : Face) (x : Nat) (hit : g ∈ t.faces f) :
    ∃ n : NamedDisk, Replaced (t.faces f) (n.faces f) g x ∧
      n.names.Perm (x :: t.names) ∧
      ∀ v, incident (n.edges f) v =
        incident (t.edges f) v + incident [(g.a,x),(g.b,x),(g.c,x)] v := by
  induction t generalizing f with
  | leaf =>
    have eq : g=f := by simpa [NamedDisk.faces] using hit
    subst g
    refine ⟨.fork x .leaf .leaf .leaf, ?_, .rfl, ?_⟩
    · simp [Replaced, NamedDisk.faces]
    · simp [NamedDisk.edges,incident]
  | fork y l m r il im ir =>
    simp only [NamedDisk.faces,List.mem_append] at hit
    rcases hit with (hl|hm)|hr
    · obtain ⟨L,hl,nl,dl⟩ := il _ hl
      refine ⟨.fork y L m r, ?_, ?_, ?_⟩
      · obtain ⟨save, kid⟩ := hl
        constructor
        · intro z mem ne
          simp only [NamedDisk.faces,List.mem_append] at mem ⊢
          tauto
        · intro z mem
          simp only [NamedDisk.faces,List.mem_append]
          exact .inl (.inl (kid _ mem))
      · exact ((nl.append_right _).append_right _ |>.cons y).trans (.swap ..)
      · intro v
        simp only [NamedDisk.edges,inc_add,dl]
        omega
    · obtain ⟨N,hm,nm,dm⟩ := im _ hm
      refine ⟨.fork y l N r, ?_, ?_, ?_⟩
      · obtain ⟨save,kid⟩ := hm
        constructor
        · intro z mem ne
          simp only [NamedDisk.faces,List.mem_append] at mem ⊢
          tauto
        · intro z mem
          simp only [NamedDisk.faces,List.mem_append]
          exact .inl (.inr (kid _ mem))
      · have front := ((nm.append_left l.names).trans List.perm_middle).append_right r.names
        exact (front.cons y).trans (.swap ..)
      · intro v
        simp only [NamedDisk.edges,inc_add,dm]
        omega
    · obtain ⟨R,hr,nr,dr⟩ := ir _ hr
      refine ⟨.fork y l m R, ?_, ?_, ?_⟩
      · obtain ⟨save,kid⟩ := hr
        constructor
        · intro z mem ne
          simp only [NamedDisk.faces,List.mem_append] at mem ⊢
          tauto
        · intro z mem
          simp only [NamedDisk.faces,List.mem_append]
          exact .inr (kid _ mem)
      · have all := (nr.append_left (l.names ++ m.names)).trans List.perm_middle
        exact (all.cons y).trans (.swap ..)
      · intro v
        simp only [NamedDisk.edges,inc_add,dr]
        omega

private theorem forest_insert (ts : List (Face × NamedDisk)) (g : Face) (x : Nat)
    (mem : g ∈ forestFaces ts) :
    ∃ us : List (Face × NamedDisk), us.map Prod.fst = ts.map Prod.fst ∧
      Replaced (forestFaces ts) (forestFaces us) g x ∧
      (forestNames us).Perm (x :: forestNames ts) ∧
      ∀ v, incident (forestEdges us) v =
        incident (forestEdges ts) v + incident [(g.a,x),(g.b,x),(g.c,x)] v := by
  induction ts with
  | nil => simp [forestFaces] at mem
  | cons ft ts ih =>
    obtain ⟨f,t⟩ := ft
    change g ∈ t.faces f ++ forestFaces ts at mem
    rcases List.mem_append.1 mem with h|h
    · obtain ⟨n, ⟨save,kid⟩,names,degrees⟩ := disk_insert t f g x h
      refine ⟨(f,n)::ts, rfl, ?_, names.append_right _, ?_⟩
      · constructor
        · intro z hz ne
          change z ∈ t.faces f ++ forestFaces ts at hz
          change z ∈ n.faces f ++ forestFaces ts
          exact (List.mem_append.1 hz).elim (fun old => List.mem_append_left _ (save _ old ne))
            (List.mem_append_right _)
        · intro z hz
          exact List.mem_append_left _ (kid _ hz)
      · intro v
        change incident (n.edges f ++ forestEdges ts) v = incident (t.edges f ++ forestEdges ts) v + _
        rw [inc_add,inc_add,degrees]
        omega
    · obtain ⟨us,roots,⟨save,kid⟩,names,degrees⟩ := ih h
      refine ⟨(f,t)::us, congrArg (f :: ·) roots, ?_,
        (names.append_left t.names).trans List.perm_middle, ?_⟩
      · constructor
        · intro z hz ne
          change z ∈ t.faces f ++ forestFaces ts at hz
          change z ∈ t.faces f ++ forestFaces us
          exact (List.mem_append.1 hz).elim (List.mem_append_left _)
            (fun old => List.mem_append_right _ (save _ old ne))
        · intro z hz
          exact List.mem_append_right _ (kid _ hz)
      · intro v
        change incident (t.edges f ++ forestEdges us) v = incident (t.edges f ++ forestEdges ts) v + _
        rw [inc_add,inc_add,degrees]
        omega

def rootFaces : List Face := [⟨0,1,2⟩,⟨0,1,3⟩,⟨0,2,3⟩,⟨1,2,3⟩]

private def names (ts : List (Face × NamedDisk)) := [0,1,2,3] ++ forestNames ts

/-- An actual labelled mesh decomposed into four independently filled disks.
The graph and all available faces carry the source's original names. -/
structure Decomposes (M : Mesh) (ts : List (Face × NamedDisk)) : Prop where
  roots : ts.map Prod.fst = rootFaces
  distinctNames : (names ts).Nodup
  vertices : ∀ v, M.vertex v ↔ v ∈ names ts
  available : ∀ f, M.face f → ∃ g ∈ forestFaces ts, Fits f g.a g.b g.c
  degrees : ∀ v, (M.neighbors v).length = incident (baseEdges ++ forestEdges ts) v

private theorem unused {M} (h : Stacked M) {x} (fresh : ¬M.vertex x) :
    (M.neighbors x).length = 0 := by
  induction h with
  | tetra => simp [tetra, show ¬ x < 4 from fresh]
  | @insert prev f y old hf hy ih =>
    have nx : x≠y := fun eq => fresh (.inl eq)
    have absent : ¬ prev.vertex x := fun h => fresh (.inr h)
    have nothit : ¬ f.hit x := fun hit => absent ((SourceBridge.regular old).corner f hf x hit)
    simp [stack,nx,nothit,ih absent]

private theorem arbitrary_degrees {M} {f g : Face} {x : Nat} (h : Stacked M) (hf : M.face f)
    (fresh : ¬ M.vertex x) (fit : Fits f g.a g.b g.c) (v : Nat) :
    ((stack M f x).neighbors v).length = (M.neighbors v).length +
      incident [(g.a,x),(g.b,x),(g.c,x)] v := by
  have reg := SourceBridge.regular h
  have dis := reg.distinct f hf
  have diff : ¬ f.hit x := fun eq => fresh (reg.corner _ hf _ eq)
  rw [fit.hit] at diff
  have nd : g.a ≠ g.b ∧ g.a ≠ g.c ∧ g.b ≠ g.c := by
    rcases fit with e|e|e|e|e|e <;> subst f <;> simp at dis <;> grind
  let recCount := fun u => if v=u then 1 else 0
  have sum : incident [(g.a,x),(g.b,x),(g.c,x)] v =
      (recCount g.a+recCount x)+(recCount g.b+recCount x)+(recCount g.c+recCount x) := by
    change (_+_) + ((_+_) + ((_+_) + 0)) = _
    change (recCount g.a+recCount x)+((recCount g.b+recCount x)+((recCount g.c+recCount x)+0)) = _
    omega
  rw [sum]
  by_cases eq : v=x
  · subst v
    simp_all [recCount,stack,unused h fresh]
  by_cases e1 : v=g.a <;> by_cases e2 : v=g.b <;> by_cases e3 : v=g.c <;>
    simp_all [stack,fit.hit,recCount]

private theorem locate_child {f g : Face} (fit : Fits f g.a g.b g.c) (x : Nat) {k : Face}
    (hk : k=⟨f.a,f.b,x⟩ ∨ k=⟨f.a,f.c,x⟩ ∨ k=⟨f.b,f.c,x⟩) :
    ∃ n ∈ [child1 g x,child2 g x,child3 g x], Fits k n.a n.b n.c := by
  rcases fit with e|e|e|e|e|e <;> subst f <;> rcases hk with e|e|e <;> subst k
  · exact ⟨child1 g x, by simp, .inl rfl⟩
  · exact ⟨child3 g x, by simp, .inr (.inr (.inl rfl))⟩
  · exact ⟨child2 g x, by simp, .inl rfl⟩
  · exact ⟨child3 g x, by simp, .inr (.inr (.inl rfl))⟩
  · exact ⟨child1 g x, by simp, .inl rfl⟩
  · exact ⟨child2 g x, by simp, .inr (.inr (.inl rfl))⟩
  · exact ⟨child1 g x, by simp, .inr (.inr (.inl rfl))⟩
  · exact ⟨child2 g x, by simp, .inl rfl⟩
  · exact ⟨child3 g x, by simp, .inr (.inr (.inl rfl))⟩
  · exact ⟨child2 g x, by simp, .inl rfl⟩
  · exact ⟨child1 g x, by simp, .inr (.inr (.inl rfl))⟩
  · exact ⟨child3 g x, by simp, .inl rfl⟩
  · exact ⟨child3 g x, by simp, .inl rfl⟩
  · exact ⟨child2 g x, by simp, .inr (.inr (.inl rfl))⟩
  · exact ⟨child1 g x, by simp, .inl rfl⟩
  · exact ⟨child2 g x, by simp, .inr (.inr (.inl rfl))⟩
  · exact ⟨child3 g x, by simp, .inl rfl⟩
  · exact ⟨child1 g x, by simp, .inr (.inr (.inl rfl))⟩

private theorem represents_tetra : Decomposes tetra (rootFaces.map (·, NamedDisk.leaf)) := by
  refine ⟨rfl, by decide, ?_, ?_, ?_⟩
  · intro v
    change v < 4 ↔ v ∈ [0,1,2,3]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro f hf
    obtain ⟨a,b,c⟩ := f
    change a < b ∧ b < c ∧ c < 4 at hf
    have options : (a=0 ∧ b=1 ∧ c=2) ∨ (a=0 ∧ b=1 ∧ c=3) ∨
        (a=0 ∧ b=2 ∧ c=3) ∨ (a=1 ∧ b=2 ∧ c=3) := by omega
    refine ⟨⟨a,b,c⟩, ?_, .inl rfl⟩
    rcases options with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩ <;> decide
  · intro v
    exact baseDegree v

/-- Extract four labelled trees from *any* sequential source history. Each
extension splits the leaf for that exact source face; insertions in the four
disks can interleave and the fresh source names need not be consecutive. -/
theorem history_decomposes {M : Mesh} (h : Stacked M) :
    ∃ ts : List (Face × NamedDisk), Decomposes M ts := by
  induction h with
  | tetra => exact ⟨_,represents_tetra⟩
  | @insert M f x prior hf fresh ih =>
    obtain ⟨ts,T⟩ := ih
    obtain ⟨g,hg,fit⟩ := T.available f hf
    obtain ⟨us,root,⟨save,kid⟩,newNames,dg⟩ := forest_insert ts g x hg
    have namePerm : (names us).Perm (x :: names ts) :=
      (newNames.append_left _).trans List.perm_middle
    have nodup : (x :: names ts).Nodup :=
      List.nodup_cons.2 ⟨fun mem => fresh ((T.vertices _).2 mem), T.distinctNames⟩
    refine ⟨us, root.trans T.roots, namePerm.nodup_iff.2 nodup, ?_, ?_, ?_⟩
    · intro v
      change v=x ∨ M.vertex v ↔ _
      rw [T.vertices, namePerm.mem_iff, List.mem_cons]
    · intro k hk
      rcases hk with ⟨old,ne⟩|kids
      · obtain ⟨z,hz,orient⟩ := T.available k old
        have away : z ≠ g := by
          intro eq
          subst z
          apply ne
          exact (SourceBridge.regular prior).unique k f old hf fun i =>
            (orient.hit i).trans (fit.hit i).symm
        exact ⟨z,save _ hz away,orient⟩
      · obtain ⟨n,hn,hnk⟩ := locate_child fit x kids
        exact ⟨n,kid _ hn,hnk⟩
    · intro v
      rw [arbitrary_degrees prior hf fresh fit,T.degrees,inc_add,inc_add,dg]
      omega

private theorem diskLength (t : Disk) (u : Nat) : (t.names u).length = t.size := by
  simp [disk_names]

private theorem nameLength (t : NamedDisk) : t.names.length = t.shape.size := by
  induction t with
  | leaf => rfl
  | fork x l m r L M R => simp [NamedDisk.names,NamedDisk.shape,Disk.size,L,M,R]; omega

private theorem edges_renamed (t : NamedDisk) (a b c u : Nat) (σ : Nat → Nat)
    (eq : (t.shape.names u).map σ = t.names) :
    (t.shape.edges a b c u).map (Prod.map σ σ) = t.edges ⟨σ a,σ b,σ c⟩ := by
  induction t generalizing a b c u with
  | leaf => rfl
  | fork x l m r L M R =>
    simp only [NamedDisk.shape,Disk.names,List.map_cons,List.map_append,NamedDisk.names,
      List.cons.injEq] at eq
    obtain ⟨center,rest⟩ := eq
    obtain ⟨lm,rr⟩ := List.append_inj rest (by simp [diskLength,nameLength])
    obtain ⟨ll,mm⟩ := List.append_inj lm (by simp [diskLength,nameLength])
    simp only [NamedDisk.shape,Disk.edges,List.map_append,NamedDisk.edges,child1,child2,child3]
    rw [L _ _ _ _ ll,M _ _ _ _ mm,R _ _ _ _ rr]
    simp [center]

private def roots (a b c d : NamedDisk) : List (Face × NamedDisk) :=
  [(⟨0,1,2⟩,a),(⟨0,1,3⟩,b),(⟨0,2,3⟩,c),(⟨1,2,3⟩,d)]

private theorem four_trees (ts : List (Face × NamedDisk)) (eq : ts.map Prod.fst = rootFaces) :
    ∃ a b c d, ts = roots a b c d := by
  match ts with
  | [(f,a),(g,b),(h,c),(i,d)] =>
    have e : f=⟨0,1,2⟩ ∧ g=⟨0,1,3⟩ ∧ h=⟨0,2,3⟩ ∧ i=⟨1,2,3⟩ := by
      simpa [rootFaces] using eq
    rcases e with ⟨rfl,rfl,rfl,rfl⟩
    exact ⟨_,_,_,_,rfl⟩
  | [] | [_] | [_,_] | [_,_,_] | _::_::_::_::_::_ => simp [rootFaces] at eq

private def shapeShell (a b c d : NamedDisk) : Shell := ⟨a.shape,b.shape,c.shape,d.shape⟩

private theorem all_edges_renamed (a b c d : NamedDisk) (σ : Nat → Nat)
    (eq : ((shapeShell a b c d).names.map σ) = names (roots a b c d)) :
    (shapeShell a b c d).edges.map (Prod.map σ σ) = baseEdges ++ forestEdges (roots a b c d) := by
  let u := 4+a.shape.size
  let w := u+b.shape.size
  let y := w+c.shape.size
  change (([0,1,2,3] ++ a.shape.names 4 ++ b.shape.names u ++ c.shape.names w ++
    d.shape.names y).map σ) = _ at eq
  simp only [List.map_append] at eq
  change _ = [0,1,2,3] ++ (a.names ++ (b.names ++ (c.names ++ (d.names ++ [])))) at eq
  simp only [List.append_nil] at eq
  rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc] at eq
  obtain ⟨abc,dd⟩ := List.append_inj eq (by simp [diskLength,nameLength])
  obtain ⟨ab,cc⟩ := List.append_inj abc (by simp [diskLength,nameLength])
  obtain ⟨base,bb⟩ := List.append_inj ab (by simp [diskLength,nameLength])
  obtain ⟨frame,aa⟩ := List.append_inj base (by simp)
  have z : σ 0=0 ∧ σ 1=1 ∧ σ 2=2 ∧ σ 3=3 := by simpa using frame
  change (baseEdges ++ a.shape.edges 0 1 2 4 ++ b.shape.edges 0 1 3 u ++
    c.shape.edges 0 2 3 w ++ d.shape.edges 1 2 3 y).map _ = _
  simp only [List.map_append]
  rw [edges_renamed a 0 1 2 4 σ aa, edges_renamed b 0 1 3 u σ bb,
    edges_renamed c 0 2 3 w σ cc, edges_renamed d 1 2 3 y σ dd]
  simp [baseEdges,roots,forestEdges,z.1,z.2.1,z.2.2.1,z.2.2.2,List.append_assoc]

private theorem diskBounds (t : Disk) (a b c u : Nat) (av : a<u) (bv : b<u) (cv : c<u)
    (e : Nat × Nat) (mem : e ∈ t.edges a b c u) : e.1 < u+t.size ∧ e.2 < u+t.size := by
  induction t generalizing a b c u with
  | empty => simp [Disk.edges] at mem
  | split l m r L M R =>
    simp only [Disk.edges,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at mem
    simp only [Disk.size]
    rcases mem with (((h|h|h)|h)|h)|h
    · subst e; simp; omega
    · subst e; simp; omega
    · subst e; simp; omega
    · obtain ⟨_,_⟩ := L a b u (u+1) (by omega) (by omega) (by omega) h
      omega
    · obtain ⟨_,_⟩ := M b c u (u+1+l.size) (by omega) (by omega) (by omega) h
      omega
    · obtain ⟨_,_⟩ := R c a u (u+1+l.size+m.size) (by omega) (by omega) (by omega) h
      omega

private theorem shellBounds (s : Shell) (e) (mem : e ∈ s.edges) :
    e.1 < order s ∧ e.2 < order s := by
  simp only [Shell.edges,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at mem
  unfold order
  rcases mem with ((((h|h|h|h|h|h)|h)|h)|h)|h
  · subst e
    change 0 < 4+s.abc.size+s.abd.size+s.acd.size+s.bcd.size ∧ 1 < 4+s.abc.size+s.abd.size+s.acd.size+s.bcd.size
    omega
  · subst e
    change 0 < 4+s.abc.size+s.abd.size+s.acd.size+s.bcd.size ∧ 2 < 4+s.abc.size+s.abd.size+s.acd.size+s.bcd.size
    omega
  · subst e
    change 0 < 4+s.abc.size+s.abd.size+s.acd.size+s.bcd.size ∧ 3 < 4+s.abc.size+s.abd.size+s.acd.size+s.bcd.size
    omega
  · subst e
    change 1 < 4+s.abc.size+s.abd.size+s.acd.size+s.bcd.size ∧ 2 < 4+s.abc.size+s.abd.size+s.acd.size+s.bcd.size
    omega
  · subst e
    change 1 < 4+s.abc.size+s.abd.size+s.acd.size+s.bcd.size ∧ 3 < 4+s.abc.size+s.abd.size+s.acd.size+s.bcd.size
    omega
  · subst e
    change 2 < 4+s.abc.size+s.abd.size+s.acd.size+s.bcd.size ∧ 3 < 4+s.abc.size+s.abd.size+s.acd.size+s.bcd.size
    omega
  · obtain ⟨_,_⟩ := diskBounds s.abc 0 1 2 4 (by omega) (by omega) (by omega) _ h
    omega
  · obtain ⟨_,_⟩ := diskBounds s.abd 0 1 3 (4+s.abc.size) (by omega) (by omega) (by omega) _ h
    omega
  · obtain ⟨_,_⟩ := diskBounds s.acd 0 2 3 (4+s.abc.size+s.abd.size) (by omega) (by omega) (by omega) _ h
    omega
  · exact diskBounds s.bcd 1 2 3 _ (by omega) (by omega) (by omega) _ h

private theorem mapped_degree (es : List (Nat × Nat)) (N : Nat) (σ : Nat → Nat)
    (inj : ∀ i<N, ∀ j<N, σ i=σ j → i=j)
    (ends : ∀ e∈es, e.1<N ∧ e.2<N) (v : Nat) (hv : v<N) :
    incident (es.map (Prod.map σ σ)) (σ v) = incident es v := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have b := ends e (by simp)
    have l : σ v = σ e.1 ↔ v=e.1 := ⟨inj _ hv _ b.1, congrArg σ⟩
    have r : σ v = σ e.2 ↔ v=e.2 := ⟨inj _ hv _ b.2, congrArg σ⟩
    have tail := ih (fun z mem => ends z (List.mem_cons_of_mem _ mem))
    change ((if σ v=σ e.1 then 1 else 0)+(if σ v=σ e.2 then 1 else 0)) +
      incident (es.map _) (σ v) = ((if v=e.1 then 1 else 0)+(if v=e.2 then 1 else 0)) +
        incident es v
    simp only [l,r,tail]

/-- Reading the four trees in preorder changes only the vertex labels.
Their quota acceptance is exactly the degree multiset of the original mesh
on the full list of its distinct vertex names. -/
theorem decomposition_accepts {M : Mesh} {ts} (h : Decomposes M ts) :
    Accepts ((names ts).map (fun v => (M.neighbors v).length) : Multiset Nat) := by
  obtain ⟨a,b,c,d,rfl⟩ := four_trees ts h.roots
  let ts := roots a b c d
  let s := shapeShell a b c d
  let ns := names ts
  have size : ns.length = order s := by
    simp [ns, names,ts,roots,s,shapeShell,order,forestNames,nameLength]
    omega
  let σ := fun i : Nat => ns[i]?.getD 0
  have exactName {i : Nat} (hi : i < order s) : σ i = ns[i]'(size ▸ hi) := by
    simp [σ, List.getElem?_eq_getElem (size ▸ hi)]
  have inject : ∀ i<order s, ∀ j<order s, σ i=σ j → i=j := by
    intro i hi j hj eq
    exact h.distinctNames.getElem_inj_iff.1 ((exactName hi).symm.trans (eq.trans (exactName hj)))
  have allNames : s.names.map σ = ns := by
    rw [shell_names]
    apply List.ext_getElem
    · simp [size]
    · intro i il ir
      have hi : i < order s := size ▸ ir
      simpa using exactName hi
  have edges := all_edges_renamed a b c d σ allNames
  apply (acceptance_iff _).2
  refine ⟨s, ?_⟩
  change ((ns.map (fun v => (M.neighbors v).length)) : Multiset Nat) = _
  rw [← allNames,List.map_map]
  apply congrArg (fun l : List Nat => (l : Multiset Nat))
  apply List.map_congr_left
  intro v hv
  rw [Function.comp_apply,h.degrees,← edges]
  exact mapped_degree s.edges (order s) σ inject (shellBounds s) v
    (by simpa [shell_names] using hv)

/-- Every sequential stacking history, with arbitrary fresh labels, gives
a quota certificate for exactly its multiset of actual vertex degrees. -/
theorem history_accepts {M : Mesh} (h : Stacked M) :
    ∃ ns : List Nat, ns.Nodup ∧ (∀ v, M.vertex v ↔ v ∈ ns) ∧
      Accepts (ns.map (fun v => (M.neighbors v).length) : Multiset Nat) := by
  obtain ⟨ts, rep⟩ := history_decomposes h
  exact ⟨_,rep.distinctNames,rep.vertices,decomposition_accepts rep⟩

/-- A sequential tetrahedral stacking with the specified unordered degrees.
Vertex names are arbitrary natural numbers and may appear in any order. -/
def SequentialRealization (d : Multiset Nat) : Prop :=
  ∃ M : Mesh, Stacked M ∧ ∃ ns : List Nat, ns.Nodup ∧
    (∀ v, M.vertex v ↔ v ∈ ns) ∧
    (ns.map (fun v => (M.neighbors v).length) : Multiset Nat) = d

/-- The three-quota recurrence is necessary and sufficient for genuine
single-face insertions in a tetrahedral triangulation, on any finite
degree multiset. Both directions use the same graph degree notion. -/
theorem accepts_iff_sequential (d : Multiset Nat) :
    Accepts d ↔ SequentialRealization d := by
  constructor
  · intro yes
    obtain ⟨s,rfl⟩ := (acceptance_iff _).1 yes
    obtain ⟨M,hist,verts,degree⟩ := shell_history s
    refine ⟨M,hist,s.names,?_,?_,?_⟩
    · rw [shell_names]
      exact List.nodup_range
    · intro v
      simp [verts,shell_names]
    · exact congrArg (fun xs : List Nat => (xs : Multiset Nat))
        (List.map_congr_left (fun v _ => degree v))
  · rintro ⟨M,hist,ns,good,verts,rfl⟩
    obtain ⟨qs,distinct,vertices,accepted⟩ := history_accepts hist
    have perm : qs.Perm ns := (List.perm_ext_iff_of_nodup distinct good).2
      (fun v => (vertices v).symm.trans (verts v))
    exact (Multiset.coe_eq_coe.2 (perm.map (fun v => (M.neighbors v).length))) ▸ accepted

end Recognition.StackedHistory
