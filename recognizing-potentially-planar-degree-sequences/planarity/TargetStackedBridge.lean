import StackedHistory
import Mathlib.Data.List.Perm.Basic
import Triangulation.SourceBridge

/-! A simultaneous subdivision of distinct old faces is a sequence of legal
single-face insertions. The old faces may share edges or corners. -/
namespace Recognition.TargetStackedBridge
open SourceMap Rigidity SourceBridge

def child (f : Face) (x : Nat) (g : Face) : Prop :=
  g=⟨f.a,f.b,x⟩ ∨ g=⟨f.a,f.c,x⟩ ∨ g=⟨f.b,f.c,x⟩

private theorem child_hit {f g : Face} {x} (h : child f x g) :
    g.hit x ∧ ∀ i, g.hit i → i=x ∨ f.hit i := by
  rcases h with rfl|rfl|rfl <;> simp [Face.hit]

private theorem child_two {f g : Face} {x} (h : child f x g)
    {a b c : Nat} (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (ax : a≠x) (bx : b≠x) (cx : c≠x) : ¬(g.hit a ∧ g.hit b ∧ g.hit c) := by
  rcases h with rfl|rfl|rfl <;> simp [Face.hit] <;> grind

def batch (M : Mesh) (face : S → Face) (name : S → Nat) : List S → Mesh
  | [] => M
  | a::xs => stack (batch M face name xs) (face a) (name a)

theorem batch_spec {M : Mesh} (built : Stacked M) (face : S → Face) (name : S → Nat)
    (existsFace : ∀ s,M.face (face s)) (fresh : ∀ s,¬M.vertex (name s))
    (distinct : Function.Injective face) (unique : Function.Injective name)
    (xs : List S) (nd : xs.Nodup) :
    let N := batch M face name xs
    Stacked N ∧ (∀ v,N.vertex v ↔ M.vertex v ∨ ∃ s∈xs,name s=v) ∧
    ∀ g,N.face g ↔ (M.face g ∧ ∀ s∈xs,g≠face s) ∨ ∃ s∈xs,child (face s) (name s) g := by
  induction xs with
  | nil => simpa [batch] using built
  | cons a xs ih =>
    obtain ⟨st,ve,fa⟩ := ih (List.nodup_cons.mp nd).2
    have absent := (List.nodup_cons.mp nd).1
    have held : (batch M face name xs).face (face a) :=
      (fa _).mpr (.inl ⟨existsFace a,fun s hs he => absent (distinct he ▸ hs)⟩)
    have newName : ¬(batch M face name xs).vertex (name a) := by
      rw [ve]; rintro (bad|⟨s,hs,eq⟩)
      · exact fresh a bad
      · exact absent (unique eq ▸ hs)
    refine ⟨Stacked.insert st held newName,?_,?_⟩
    · intro v
      change v=name a ∨ (batch M face name xs).vertex v ↔ _
      rw [ve]; simp only [List.mem_cons]; grind
    · intro g
      change ((batch M face name xs).face g ∧ g≠face a) ∨ child (face a) (name a) g ↔ _
      rw [fa]; simp only [List.mem_cons]
      have dis (s : S) (c : child (face s) (name s) g) : g≠face a := by
        intro eq; subst g
        exact fresh s ((regular built).corner _ (existsFace a) _ (child_hit c).1)
      constructor
      · rintro (⟨⟨old,h⟩|⟨s,m,c⟩,other⟩|c)
        · exact Or.inl ⟨old,fun s mem => mem.elim (fun e => e ▸ other) (h s)⟩
        · exact Or.inr ⟨s,Or.inr m,c⟩
        · exact Or.inr ⟨a,Or.inl rfl,c⟩
      · rintro (⟨old,h⟩|⟨s,rfl|mem,c⟩)
        · exact Or.inl ⟨Or.inl ⟨old,fun s m => h s (Or.inr m)⟩,h a (Or.inl rfl)⟩
        · exact Or.inr c
        · exact Or.inl ⟨Or.inr ⟨s,mem,c⟩,dis s c⟩

structure Display {V : Type} (G : Map V) where
  mesh : Mesh
  built : Stacked mesh
  enum : Enumeration V
  label : V → Nat
  inj : Function.Injective label
  hits : ∀ x, mesh.vertex x ↔ ∃ v,label v=x
  faces : ∀ a b c,G.face a b c ↔ triple mesh (label a) (label b) (label c)

private def tetraDisplay : Display Tetrahedron.map where
  mesh := tetra
  built := .tetra
  enum := tetraBridge.enum
  label := tetraBridge.label
  inj := tetraBridge.inj
  hits := tetraBridge.hits
  faces := tetraBridge.face

variable {V : Type} {G : Map V} (D : Display G) (fill : Stacking.Choice V)
local notation "Star" => Stacking.Star G fill

private theorem face_rep (s : Star) :
    ∃ f,D.mesh.face f ∧ ∀ v,f.hit (D.label v) ↔ s.val v := by
  obtain ⟨a,b,c,face,eq⟩ := s.property.1
  obtain ⟨ab,bc,ac,f,hf,ha,hb,hc⟩ := (D.faces ..).mp face
  refine ⟨f,hf,fun v => ?_⟩
  rw [three_cover f ab bc ac ha hb hc,eq]
  simp [Stacking.corners,D.inj.eq_iff]

noncomputable def rep (s : Star) : Face := Classical.choose (face_rep D fill s)

theorem rep_spec (s : Star) : D.mesh.face (rep D fill s) ∧
    ∀ v,(rep D fill s).hit (D.label v) ↔ s.val v := Classical.choose_spec (face_rep D fill s)

private theorem rep_inj : Function.Injective (rep D fill) := by
  intro a b eq
  apply Subtype.ext; funext x; apply propext
  rw [←(rep_spec D fill a).2,←(rep_spec D fill b).2,eq]

noncomputable def freshName (s : Star) : Nat := by
  classical
  exact (D.enum.vertices.map D.label).sum+1+(Stacking.starEnumeration G fill D.enum).vertices.idxOf s

private theorem freshName_gt (s : Star) (a : V) : D.label a < freshName D fill s := by
  classical
  have le (v : Nat) (ns : List Nat) (mem : v∈ns) : v ≤ ns.sum := by
    induction ns with
    | nil => simp at mem
    | cons w ws ih => simp at mem ⊢; rcases mem with rfl|h <;> first | omega | exact (ih h).trans (by omega)
  have m := le _ _ (List.mem_map.mpr ⟨a,D.enum.complete a,rfl⟩ :
      D.label a ∈ D.enum.vertices.map D.label)
  unfold freshName; omega

private theorem freshName_inj : Function.Injective (freshName D fill) := by
  classical
  intro s t eq
  have : (Stacking.starEnumeration G fill D.enum).vertices.idxOf s =
      (Stacking.starEnumeration G fill D.enum).vertices.idxOf t := by unfold freshName at eq;omega
  exact (List.idxOf_inj (Stacking.starEnumeration G fill D.enum |>.complete s)).mp this


private theorem fresh (s : Star) : ¬D.mesh.vertex (freshName D fill s) := by
  intro hv
  obtain ⟨a,e⟩ := (D.hits _).mp hv
  exact (freshName_gt D fill s a).ne e

private theorem rep_eq {a b c : V} {g : Face} (hg : D.mesh.face g)
    (ab : D.label a≠D.label b) (bc : D.label b≠D.label c) (ac : D.label a≠D.label c)
    (ha : g.hit (D.label a)) (hb : g.hit (D.label b)) (hc : g.hit (D.label c)) (s : Star) :
    g=rep D fill s ↔ s.val=Stacking.corners a b c := by
  have cover (v : V) : g.hit (D.label v) ↔ Stacking.corners a b c v := by
    simp [three_cover g ab bc ac ha hb hc,Stacking.corners,D.inj.eq_iff]
  constructor
  · intro eq; subst g; funext v; apply propext
    exact ((rep_spec D fill s).2 v).symm.trans (cover v)
  · intro eq
    apply (regular D.built).unique _ _ hg (rep_spec D fill s).1
    intro i
    by_cases h : D.mesh.vertex i
    · obtain ⟨v,rfl⟩ := (D.hits _).mp h
      rw [(rep_spec D fill s).2,eq]; exact cover v
    · exact iff_of_false (fun a => h ((regular D.built).corner _ hg _ a))
        (fun a => h ((regular D.built).corner _ (rep_spec D fill s).1 _ a))

noncomputable def nextDisplay : Display (Stacking.stack G fill) := by
  classical
  let F := rep D fill
  let X := freshName D fill
  let chosen := Stacking.starEnumeration G fill D.enum
  let N := batch D.mesh F X chosen.vertices
  obtain ⟨built,vertices,faces⟩ := batch_spec D.built F X (fun s => (rep_spec D fill s).1)
    (fresh D fill) (rep_inj D fill) (freshName_inj D fill) chosen.vertices chosen.unique
  have vf (v) : N.vertex v ↔ D.mesh.vertex v ∨ ∃ s,X s=v := by
    simpa [N,chosen.complete] using vertices v
  have ff (g) : N.face g ↔ (D.mesh.face g ∧ ∀ s,g≠F s) ∨ ∃ s,child (F s) (X s) g := by
    simpa [N,chosen.complete] using faces g
  have cx (s : Star) (g : Face) (hg : N.face g) (hx : g.hit (X s)) :
      child (F s) (X s) g := by
    rcases (ff g).mp hg with ⟨old,_⟩|⟨t,h⟩
    · exact False.elim (fresh D fill s ((regular D.built).corner _ old _ hx))
    · rcases (child_hit h).2 _ hx with eq|old
      · exact (freshName_inj D fill eq).symm ▸ h
      · exact False.elim (fresh D fill s ((regular D.built).corner _ (rep_spec D fill t).1 _ old))
  have old3 (a b c : V) : G.face a b c ∧ ¬fill (Stacking.corners a b c) ↔
      triple N (D.label a) (D.label b) (D.label c) := by
    constructor
    · intro ⟨face,no⟩
      obtain ⟨ab,bc,ac,g,hg,ha,hb,hc⟩ := (D.faces ..).mp face
      refine ⟨ab,bc,ac,g,(ff g).mpr (.inl ⟨hg,?_⟩),ha,hb,hc⟩
      intro s eq
      exact no (((rep_eq D fill hg ab bc ac ha hb hc s).mp eq) ▸ s.property.2)
    · rintro ⟨ab,bc,ac,g,hg,ha,hb,hc⟩
      rcases (ff g).mp hg with ⟨old,n⟩|⟨s,sub⟩
      · have face := (D.faces ..).mpr ⟨ab,bc,ac,g,old,ha,hb,hc⟩
        refine ⟨face,fun h => ?_⟩
        let s : Star := ⟨_,⟨a,b,c,face,rfl⟩,h⟩
        exact n s ((rep_eq D fill old ab bc ac ha hb hc s).mpr rfl)
      · exact False.elim (child_two sub ab ac bc (freshName_gt D fill s a).ne
          (freshName_gt D fill s b).ne (freshName_gt D fill s c).ne ⟨ha,hb,hc⟩)
  have one3 (a b : V) (s : Star) : a≠b ∧ s.val a ∧ s.val b ↔
      triple N (D.label a) (D.label b) (X s) := by
    constructor
    · rintro ⟨ab,sa,sb⟩
      have tr := (new_triple (f:=F s) (regular D.built) (fresh D fill s)
        (freshName_gt D fill s a).ne (freshName_gt D fill s b).ne).mpr
          ⟨D.inj.ne ab,(rep_spec D fill s).2 a |>.mpr sa,(rep_spec D fill s).2 b |>.mpr sb⟩
      obtain ⟨ab,bx,ax,g,hg,ha,hb,hx⟩ := tr
      rcases hg with ⟨old,_⟩|sub
      · exact False.elim (fresh D fill s ((regular D.built).corner _ old _ hx))
      · exact ⟨ab,bx,ax,g,(ff g).mpr (.inr ⟨s,sub⟩),ha,hb,hx⟩
    · rintro ⟨ab,bx,ax,g,hg,ha,hb,hx⟩
      have hit := (child_hit (cx s g hg hx)).2
      exact ⟨fun eq => ab (congrArg D.label eq),(rep_spec D fill s).2 a |>.mp
        ((hit _ ha).resolve_left ax),(rep_spec D fill s).2 b |>.mp ((hit _ hb).resolve_left bx)⟩
  have two3 (v : Nat) (s t : Star) : ¬triple N v (X s) (X t) := by
    rintro ⟨_,st,_,g,hg,_,hs,ht⟩
    rcases (child_hit (cx t g hg ht)).2 _ hs with eq|old
    · exact st eq
    · exact fresh D fill s ((regular D.built).corner _ (rep_spec D fill t).1 _ old)
  refine ⟨N,built,Stacking.enumeration G fill D.enum,Sum.elim D.label X,?_,?_,?_⟩
  · intro a b e; cases a with
    | inl a => cases b with
               | inl b => exact congrArg Sum.inl (D.inj e)
               | inr s => exact False.elim ((freshName_gt D fill s a).ne e)
    | inr s => cases b with
               | inl b => exact False.elim ((freshName_gt D fill s b).ne e.symm)
               | inr t => exact congrArg Sum.inr (freshName_inj D fill e)
  · intro v; rw [vf,D.hits]; constructor
    · rintro (⟨a,e⟩|⟨s,e⟩)
      · exact ⟨.inl a,e⟩
      · exact ⟨.inr s,e⟩
    · rintro ⟨a|s,e⟩
      · exact .inl ⟨a,e⟩
      · exact .inr ⟨s,e⟩
  · rintro (a|s) (b|t) (c|u)
    · exact old3 a b c
    · exact one3 a b u
    · exact (one3 c a t).trans triple_rot
    · exact iff_of_false id (two3 _ t u)
    · exact (one3 b c s).trans triple_rot.symm
    · exact iff_of_false id (fun h => two3 _ u s (triple_rot.mp h))
    · exact iff_of_false id (fun h => two3 _ s t (triple_rot.mpr h))
    · exact iff_of_false id (two3 _ t u)

theorem display {V : Type} {G : Map V} (h : StackedMap G) : Nonempty (Display G) := by
  induction h with
  | tetra => exact ⟨tetraDisplay⟩
  | subdivide _ fill ih => obtain ⟨D⟩ := ih; exact ⟨nextDisplay D fill⟩


private theorem display_edge (a b : V) : G.adj a b ↔ D.label b∈D.mesh.neighbors (D.label a) := by
  obtain ⟨B⟩ := stacked_bridge D.built
  have old (v : V) := (D.hits _).mpr ⟨v,rfl⟩
  obtain ⟨x,hx⟩ := (B.hits _).mp (old a)
  obtain ⟨y,hy⟩ := (B.hits _).mp (old b)
  rw [←hx,←hy,←B.edge x y]
  constructor
  · rintro ⟨v,h⟩
    obtain ⟨z,hz⟩ := (B.hits _).mp (old v)
    exact ⟨z,(B.face ..).mpr (by rw [hx,hy,hz]; exact (D.faces ..).mp h)⟩
  · rintro ⟨z,h⟩
    obtain ⟨v,hv⟩ := (D.hits _).mp ((B.hits _).mpr ⟨z,rfl⟩)
    exact ⟨v,(D.faces ..).mpr (by rw [←hx,←hy,hv]; exact (B.face ..).mp h)⟩

/-- Simultaneous layers can always be unpacked into legal individual face
insertions, with the prescribed degrees retained at every original label. -/
theorem sequential {ds : List Nat} : HasStackedRealization ds →
    StackedHistory.SequentialRealization (ds : Multiset Nat) := by
  rintro ⟨R,stacked⟩
  obtain ⟨D⟩ := display stacked
  let B : Bridge D.mesh := {
    V := R.V, map := R.map, origin := stacked, enum := R.vertices, label := D.label
    inj := D.inj, hits := D.hits, edge := display_edge D, face := D.faces }
  let ns := R.vertices.vertices.map D.label
  have hp := (Layers.label_perm R).map (fun i => ds[i]?.getD 0)
  have eq : (List.range ds.length).map (fun i => ds[i]?.getD 0) = ds := by
    apply List.ext_getElem <;> simp +contextual
  rw [eq] at hp
  refine ⟨D.mesh,D.built,ns,List.pairwise_map.mpr (R.vertices.unique.imp fun ne e => ne (D.inj e)),?_,?_⟩
  · intro v
    simp [ns,D.hits,R.vertices.complete]
  · apply Multiset.coe_eq_coe.mpr
    apply List.Perm.trans _ hp
    apply List.Perm.of_eq
    simp only [ns,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro v _
    exact (B.degree_eq (regular D.built) v).symm.trans (R.value v)

/-- Read a sequential realization in the precise order of the input list,
including repeated values. -/
theorem of_sequential {ds : List Nat} : StackedHistory.SequentialRealization (ds : Multiset Nat) →
    HasStackedRealization ds := by
  classical
  rintro ⟨M,st,ns,nd,vertices,deg⟩
  obtain ⟨B⟩ := stacked_bridge st
  let f := fun a : B.V => (M.neighbors (B.label a)).length
  have nd' : (B.enum.vertices.map B.label).Nodup :=
    List.pairwise_map.mpr (B.enum.unique.imp fun ne e => ne (B.inj e))
  have perm : (B.enum.vertices.map B.label).Perm ns := by
    apply (List.perm_ext_iff_of_nodup nd' nd).2
    intro v; rw [←vertices, B.hits]; simp [B.enum.complete]
  have p : ds.Perm (B.enum.vertices.map f) := by
    have := (perm.map (fun i => (M.neighbors i).length)).trans (Multiset.coe_eq_coe.mp deg)
    simpa [f,List.map_map,Function.comp_def] using this.symm
  have reorder : ∃ vs : List B.V, ds=vs.map f ∧ vs.Perm B.enum.vertices := by
    change (Relation.Comp (fun l vs => l=List.map f vs) List.Perm) ds B.enum.vertices
    rw [List.eq_map_comp_perm]; exact p
  obtain ⟨vs,rfl,pv⟩ := reorder
  have allv (v : B.V) := pv.mem_iff.mpr (B.enum.complete v)
  let R : Layers.Model (vs.map f) := {
    V := B.V, map := B.map, vertices := B.enum, label := fun a => vs.idxOf a
    inj := fun a _ h => (List.idxOf_inj (allv a)).mp h
    hits := fun i => by
      simp only [List.length_map]
      constructor
      · intro hi
        exact ⟨vs[i],(pv.nodup_iff.mpr B.enum.unique).idxOf_getElem i hi⟩
      · rintro ⟨v,rfl⟩; exact List.idxOf_lt_length_of_mem (allv v)
    value := fun a => by
      have ia := List.idxOf_lt_length_of_mem (allv a)
      rw [B.degree_eq (regular st),List.getElem?_eq_getElem (by simpa using ia)]
      simp [List.getElem_idxOf ia,f] }
  exact ⟨R,B.origin⟩

theorem sequential_iff (ds : List Nat) : HasStackedRealization ds ↔
    StackedHistory.SequentialRealization (ds : Multiset Nat) := ⟨sequential,of_sequential⟩

end Recognition.TargetStackedBridge
