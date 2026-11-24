import SourceMap
import Triangulation.Tetrahedron
import Triangulation.Provenance
import Triangulation.Stacking
import Triangulation.Layers

namespace Recognition.SourceBridge
open SourceMap Rigidity Reduction

/-- A triangle in the ordered mesh, read in any order. -/
def triple (M : Mesh) (i j k : Nat) : Prop :=
  i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ ∃ f, M.face f ∧ f.hit i ∧ f.hit j ∧ f.hit k

theorem three_cover (f : Face) {i j k} (ij : i ≠ j) (jk : j ≠ k) (ik : i ≠ k)
    (hi : f.hit i) (hj : f.hit j) (hk : f.hit k) (z : Nat) :
    f.hit z ↔ z=i ∨ z=j ∨ z=k := by
  simp only [Face.hit] at *; grind

theorem triple_rot {M : Mesh} {i j k} : triple M i j k ↔ triple M j k i := by
  unfold triple; grind

/-- The mesh retains one representative for each unordered face. -/
structure Regular (M : Mesh) : Prop where
  corner : ∀ f, M.face f → ∀ i, f.hit i → M.vertex i
  distinct : ∀ f, M.face f → f.a ≠ f.b ∧ f.b ≠ f.c ∧ f.a ≠ f.c
  unique : ∀ f g, M.face f → M.face g → (∀ i, f.hit i ↔ g.hit i) → f=g
  nodup : ∀ v, M.vertex v → (M.neighbors v).Nodup
  neighbor : ∀ v i, M.vertex v → i ∈ M.neighbors v → M.vertex i

private theorem tetra_regular : Regular tetra := by
  constructor
  · intro f h i hi; simp [tetra,Face.hit] at *; omega
  · intro f h; simp [tetra] at *; omega
  · rintro ⟨a,b,c⟩ ⟨x,y,z⟩ hf hg he
    have ha := he a; have hb := he b; have hc := he c
    simp [tetra,Face.hit] at *; grind
  · intro v hv
    simp only [tetra] at *
    rw [ite_eq_left hv]
    exact List.nodup_range.filter _
  · intro v i hv h; simp [tetra] at hv h ⊢; grind

private theorem stack_regular {M : Mesh} (R : Regular M) {f x}
    (hf : M.face f) (fresh : ¬M.vertex x) : Regular (stack M f x) := by
  have old (g) (hg : M.face g) : ¬g.hit x := fun h => fresh (R.corner _ hg _ h)
  have nd := R.distinct f hf
  have nxf := old f hf
  constructor
  · intro g hg i hi
    change i=x ∨ M.vertex i
    rcases hg with ⟨hg,_⟩|h|h|h
    · exact Or.inr (R.corner _ hg _ hi)
    all_goals subst g; simp only [Face.hit] at hi; grind [Regular.corner,Face.hit]
  · intro g hg
    rcases hg with ⟨hg,_⟩|h|h|h
    · exact R.distinct _ hg
    all_goals subst g; simp only [Face.hit] at nxf; dsimp; omega
  · intro g h hg hh eq
    have sameX := eq x
    rcases hg with ⟨hg,_⟩|rfl|rfl|rfl <;> rcases hh with ⟨hh,_⟩|rfl|rfl|rfl
    · exact R.unique _ _ hg hh eq
    all_goals first
      | rfl
      | exact False.elim (old _ hg (sameX.mpr (by simp [Face.hit])))
      | exact False.elim (old _ hh (sameX.mp (by simp [Face.hit])))
      | have a := eq f.a; have b := eq f.b; have c := eq f.c; simp [Face.hit] at *; grind
  · intro v hv
    by_cases hx : v=x
    · subst v; simp [stack,nd]
    · have hvo := (show v=x ∨ M.vertex v from hv).resolve_left hx
      have no : x ∉ M.neighbors v := fun h => fresh (R.neighbor _ _ hvo h)
      by_cases ht : f.hit v <;> simp [stack,hx,ht,R.nodup _ hvo,no]
  · intro v i hv hi
    change i=x ∨ M.vertex i
    by_cases hx : v=x
    · subst v
      have h : f.hit i := by simpa [stack,Face.hit] using hi
      exact Or.inr (R.corner _ hf _ h)
    · have hvo := (show v=x ∨ M.vertex v from hv).resolve_left hx
      by_cases ht : f.hit v <;> simp [stack,hx,ht] at hi <;> grind [Regular.neighbor]

theorem regular {M : Mesh} (h : Stacked M) : Regular M := by
  induction h with
  | tetra => exact tetra_regular
  | insert _ hf hx ih => exact stack_regular ih hf hx

/-- The diagram between permanent names in a mesh and vertices of a closed
triangular map, preserving all edge and face incidences. -/
structure Bridge (M : Mesh) where
  V : Type
  map : Map V
  origin : Recognition.StackedMap map
  enum : Enumeration V
  label : V → Nat
  inj : Function.Injective label
  hits : ∀ i, M.vertex i ↔ ∃ a, label a=i
  edge : ∀ a b, map.adj a b ↔ label b ∈ M.neighbors (label a)
  face : ∀ a b c, map.face a b c ↔ triple M (label a) (label b) (label c)

private theorem old_triple {M : Mesh} (R : Regular M) {f x} (hf : M.face f)
    {i j k} (ix : i ≠ x) (jx : j ≠ x) (kx : k ≠ x) :
    triple (stack M f x) i j k ↔ triple M i j k ∧ ¬(f.hit i ∧ f.hit j ∧ f.hit k) := by
  constructor
  · rintro ⟨ij,jk,ik,g,hg,hi,hj,hk⟩
    rcases hg with ⟨hg,ne⟩|rfl|rfl|rfl
    · refine ⟨⟨ij,jk,ik,g,hg,hi,hj,hk⟩,?_⟩
      rintro ⟨fi,fj,fk⟩
      exact ne (R.unique g f hg hf (fun z =>
        (three_cover g ij jk ik hi hj hk z).trans (three_cover f ij jk ik fi fj fk z).symm))
    all_goals simp [Face.hit] at hi hj hk; grind
  · rintro ⟨⟨ij,jk,ik,g,hg,hi,hj,hk⟩,excluded⟩
    exact ⟨ij,jk,ik,g,Or.inl ⟨hg,fun eq => excluded (eq ▸ ⟨hi,hj,hk⟩)⟩,hi,hj,hk⟩

theorem new_triple {M : Mesh} (R : Regular M) {f x} (fresh : ¬M.vertex x)
    {i j} (ix : i ≠ x) (jx : j ≠ x) :
    triple (stack M f x) i j x ↔ i ≠ j ∧ f.hit i ∧ f.hit j := by
  constructor
  · rintro ⟨ij,_,_,g,hg,hi,hj,hx⟩
    rcases hg with ⟨hg,_⟩|rfl|rfl|rfl
    · exact False.elim (fresh (R.corner _ hg _ hx))
    all_goals simp [Face.hit] at hi hj ⊢; grind
  · rintro ⟨ij,hi,hj⟩
    refine ⟨ij,jx,ix,?_⟩
    have ab : (stack M f x).face ⟨f.a,f.b,x⟩ := Or.inr (Or.inl rfl)
    have ac : (stack M f x).face ⟨f.a,f.c,x⟩ := Or.inr (Or.inr (Or.inl rfl))
    have bc : (stack M f x).face ⟨f.b,f.c,x⟩ := Or.inr (Or.inr (Or.inr rfl))
    rcases hi with rfl|rfl|rfl <;> rcases hj with rfl|rfl|rfl
    · contradiction
    · exact ⟨_,ab,by simp [Face.hit],by simp [Face.hit],by simp [Face.hit]⟩
    · exact ⟨_,ac,by simp [Face.hit],by simp [Face.hit],by simp [Face.hit]⟩
    · exact ⟨_,ab,by simp [Face.hit],by simp [Face.hit],by simp [Face.hit]⟩
    · contradiction
    · exact ⟨_,bc,by simp [Face.hit],by simp [Face.hit],by simp [Face.hit]⟩
    · exact ⟨_,ac,by simp [Face.hit],by simp [Face.hit],by simp [Face.hit]⟩
    · exact ⟨_,bc,by simp [Face.hit],by simp [Face.hit],by simp [Face.hit]⟩
    · contradiction

end Recognition.SourceBridge

namespace Recognition.SourceBridge
open SourceMap Rigidity Reduction

def tetraBridge : Bridge tetra where
  V := Fin 4
  map := Tetrahedron.map
  origin := .tetra
  enum := ⟨List.finRange _,List.nodup_finRange _,List.mem_finRange⟩
  label := Fin.val
  inj := fun _ _ h => Fin.ext h
  hits i := ⟨fun h => ⟨⟨i,h⟩,rfl⟩,fun ⟨a,e⟩ => e ▸ a.isLt⟩
  edge a b := by
    rw [Tetrahedron.adj_iff]
    simp [tetra,a.isLt,b.isLt,Fin.ext_iff,ne_comm]
  face a b c := by
    rw [Tetrahedron.face_iff]
    constructor
    · rintro ⟨ab,bc,ac⟩
      have i := a.isLt; have j := b.isLt; have k := c.isLt
      simp only [ne_eq,Fin.ext_iff] at *
      refine ⟨ab,bc,ac,?_⟩
      rcases Nat.lt_or_gt_of_ne ab with h|h <;> rcases Nat.lt_or_gt_of_ne bc with l|l <;>
        rcases Nat.lt_or_gt_of_ne ac with u|u
      all_goals
        first
        | omega
        | (refine ⟨⟨a,b,c⟩,?_,?_,?_,?_⟩ <;> simp [tetra,Face.hit] <;> omega)
        | (refine ⟨⟨a,c,b⟩,?_,?_,?_,?_⟩ <;> simp [tetra,Face.hit] <;> omega)
        | (refine ⟨⟨b,a,c⟩,?_,?_,?_,?_⟩ <;> simp [tetra,Face.hit] <;> omega)
        | (refine ⟨⟨b,c,a⟩,?_,?_,?_,?_⟩ <;> simp [tetra,Face.hit] <;> omega)
        | (refine ⟨⟨c,a,b⟩,?_,?_,?_,?_⟩ <;> simp [tetra,Face.hit] <;> omega)
        | (refine ⟨⟨c,b,a⟩,?_,?_,?_,?_⟩ <;> simp [tetra,Face.hit] <;> omega)

    · rintro ⟨ab,bc,ac,_⟩
      exact ⟨fun h => ab (congrArg Fin.val h),fun h => bc (congrArg Fin.val h),fun h => ac (congrArg Fin.val h)⟩

private theorem adj_comm {V} (G : Map V) (a b : V) : G.adj a b ↔ G.adj b a :=
  ⟨fun ⟨c,h⟩ => ⟨c,G.flip h⟩,fun ⟨c,h⟩ => ⟨c,G.flip h⟩⟩

private theorem triangleGet {M : Mesh} (B : Bridge M) (R : Regular M) (f : Face) (hf : M.face f) :
    ∃ a b c, B.map.face a b c ∧
      (fun z => f.hit (B.label z)) = Stacking.corners a b c := by
  obtain ⟨a,ea⟩ := (B.hits _).mp (R.corner _ hf _ (Or.inl rfl))
  obtain ⟨b,eb⟩ := (B.hits _).mp (R.corner _ hf _ (Or.inr (Or.inl rfl)))
  obtain ⟨c,ec⟩ := (B.hits _).mp (R.corner _ hf _ (Or.inr (Or.inr rfl)))
  obtain ⟨ab,bc,ac⟩ := R.distinct f hf
  have htr : triple M f.a f.b f.c := ⟨ab,bc,ac,f,hf,Or.inl rfl,Or.inr (Or.inl rfl),Or.inr (Or.inr rfl)⟩
  refine ⟨a,b,c,(B.face ..).mpr (by simpa [ea,eb,ec] using htr),?_⟩
  funext z
  apply propext
  simp [Face.hit,← ea,← eb,← ec,Stacking.corners,B.inj.eq_iff]

/-- Choose a singleton set of faces for simultaneous stellation. The unique
star receives the permanent name of the mesh insertion. -/
private theorem grow {M : Mesh} (B : Bridge M) (R : Regular M)
    {f : Face} {x : Nat} (hf : M.face f) (fresh : ¬ M.vertex x) : Nonempty (Bridge (stack M f x)) := by
  classical
  let target := fun z => f.hit (B.label z)
  let fill : Stacking.Choice B.V := fun k => k = target
  obtain ⟨a₀,b₀,c₀,f₀,eq₀⟩ := triangleGet B R f hf
  let s₀ : Stacking.Star B.map fill := ⟨target,⟨a₀,b₀,c₀,f₀,eq₀⟩,rfl⟩
  let lab : Stacking.Vertex B.map fill → Nat := Sum.elim B.label (fun _ => x)
  have oldNe (a : B.V) : B.label a ≠ x := fun he => fresh ((B.hits _).mpr ⟨a,he⟩)
  have reps (s : Stacking.Star B.map fill) : s.val = target := s.property.2
  have vi (a : B.V) : M.vertex (B.label a) := (B.hits _).mpr ⟨a,rfl⟩
  have marker (a b c : B.V) (distinct : a ≠ b ∧ b ≠ c ∧ a ≠ c) :
      fill (Stacking.corners a b c) ↔ f.hit (B.label a) ∧ f.hit (B.label b) ∧ f.hit (B.label c) := by
    constructor
    · intro h
      change Stacking.corners a b c = target at h
      have ht (u) (hu : Stacking.corners a b c u) : target u := h ▸ hu
      exact ⟨ht _ (Or.inl rfl),ht _ (Or.inr (Or.inl rfl)),ht _ (Or.inr (Or.inr rfl))⟩
    · rintro ⟨ha,hb,hc⟩
      apply funext
      intro z
      apply propext
      have h := three_cover f (B.inj.ne distinct.1) (B.inj.ne distinct.2.1)
        (B.inj.ne distinct.2.2) ha hb hc (B.label z)
      simpa [target,Stacking.corners,B.inj.eq_iff] using h.symm
  refine ⟨{
    V := Stacking.Vertex B.map fill, map := Stacking.stack B.map fill, origin := .subdivide B.origin fill,
    enum := Stacking.enumeration B.map fill B.enum, label := lab, inj := ?_, hits := ?_, edge := ?_, face := ?_ }⟩
  · rintro (a|a) (b|b) h
    · exact congrArg Sum.inl (B.inj h)
    · exact False.elim (oldNe a h)
    · exact False.elim (oldNe b h.symm)
    · exact congrArg Sum.inr (Subtype.ext ((reps a).trans (reps b).symm))
  · intro i
    constructor
    · rintro (rfl|h)
      · exact ⟨.inr s₀,rfl⟩
      · obtain ⟨a,ha⟩ := (B.hits _).mp h
        exact ⟨.inl a,ha⟩
    · rintro ⟨a|s,h⟩
      · exact Or.inr (h ▸ vi a)
      · exact Or.inl h.symm
  · rintro (a|a) (b|b)
    · rw [Stacking.old_edges,B.edge]
      change _ ↔ B.label b ∈ (stack M f x).neighbors (B.label a)
      by_cases ht : f.hit (B.label a) <;> simp [stack,oldNe _,ht]
    · rw [adj_comm,Stacking.star_neighbors,reps]
      change f.hit (B.label a) ↔ x ∈ (stack M f x).neighbors (B.label a)
      have absent : x ∉ M.neighbors (B.label a) := fun h => fresh (R.neighbor _ _ (vi a) h)
      by_cases ht : f.hit (B.label a) <;> simp [stack,oldNe _,ht,absent]
    · rw [Stacking.star_neighbors,reps]
      change f.hit (B.label b) ↔ B.label b ∈ (stack M f x).neighbors x
      simp [stack,Face.hit]
    · have equal : a=b := Subtype.ext ((reps a).trans (reps b).symm)
      subst b
      have no : ¬(Stacking.stack B.map fill).adj (.inr a) (.inr a) := fun ⟨_,h⟩ => (Stacking.stack B.map fill).distinct h rfl
      have nox : ¬f.hit x := fun h => fresh (R.corner _ hf _ h)
      change _ ↔ x ∈ (stack M f x).neighbors x
      simpa [no,stack,Face.hit] using nox
  · have oo (a b c : B.V) : (Stacking.stack B.map fill).face (.inl a) (.inl b) (.inl c) ↔
        triple (stack M f x) (B.label a) (B.label b) (B.label c) := by
      rw [old_triple R hf (oldNe _) (oldNe _) (oldNe _),← B.face]
      change (B.map.face a b c ∧ ¬fill _) ↔ _
      constructor <;> rintro ⟨h,ne⟩
      all_goals
        have nd := And.intro (B.map.distinct h) (And.intro (B.map.distinct (B.map.rot h))
          (Ne.symm (B.map.distinct (B.map.rot (B.map.rot h)))))
        exact ⟨h,by simpa [marker _ _ _ nd] using ne⟩
    have on (a b : B.V) (s : Stacking.Star B.map fill) :
        (Stacking.stack B.map fill).face (.inl a) (.inl b) (.inr s) ↔
          triple (stack M f x) (B.label a) (B.label b) x := by
      rw [new_triple R fresh (oldNe _) (oldNe _)]
      change (a ≠ b ∧ s.val a ∧ s.val b) ↔ _
      simp [reps,target,B.inj.eq_iff]
    have rotate (i j k : Stacking.Vertex B.map fill) :
        (Stacking.stack B.map fill).face i j k ↔ (Stacking.stack B.map fill).face j k i :=
      ⟨(Stacking.stack B.map fill).rot,fun h => (Stacking.stack B.map fill).rot ((Stacking.stack B.map fill).rot h)⟩
    rintro (a|s) (b|t) (c|u)
    · exact oo .. 
    · exact on ..
    · exact (rotate ..).trans ((rotate ..).trans ((on ..).trans triple_rot))
    · simp [Stacking.stack,Stacking.face,triple,lab]
    · exact (rotate ..).trans ((on ..).trans (triple_rot.trans triple_rot))
    · simp [Stacking.stack,Stacking.face,triple,lab]
    · simp [Stacking.stack,Stacking.face,triple,lab]
    · simp [Stacking.stack,Stacking.face,triple,lab]

end Recognition.SourceBridge

namespace Recognition.SourceBridge
open SourceMap Rigidity Reduction

/-- Construct a finite labelled map from every inductively stacked mesh. -/
theorem stacked_bridge {M : Mesh} (h : Stacked M) : Nonempty (Bridge M) := by
  induction h with
  | tetra => exact ⟨tetraBridge⟩
  | insert hm hf hx ih =>
    obtain ⟨B⟩ := ih
    exact grow B (regular hm) hf hx

theorem Bridge.degree_eq {M : Mesh} (B : Bridge M) (h : Regular M) (a : B.V) :
    degree (M := B.map) B.enum a = (M.neighbors (B.label a)).length := by
  classical
  let neighbors := B.enum.vertices.filter (fun b => decide (B.map.adj a b))
  have ha : M.vertex (B.label a) := (B.hits _).mpr ⟨a,rfl⟩
  have nd : (neighbors.map B.label).Nodup := List.pairwise_map.mpr ((B.enum.unique.filter (fun b => decide (B.map.adj a b))).imp
    (fun ne e => ne (B.inj e)))
  have perm : (neighbors.map B.label).Perm (M.neighbors (B.label a)) := by
    apply List.perm_iff_count.mpr
    intro x
    change (List.map B.label (List.filter _ _)).count x = _
    rw [nd.count,(h.nodup _ ha).count]
    have mem : x ∈ neighbors.map B.label ↔ x ∈ M.neighbors (B.label a) := by
      constructor
      · rintro hx
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
        exact (B.edge a b).mp (of_decide_eq_true (List.mem_filter.mp hb).2)
      · intro hx
        obtain ⟨b,rfl⟩ := (B.hits _).mp (h.neighbor _ _ ha hx)
        exact List.mem_map.mpr ⟨_,List.mem_filter.mpr ⟨B.enum.complete b,decide_eq_true ((B.edge a b).mpr hx)⟩,rfl⟩
    change (if x ∈ neighbors.map B.label then 1 else 0) = _
    simp only [mem]
  have card (xs : List B.V) : mass xs (fun b => mark (B.map.adj a b)) =
      (xs.filter (fun b => decide (B.map.adj a b))).length := by
    induction xs with
    | nil => rfl
    | cons b xs ih => by_cases adj : B.map.adj a b <;> simpa [adj,mark,mass,Nat.add_comm] using ih
  exact (card _).trans (by simpa using perm.length_eq)

noncomputable def sourceModel {I : Instance} {M : Mesh} (h : RealizesSource I M)
    (B : Bridge M) : Layers.Model (sourceTable I) where
  V := B.V
  map := B.map
  vertices := B.enum
  label := B.label
  inj _ _ hEq := B.inj hEq
  hits i := (h.2.1 i).symm.trans (B.hits i)
  value a := by
    have bound := (h.2.1 _).mp ((B.hits _).mpr ⟨a,rfl⟩)
    rw [B.degree_eq (regular h.1),h.2.2 ⟨B.label a,bound⟩,List.getElem?_eq_getElem bound]
    rfl

/-- Starting with a partition, obtain one ordinary labelled triangulation
model of the source degree list that realizes every named constraint. -/
theorem prescribed_origin (I : Instance) (hv : Valid I) (hp : ThreePartition I) :
    ∃ R : Layers.Model (sourceTable I), StackedMap R.map ∧ ∀ e ∈ prescribed I, R.edge e.left e.right := by
  obtain ⟨M,h,he⟩ := source_prescribed_stacked I hv hp
  obtain ⟨B⟩ := stacked_bridge h.1
  refine ⟨sourceModel h B,B.origin,?_⟩
  intro e ein
  have bounds := edges_bounds I e ein
  obtain ⟨a,ha⟩ := (B.hits e.left).mp ((h.2.1 _).mpr (by omega))
  obtain ⟨b,hb⟩ := (B.hits e.right).mp ((h.2.1 _).mpr (by omega))
  exact ⟨a,b,ha,hb,(adj_comm B.map a b).mpr ((B.edge b a).mpr (by simpa [ha,hb] using he e ein))⟩

theorem prescribed_model (I : Instance) (hv : Valid I) (hp : ThreePartition I) :
    ∃ R : Layers.Model (sourceTable I), ∀ e ∈ prescribed I, R.edge e.left e.right := by
  obtain ⟨R,_,h⟩ := prescribed_origin I hv hp
  exact ⟨R,h⟩

end Recognition.SourceBridge
