import Reduction

/-! A labelled, constructive model of stacking in a triangular face. Each
triangular face carries a single ordered representative. The other two data
structures retain vertex names and the actual lists of neighbors. -/
namespace Recognition.SourceMap
open Reduction

structure Face where
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq

def Face.hit (f : Face) (v : Nat) := v = f.a ∨ v = f.b ∨ v = f.c

instance (f : Face) (v : Nat) : Decidable (f.hit v) := by unfold Face.hit; infer_instance

structure Mesh where
  vertex : Nat → Prop
  face : Face → Prop
  neighbors : Nat → List Nat

def tetra : Mesh where
  vertex v := v < 4
  face f := f.a < f.b ∧ f.b < f.c ∧ f.c < 4
  neighbors v := if v < 4 then (List.range 4).filter (· != v) else []

def stack (M : Mesh) (f : Face) (x : Nat) : Mesh where
  vertex v := v = x ∨ M.vertex v
  face g := (M.face g ∧ g ≠ f) ∨
    g = ⟨f.a,f.b,x⟩ ∨ g = ⟨f.a,f.c,x⟩ ∨ g = ⟨f.b,f.c,x⟩
  neighbors v := if v = x then [f.a,f.b,f.c]
    else if f.hit v then x :: M.neighbors v else M.neighbors v

/-- Exactly the labelled sphere triangulations constructed by inserting a
fresh vertex in a current triangular face starting from the tetrahedron. -/
inductive Stacked : Mesh → Prop where
  | tetra : Stacked tetra
  | insert {M f x} : Stacked M → M.face f → ¬ M.vertex x → Stacked (stack M f x)

def lastFace (k : Nat) : Face := ⟨k+1,k+2,k+3⟩

/-- The parameter is the number of insertions after the tetrahedron. -/
def cube : Nat → Mesh
  | 0 => tetra
  | k+1 => stack (cube k) (lastFace k) (k+4)

def binFace (r : Nat) : Face := ⟨r,r+1,r+3⟩

theorem cube_vertices (k v : Nat) : (cube k).vertex v ↔ v < k+4 := by
  induction k with
  | zero => exact Iff.rfl
  | succ k ih => change v = k+4 ∨ (cube k).vertex v ↔ _; rw [ih]; omega

theorem cube_last (k : Nat) : (cube k).face (lastFace k) := by
  cases k with
  | zero => simp [cube,tetra,lastFace]
  | succ k =>
    apply Or.inr; apply Or.inr; apply Or.inr
    simp [lastFace,Nat.add_assoc]

theorem cube_stacked (k : Nat) : Stacked (cube k) := by
  induction k with
  | zero => exact .tetra
  | succ k ih => exact .insert ih (cube_last k) (by simp [cube_vertices])

theorem cube_bin_face (k r : Nat) (hr : r+3 < k+4) : (cube k).face (binFace r) := by
  induction k with
  | zero =>
    have : r = 0 := by omega
    subst r
    simp [cube,tetra,binFace]
  | succ k ih =>
    by_cases h : r+3 < k+4
    · apply Or.inl; refine ⟨ih h,?_⟩
      intro eq
      have := congrArg Face.a eq
      have := congrArg Face.c eq
      simp [binFace,lastFace] at *; omega
    · apply Or.inr; apply Or.inl
      have : r = k+1 := by omega
      subst r; rfl

theorem cube_edge (k u v : Nat) (hu : u < k+4) :
    v ∈ (cube k).neighbors u ↔ v < k+4 ∧ u ≠ v ∧ u ≤ v+3 ∧ v ≤ u+3 := by
  induction k generalizing u v with
  | zero =>
    simp [cube,tetra,hu]; omega
  | succ k ih =>
    change v ∈ (if u = k+4 then _ else if _ then _ else _) ↔ _
    by_cases eu : u = k+4
    · simp [eu,lastFace]; omega
    · have ou : u < k+4 := by omega
      by_cases h : (lastFace k).hit u
      · simp [eu,h,ih u v ou]; unfold Face.hit lastFace at h; simp at h; omega
      · simp [eu,h,ih u v ou]; unfold Face.hit lastFace at h; simp at h; omega

theorem cube_degree (k v : Nat) (hv : v < k+4) :
    ((cube k).neighbors v).length = min 3 v + min 3 (k+3-v) := by
  induction k generalizing v with
  | zero =>
    have hv' : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
    rcases hv' with rfl|rfl|rfl|rfl <;> rfl
  | succ k ih =>
    change List.length (if v = k+4 then _ else if _ then _ else _) = _
    by_cases ev : v = k+4
    · subst v; simp
    · have ov : v < k+4 := by omega
      by_cases h : (lastFace k).hit v
      · simp [ev,h,ih v ov]; unfold Face.hit lastFace at h; simp at h; omega
      · simp [ev,h,ih v ov]; unfold Face.hit lastFace at h; simp at h; omega


def chain (M : Mesh) (f : Face) : List Nat → Mesh
  | [] => M
  | x::xs => chain (stack M f x) ⟨f.a,f.b,x⟩ xs

theorem chain_vertices (M : Mesh) (f : Face) (xs : List Nat) (v : Nat) :
    (chain M f xs).vertex v ↔ M.vertex v ∨ v ∈ xs := by
  induction xs generalizing M f with
  | nil => simp [chain]
  | cons x xs ih => simp [chain, ih, stack]; grind

theorem chain_stacked (M : Mesh) (f : Face) (xs : List Nat) (hm : Stacked M) (hf : M.face f)
    (fresh : ∀ x ∈ xs, ¬ M.vertex x) (nd : xs.Nodup) : Stacked (chain M f xs) := by
  induction xs generalizing M f with
  | nil => exact hm
  | cons x xs ih =>
    apply ih _ _ (.insert hm hf (fresh x (by simp))) (.inr (.inl rfl)) _ (List.nodup_cons.mp nd).2
    intro y hy H
    rcases H with rfl|H
    · exact (List.nodup_cons.mp nd).1 hy
    · exact fresh y (by simp [hy]) H

theorem chain_keep_face (M : Mesh) (f g : Face) (xs : List Nat) (hg : M.face g) (ne : g.a ≠ f.a) :
    (chain M f xs).face g := by
  induction xs generalizing M f with
  | nil => exact hg
  | cons x xs ih => exact ih _ _ (.inl ⟨hg, fun he => ne (congrArg Face.a he)⟩) ne

theorem chain_keep_edge (M : Mesh) (f : Face) (xs : List Nat) (u v : Nat)
    (old : u ∉ xs) (he : v ∈ M.neighbors u) : v ∈ (chain M f xs).neighbors u := by
  induction xs generalizing M f with
  | nil => exact he
  | cons x xs ih =>
    simp only [List.mem_cons,not_or] at old
    apply ih _ _ old.2
    by_cases hu : f.hit u <;> simp [stack,old.1,hu,he]

def increment (f : Face) (xs : List Nat) (v : Nat) :=
  if v = f.a ∨ v = f.b then xs.length else if v = f.c ∧ xs ≠ [] then 1 else 0

theorem chain_old_degree (M : Mesh) (f : Face) (xs : List Nat) (v : Nat) (old : v ∉ xs) :
    ((chain M f xs).neighbors v).length = (M.neighbors v).length + increment f xs v := by
  induction xs generalizing M f with
  | nil => simp [chain,increment]
  | cons x xs ih =>
    simp only [List.mem_cons,not_or] at old
    rw [chain, ih _ _ old.2]
    by_cases pole : v = f.a ∨ v = f.b
    · have hit : f.hit v := by unfold Face.hit; grind
      simp [stack,increment,old.1,pole,hit]; omega
    · by_cases third : v = f.c <;> simp [stack,increment,Face.hit,old.1,pole,third] <;> grind

theorem chain_poles (M : Mesh) (f : Face) (xs : List Nat) (nd : xs.Nodup) {x : Nat}
    (hx : x ∈ xs) :
    f.a ∈ (chain M f xs).neighbors x ∧ f.b ∈ (chain M f xs).neighbors x := by
  induction xs generalizing M f with
  | nil => contradiction
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl|tail
    · constructor <;> apply chain_keep_edge _ _ _ _ _ (List.nodup_cons.mp nd).1 <;> simp [stack]
    · exact ih _ ⟨f.a,f.b,y⟩ (List.nodup_cons.mp nd).2 tail

theorem chain_new_degree (M : Mesh) (f : Face) (xs : List Nat) (y : Nat)
    (nd : (xs++[y]).Nodup) (poles : ∀ v ∈ xs++[y], v ≠ f.a ∧ v ≠ f.b) :
    ((chain M f (xs++[y])).neighbors y).length = 3 ∧
    ∀ x ∈ xs, ((chain M f (xs++[y])).neighbors x).length = 4 := by
  induction xs generalizing M f with
  | nil => simp [chain,stack]
  | cons a xs ih =>
    have nd' := List.nodup_cons.mp nd
    have H := ih (stack M f a) ⟨f.a,f.b,a⟩ nd'.2 (fun v hv => poles v (List.mem_cons_of_mem _ hv))
    refine ⟨H.1,?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · rw [List.cons_append,chain,chain_old_degree (stack M f x) ⟨f.a,f.b,x⟩ (xs++[y]) x nd'.1]
      have h := poles x (by simp)
      simp [stack,increment,h.1,h.2]
    · exact H.2 _ hx

/-- Oriented consecutive vertices along a chain of distinct names. -/
inductive Consecutive {α : Type} (x y : α) : List α → Prop
  | here (zs) : Consecutive x y (x::y::zs)
  | later {zs} (h : Consecutive x y zs) (z : α) : Consecutive x y (z::zs)

theorem chain_path (M : Mesh) (f : Face) {xs : List Nat} {x y : Nat}
    (h : Consecutive x y xs) (nd : xs.Nodup) : x ∈ (chain M f xs).neighbors y := by
  induction h generalizing M f with
  | here zs =>
    apply chain_keep_edge _ _ _ _ _ (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
    simp [stack]
  | later _ z ih => exact ih _ _ (List.nodup_cons.mp nd).2


abbrev Row (m : Nat) := Fin m × List Nat

/-- Number each item's path in its original order before sorting into bins. -/
def paths {m} (start : Nat) : List (Fin m × Nat) → List (Row m)
  | [] => []
  | (r,w)::ds => (r,List.range' start w) :: paths (start+w) ds

def contents {m} (rs : List (Row m)) (r : Fin m) :=
  (rs.filter (fun a => a.1 == r)).flatMap Prod.snd

private theorem paths_unroll {m} (k : Nat) (ds : List (Fin m × Nat)) :
    (paths k ds).flatMap Prod.snd = List.range' k (ds.map Prod.snd).sum := by
  induction ds generalizing k with
  | nil => simp [paths]
  | cons d ds ih =>
    simp [paths, ih]

private theorem contents_size {m} (k : Nat) (ds : List (Fin m × Nat)) (r : Fin m) :
    (contents (paths k ds) r).length = (binWeights ds r).sum := by
  induction ds generalizing k with
  | nil => simp [contents,paths,binWeights]
  | cons p ds ih =>
    cases p with
    | mk s w =>
      by_cases h : s = r <;> simp [paths,contents,binWeights,h] at * <;> exact ih _

private theorem contents_mem {m} {rs : List (Row m)} {r : Fin m} {v} :
    v ∈ contents rs r ↔ ∃ xs, (r,xs) ∈ rs ∧ v ∈ xs := by
  simp [contents,List.mem_flatMap]
  grind

private theorem contents_nodup {m} (rs : List (Row m)) (r : Fin m)
    (nd : (rs.flatMap Prod.snd).Nodup) : (contents rs r).Nodup := by
  induction rs with
  | nil => simp [contents]
  | cons p rs ih =>
    obtain ⟨ndh,ndt,ne⟩ := List.nodup_append.mp nd
    by_cases h : p.1 = r
    · simp only [contents,List.filter_cons,beq_iff_eq.mpr h,ite_true,List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨ndh,ih ndt,?_⟩
      intro x hx y hy
      obtain ⟨xs,hm,hy⟩ := contents_mem.mp hy
      exact ne _ hx _ (List.mem_flatMap.mpr ⟨(r,xs),hm,hy⟩)
    · simpa [contents,h] using ih ndt

private theorem different_contents {m} (rs : List (Row m)) {r s : Fin m} (ne : r ≠ s)
    (nd : (rs.flatMap Prod.snd).Nodup) {v : Nat} (hr : v ∈ contents rs r) :
    v ∉ contents rs s := by
  intro hs
  obtain ⟨xs,hx,hv⟩ := contents_mem.mp hr
  obtain ⟨ys,hy,hw⟩ := contents_mem.mp hs
  induction rs with
  | nil => contradiction
  | cons p rs ih =>
    obtain ⟨_,ndt,dis⟩ := List.nodup_append.mp nd
    rcases List.mem_cons.mp hx with eq|hxt <;> rcases List.mem_cons.mp hy with eq'|hyt
    · exact ne (congrArg Prod.fst (eq.trans eq'.symm))
    · subst p; exact dis _ hv _ (List.mem_flatMap.mpr ⟨(s,ys),hyt,hw⟩) rfl
    · subst p; exact dis _ hw _ (List.mem_flatMap.mpr ⟨(r,xs),hxt,hv⟩) rfl
    · exact ih ndt (contents_mem.mpr ⟨_,hxt,hv⟩) (contents_mem.mpr ⟨_,hyt,hw⟩) hxt hyt

private theorem range_pair (k w j : Nat) (hj : j < w-1) :
    Consecutive (k+j) (k+j+1) (List.range' k w) := by
  induction j generalizing k w with
  | zero =>
    obtain ⟨t,rfl⟩ : ∃ t, w=t+2 := ⟨w-2,by omega⟩
    simp [List.range'_succ]; exact .here _
  | succ j ih =>
    obtain ⟨t,rfl⟩ : ∃ t, w=t+1 := ⟨w-1,by omega⟩
    simp only [List.range'_succ]
    have H := Consecutive.later (ih (k+1) t (by omega)) k
    simpa [Nat.add_assoc,Nat.add_comm 1 j] using H

private theorem consecutive_prepend {α} (ls : List α) {x y : α} {xs : List α}
    (h : Consecutive x y xs) : Consecutive x y (ls++xs) := by
  induction ls with
  | nil => exact h
  | cons a ls ih => exact .later ih a

private theorem consecutive_append {α} (ls : List α) {x y : α} {xs : List α}
    (h : Consecutive x y xs) : Consecutive x y (xs++ls) := by
  induction h with
  | here _ => exact .here _
  | later _ a ih => exact .later ih a

private theorem contains_path {m} (rs : List (Row m)) (r : Fin m) (xs : List Nat)
    (h : (r,xs) ∈ rs) {x y : Nat} (p : Consecutive x y xs) : Consecutive x y (contents rs r) := by
  induction rs with
  | nil => contradiction
  | cons a rs ih =>
    rcases List.mem_cons.mp h with rfl|ht
    · simpa [contents] using consecutive_append (contents rs r) p
    · by_cases h : a.1 = r
      · simpa [contents,h] using consecutive_prepend a.2 (ih ht)
      · simpa [contents,h] using ih ht

private theorem item_in_column {m} (k : Nat) (ds : List (Fin m × Nat)) (e : Edge)
    (he : e ∈ itemEdges k (ds.map Prod.snd)) :
    ∃ r, Consecutive e.left e.right (contents (paths k ds) r) := by
  have path : ∃ p ∈ paths k ds, Consecutive e.left e.right p.2 := by
    induction ds generalizing k with
    | nil => simp [itemEdges] at he
    | cons d ds ih =>
      obtain ⟨r,w⟩ := d
      rcases List.mem_append.mp he with h|h
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
        exact ⟨(r,List.range' k w),by simp [paths], range_pair _ _ _ (List.mem_range.mp hj)⟩
      · obtain ⟨p,hp,hh⟩ := ih _ h
        exact ⟨p,List.mem_cons_of_mem _ hp,hh⟩
  obtain ⟨⟨r,xs⟩,hr,hx⟩ := path
  exact ⟨r,contains_path _ _ _ hr hx⟩


def capName (I : Instance) (r : Fin I.bins) := skeletonOrder I + I.weights.sum + r.val

/-- The disjoint lists of original item-vertex names that will be inserted
in the specified faces. -/
structure Columns (I : Instance) where
  items : Fin I.bins → List Nat
  size : ∀ r, (items r).length = I.capacity
  distinct : ∀ r, (items r).Nodup
  bounds : ∀ r x, x ∈ items r → skeletonOrder I ≤ x ∧ x < skeletonOrder I+I.weights.sum
  disjoint : ∀ {r s}, r ≠ s → ∀ x ∈ items r, x ∉ items s
  allItems : ∀ x, skeletonOrder I ≤ x → x < skeletonOrder I+I.weights.sum → ∃ r, x ∈ items r

def Supports (I : Instance) (C : Columns I) :=
  ∀ e ∈ itemEdges (skeletonOrder I) I.weights, ∃ r, Consecutive e.left e.right (C.items r)

theorem partition_columns (I : Instance) (hp : ThreePartition I) : ∃ C : Columns I, Supports I C := by
  obtain ⟨ds,hs,hp⟩ := hp
  let rs := paths (skeletonOrder I) ds
  have eq : rs.flatMap Prod.snd = List.range' (skeletonOrder I) I.weights.sum := by
    rw [← hs]; exact paths_unroll .. 
  have nd : (rs.flatMap Prod.snd).Nodup := eq ▸ List.nodup_range' 1
  refine ⟨⟨contents rs,fun r => (contents_size ..).trans (hp r).1,
    fun r => contents_nodup _ r nd, ?_,fun h _ hm => different_contents _ h nd hm,?_⟩,?_⟩
  · intro r x hx
    obtain ⟨xs,ht,hx⟩ := contents_mem.mp hx
    have H : x ∈ rs.flatMap Prod.snd := List.mem_flatMap.mpr ⟨(r,xs),ht,hx⟩
    rw [eq,List.mem_range'] at H
    obtain ⟨j,hj,rfl⟩ := H
    simp; omega
  · intro x h₁ h₂
    have H : x ∈ rs.flatMap Prod.snd := by
      rw [eq,List.mem_range']
      exact ⟨x-skeletonOrder I,by omega,by simp; omega⟩
    obtain ⟨⟨r,xs⟩,ht,hx⟩ := List.mem_flatMap.mp H
    exact ⟨r,contents_mem.mpr ⟨xs,ht,hx⟩⟩
  · intro e he
    rw [← hs] at he
    exact item_in_column _ _ e he

variable {I : Instance} (C : Columns I)

def names (r : Fin I.bins) := C.items r ++ [capName I r]

private theorem names_bounds (r : Fin I.bins) (x : Nat) (h : x ∈ names C r) :
    skeletonOrder I ≤ x ∧ x < (sourceTable I).length := by
  rw [source_order]
  rcases List.mem_append.mp h with h|h
  · have := C.bounds _ _ h; omega
  · obtain rfl := List.mem_singleton.mp h
    unfold capName
    have := r.isLt; omega

private theorem names_nd (r : Fin I.bins) : (names C r).Nodup := by
  refine List.nodup_append.mpr ⟨C.distinct r,by simp,?_⟩
  intro v hv w hw
  obtain rfl := List.mem_singleton.mp hw
  have := (C.bounds _ _ hv).2
  unfold capName
  omega

private theorem names_disj {r s : Fin I.bins} (ne : r ≠ s) {x} (h : x ∈ names C r) :
    x ∉ names C s := by
  intro h'
  rcases List.mem_append.mp h with hi|hc <;> rcases List.mem_append.mp h' with hj|hd
  · exact C.disjoint ne _ hi hj
  · obtain rfl := List.mem_singleton.mp hd
    have := C.bounds _ _ hi
    unfold capName at this; omega
  · obtain rfl := List.mem_singleton.mp hc
    have := C.bounds _ _ hj
    unfold capName at this; omega
  · exact ne (Fin.ext (Nat.add_left_cancel ((List.mem_singleton.mp hc).symm.trans (List.mem_singleton.mp hd))))

def rootFace (I : Instance) (r : Fin I.bins) := binFace (4*r.val)

private theorem root_corners (r : Fin I.bins) :
    (rootFace I r).a < skeletonOrder I ∧ (rootFace I r).b < skeletonOrder I ∧
      (rootFace I r).c < skeletonOrder I := by
  unfold rootFace binFace skeletonOrder
  have := r.isLt; simp; omega

def assembled (base : Mesh) : List (Fin I.bins) → Mesh
  | [] => base
  | r::rs => chain (assembled base rs) (rootFace I r) (names C r)

private theorem root_ne {r s : Fin I.bins} (ne : r ≠ s) : (rootFace I r).a ≠ (rootFace I s).a := by
  intro h
  apply ne; apply Fin.ext
  change 4*r.val = 4*s.val at h
  omega

private theorem assembled_vertices (base : Mesh) (rs : List (Fin I.bins)) (v : Nat) :
    (assembled C base rs).vertex v ↔ base.vertex v ∨ ∃ r ∈ rs, v ∈ names C r := by
  induction rs with
  | nil => simp [assembled]
  | cons r rs ih => simp [assembled,chain_vertices,ih]; grind

private theorem unused_face (base : Mesh) (rs : List (Fin I.bins)) (r : Fin I.bins)
    (hr : r ∉ rs) (hf : base.face (rootFace I r)) : (assembled C base rs).face (rootFace I r) := by
  induction rs with
  | nil => exact hf
  | cons s rs ih =>
    have ⟨_,tail⟩ := not_or.mp (fun h => hr (List.mem_cons.mpr h))
    exact chain_keep_face _ _ _ _ (ih tail) (root_ne (fun e => hr (List.mem_cons.mpr (.inl e))))

theorem assembled_stacked (base : Mesh) (rs : List (Fin I.bins)) (nd : rs.Nodup) (hv : Stacked base)
    (hb : ∀ v, base.vertex v → v < skeletonOrder I)
    (hf : ∀ r, base.face (rootFace I r)) : Stacked (assembled C base rs) := by
  induction rs with
  | nil => exact hv
  | cons r rs ih =>
    have hn := List.nodup_cons.mp nd
    apply chain_stacked _ _ _ (ih hn.2) (unused_face C _ _ r hn.1 (hf r)) _ (names_nd C _)
    intro x hx old
    rcases (assembled_vertices C _ _ _).mp old with base|inRs
    · have := (names_bounds C _ _ hx).1; have := hb _ base; omega
    · obtain ⟨s,hs,hx'⟩ := inRs
      have ne : r ≠ s := fun eq => hn.1 (eq ▸ hs)
      exact names_disj C ne hx hx'

private theorem accumulated_edges (base : Mesh) (rs : List (Fin I.bins)) (u v : Nat)
    (h : v ∈ base.neighbors u) (fresh : ∀ r ∈ rs, u ∉ names C r) :
    v ∈ (assembled C base rs).neighbors u := by
  induction rs with
  | nil => exact h
  | cons r rs ih => exact chain_keep_edge _ _ _ _ _ (fresh _ (by simp)) (ih (fun _ hr => fresh _ (by simp [hr])))

private theorem inserted_edge (base : Mesh) (rs : List (Fin I.bins)) (nd : rs.Nodup)
    (r : Fin I.bins) (hr : r ∈ rs) (u v : Nat) (hu : u ∈ names C r)
    (given : ∀ M, v ∈ (chain M (rootFace I r) (names C r)).neighbors u) :
    v ∈ (assembled C base rs).neighbors u := by
  induction rs with
  | nil => contradiction
  | cons s rs ih =>
    rcases List.mem_cons.mp hr with rfl|hr
    · exact given _
    · have ns : r ≠ s := by intro e; exact (List.nodup_cons.mp nd).1 (e ▸ hr)
      exact chain_keep_edge _ _ _ _ _ (names_disj C ns hu) (ih (List.nodup_cons.mp nd).2 hr)

private theorem in_pair {α} {x y : α} {xs : List α} (p : Consecutive x y xs) : y ∈ xs := by
  induction p with
  | here _ => simp
  | later _ z ih => exact List.mem_cons_of_mem z ih

private theorem inserted_degree (base : Mesh) (rs : List (Fin I.bins)) (nd : rs.Nodup)
    (r : Fin I.bins) (hr : r ∈ rs) (u : Nat) (hu : u ∈ names C r) :
    ((assembled C base rs).neighbors u).length = if u = capName I r then 3 else 4 := by
  induction rs with
  | nil => contradiction
  | cons s rs ih =>
    rcases List.mem_cons.mp hr with rfl|hr
    · have h := chain_new_degree (assembled C base rs) (rootFace I r) (C.items r) (capName I r)
        (names_nd C _) (by
          intro v hv
          have := (names_bounds C _ _ hv).1
          have := root_corners r; omega)
      by_cases he : u = capName I r
      · simpa [he,assembled,names] using h.1
      · have hi : u ∈ C.items r := by simpa [names,he] using hu
        simpa [he,assembled,names] using h.2 _ hi
    · have ns : r ≠ s := by intro e; exact (List.nodup_cons.mp nd).1 (e ▸ hr)
      rw [assembled,chain_old_degree _ _ _ _ (names_disj C ns hu), ih (List.nodup_cons.mp nd).2 hr]
      have hu' := (names_bounds C _ _ hu).1
      have hs := root_corners s
      have a : u ≠ (rootFace I s).a := by omega
      have b : u ≠ (rootFace I s).b := by omega
      have c : u ≠ (rootFace I s).c := by omega
      simp [increment,a,b,c]


private def bonusValue (B t : Nat) := if t ≤ 1 then B+1 else if t = 3 then 1 else 0

private theorem base_lookup (m v : Nat) (hm : 0 < m) (hv : v < 4*m+3) :
    (skeletonBase m)[v]? = some (min 3 v + min 3 (4*m+2-v)) := by
  obtain ⟨t,rfl⟩ : ∃ t, m=t+1 := ⟨m-1,by omega⟩
  by_cases h : v < 3
  · have : v=0 ∨ v=1 ∨ v=2 := by omega
    rcases this with rfl|rfl|rfl <;> simp [skeletonBase] <;> omega
  · obtain ⟨j,rfl⟩ : ∃ j, v=j+3 := ⟨v-3,by omega⟩
    change ((List.replicate (4*t+1) 6) ++ [5,4,3])[j]? = _
    rw [List.getElem?_append]
    simp only [List.length_replicate]
    split
    · rename_i hj
      simp [hj]; omega
    · rename_i hj
      have : j-(4*t+1)=0 ∨ j-(4*t+1)=1 ∨ j-(4*t+1)=2 := by omega
      rcases this with h'|h'|h' <;> rw [h'] <;> simp <;> omega

private theorem bonus_lookup (m B v : Nat) (hv : v < 4*m+3) :
    (bonuses B m)[v]? = some (if v/4 < m then bonusValue B (v%4) else 0) := by
  induction m generalizing v with
  | zero =>
    have : v=0 ∨ v=1 ∨ v=2 := by omega
    rcases this with rfl|rfl|rfl <;> simp [bonuses]
  | succ m ih =>
    by_cases h : v < 4
    · have : v=0 ∨ v=1 ∨ v=2 ∨ v=3 := by omega
      rcases this with rfl|rfl|rfl|rfl <;> simp [bonuses,bonusValue]
    · have eq := ih (v-4) (by omega)
      rw [bonuses,List.getElem?_append_right (by simp; omega)]
      simp only [List.length_cons,List.length_nil] 
      rw [eq]
      have ev : (v-4)%4 = v%4 := by omega
      have em : (v-4)/4<m ↔ v/4<m+1 := by omega
      simp [ev,em]

private theorem sum_hit (rs : List (Fin m)) (q val : Nat) :
    (rs.map (fun r => if r.val = q then val else 0)).sum =
      (rs.map Fin.val).count q * val := by
  induction rs with
  | nil => simp
  | cons a rs ih => by_cases h : a.val=q <;>
      simp [ih,h,Nat.add_mul,Nat.add_comm]

private theorem vals_range (m : Nat) : (List.finRange m).map Fin.val = List.range m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.finRange_succ_last,List.map_append,List.range_succ]
    simpa [List.map_map,Function.comp_def] using congrArg (· ++ [m]) ih

private theorem column_increment (r : Fin I.bins) (v : Nat) :
    increment (rootFace I r) (names C r) v =
      if r.val = v/4 then bonusValue I.capacity (v%4) else 0 := by
  unfold increment rootFace binFace bonusValue
  have nonempty : C.items r ++ [capName I r] ≠ [] := by simp
  simp [names,C.size,nonempty]
  grind only

private theorem original_degree (base : Mesh) (v : Nat) (hv : v < skeletonOrder I)
    (rs : List (Fin I.bins)) :
    ((assembled C base rs).neighbors v).length = (base.neighbors v).length +
      (rs.map fun r => if r.val = v/4 then bonusValue I.capacity (v%4) else 0).sum := by
  induction rs with
  | nil => simp [assembled]
  | cons r rs ih =>
    have old : v ∉ names C r := fun h => Nat.not_le_of_lt hv (names_bounds C _ _ h).1
    rw [assembled,chain_old_degree _ _ _ _ old,ih,column_increment]
    simp; omega

private theorem mesh_degree_at_root (v : Nat) (hv : v < skeletonOrder I) (hm : 0 < I.bins) :
    let k := skeletonOrder I-4
    ((assembled C (cube k) (List.finRange I.bins)).neighbors v).length =
      (min 3 v + min 3 (4*I.bins+2-v)) +
      (if v/4 < I.bins then bonusValue I.capacity (v%4) else 0) := by
  intro k
  have k4 : k+4 = skeletonOrder I := by unfold k skeletonOrder; omega
  have k3 : k+3 = 4*I.bins+2 := by unfold k skeletonOrder; omega
  rw [original_degree _ _ _ hv,sum_hit,vals_range,cube_degree _ _ (by omega),k3,
    List.nodup_range.count]
  by_cases h : v/4 < I.bins <;> simp [h]


private def consecutiveColumns (I : Instance) (hv : Valid I) : Columns I := by
  let q := skeletonOrder I
  let B := I.capacity
  obtain ⟨hm,hl,hs,hw⟩ := hv
  have bp : 0 < B := by
    have hi : 0 < I.weights.length := by omega
    have := (hw _ (List.getElem_mem (n := 0) hi)).2
    change 0 < I.capacity; omega
  let row := fun r : Fin I.bins => List.range' (q+r.val*B) B
  have unroll (r : Fin I.bins) {x : Nat} (h : x ∈ row r) :
      ∃ j<B, x = q+r.val*B+j := by simpa [row,List.mem_range'] using h
  have owner (r : Fin I.bins) {x : Nat} (h : x ∈ row r) : (x-q)/B = r.val := by
    obtain ⟨j,hj,rfl⟩ := unroll r h
    rw [show q+r.val*B+j-q = B*r.val+j by rw [Nat.mul_comm B]; omega,
      Nat.mul_add_div bp,Nat.div_eq_of_lt hj,Nat.add_zero]
  refine ⟨row,fun r => by simp [row,B],fun _ => List.nodup_range' 1,?_,?_,?_⟩
  · intro r x h
    obtain ⟨j,hj,rfl⟩ := unroll r h
    have H := Nat.mul_le_mul_right B r.isLt
    rw [Nat.succ_mul] at H
    change q ≤ _ ∧ _ < q+I.weights.sum
    change I.weights.sum = I.bins*B at hs
    omega
  · intro r s ne x hx h
    exact ne (Fin.ext ((owner r hx).symm.trans (owner s h)))
  · intro x lo hi
    change q ≤ x at lo
    change x < q+I.weights.sum at hi
    let i := (x-q)/B
    have ilt : i < I.bins := (Nat.div_lt_iff_lt_mul bp).mpr (by change x-q<I.bins*I.capacity; omega)
    refine ⟨⟨i,ilt⟩,List.mem_range'.mpr ⟨(x-q)%B,Nat.mod_lt _ bp,?_⟩⟩
    change x = q+i*B+1*((x-q)%B)
    have := Nat.div_add_mod (x-q) B
    dsimp [i]; rw [Nat.mul_comm _ B]; omega

def sourceMesh (C : Columns I) :=
  assembled C (cube (skeletonOrder I-4)) (List.finRange I.bins)

/-- Stacking realization of the concrete, ordered degree list. -/
def RealizesSource (I : Instance) (M : Mesh) :=
  Stacked M ∧ (∀ v, M.vertex v ↔ v < (sourceTable I).length) ∧
    ∀ i : Fin (sourceTable I).length, (M.neighbors i.val).length = (sourceTable I)[i.val]

theorem columns_realize (C : Columns I) (hv : Valid I) : RealizesSource I (sourceMesh C) := by
  let k := skeletonOrder I-4
  have hm := hv.1
  have k4 : k+4 = skeletonOrder I := by unfold k skeletonOrder; omega
  have order := source_order I
  have old (v : Nat) : (cube k).vertex v ↔ v < skeletonOrder I := by rw [cube_vertices,k4]
  have new (v : Nat) (lo : skeletonOrder I ≤ v) (hi : v < (sourceTable I).length) :
      ∃ r, v ∈ names C r := by
    by_cases ahead : v < skeletonOrder I+I.weights.sum
    · obtain ⟨r,h⟩ := C.allItems v lo ahead
      exact ⟨r,List.mem_append_left _ h⟩
    · let i := v-(skeletonOrder I+I.weights.sum)
      have ir : i<I.bins := by unfold i; omega
      refine ⟨⟨i,ir⟩, List.mem_append_right _ (List.mem_singleton.mpr ?_)⟩
      unfold capName; change _ = _+i; unfold i; omega
  refine ⟨assembled_stacked C (cube k) _ (List.nodup_finRange _) (cube_stacked k)
    (fun v => (old v).mp) (fun r => cube_bin_face _ _ (by
      rw [k4]; unfold skeletonOrder; have := r.isLt; omega)),?_,?_⟩
  · intro v
    rw [sourceMesh,assembled_vertices,cube_vertices,show skeletonOrder I-4+4 = _ from k4]
    constructor
    · rintro (h|⟨r,_,h⟩)
      · omega
      · exact (names_bounds C _ _ h).2
    · intro h
      by_cases hl : v<skeletonOrder I
      · exact .inl hl
      · obtain ⟨r,hr⟩ := new v (by omega) h
        exact .inr ⟨r,List.mem_finRange _,hr⟩
  · rintro ⟨i,ilt⟩
    let core := List.zipWith (·+·) (skeletonBase I.bins) (bonuses I.capacity I.bins)
    have src : sourceTable I = core ++ (List.replicate I.weights.sum 4 ++ List.replicate I.bins 3) := by
      simp [sourceTable,core,List.append_assoc]
    have lc : core.length = skeletonOrder I := by
      rw [src] at order
      simp at order; omega
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem ilt]
    change some ((sourceMesh C).neighbors i).length = (sourceTable I)[i]?
    rw [src,List.getElem?_append,lc]
    split
    · rename_i hi
      have H := mesh_degree_at_root C _ hi hm
      change ((sourceMesh C).neighbors i).length = _ at H
      change some ((sourceMesh C).neighbors i).length = core[i]?
      rw [H]
      simp [core,List.getElem?_zipWith,base_lookup _ _ hm hi,bonus_lookup _ _ _ hi]
    · rename_i hi
      have hl := ilt
      rw [List.getElem?_append,List.length_replicate]
      split
      · rename_i hh
        obtain ⟨r,hr⟩ := C.allItems i (by omega) (by omega)
        have h := inserted_degree C (cube k) _ (List.nodup_finRange _) r (List.mem_finRange _) i
          (List.mem_append_left _ hr)
        have ne : i ≠ capName I r := by unfold capName; omega
        change ((sourceMesh C).neighbors i).length = _ at h
        simp [h,ne,hh]
      · rename_i hh
        obtain ⟨r,hr⟩ := new i (by omega) ilt
        have eq : i = capName I r := by
          rcases List.mem_append.mp hr with h|h
          · have := (C.bounds r _ h).2; omega
          · exact List.mem_singleton.mp h
        have h := inserted_degree C (cube k) _ (List.nodup_finRange _) r (List.mem_finRange _) i hr
        change ((sourceMesh C).neighbors i).length = _ at h
        have hlt : i-skeletonOrder I-I.weights.sum < I.bins := by omega
        rw [h,ite_eq_left eq,List.getElem?_replicate,ite_eq_left hlt]

theorem source_bare_stacked (I : Instance) (hv : Valid I) :
    ∃ M, RealizesSource I M :=
  ⟨sourceMesh (consecutiveColumns I hv), columns_realize _ hv⟩

/-- A partition gives one labelled stacked realization containing *all* source
constraints, including every edge inside every original item's interval. -/
theorem source_prescribed_stacked (I : Instance) (hv : Valid I) (hp : ThreePartition I) :
    ∃ M, RealizesSource I M ∧ ∀ e ∈ prescribed I, e.left ∈ M.neighbors e.right := by
  obtain ⟨C,hc⟩ := partition_columns I hp
  refine ⟨sourceMesh C,columns_realize C hv,?_⟩
  intro e he
  let k := skeletonOrder I-4
  have k4 : k+4 = skeletonOrder I := by
    have := hv.1; unfold k skeletonOrder; omega
  rcases List.mem_append.mp he with old|cap
  · rcases List.mem_append.mp old with skel|item
    · obtain ⟨d,hd,h⟩ := List.mem_flatMap.mp skel
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
      have bound := List.mem_range.mp hj
      have dif : d=1 ∨ d=2 ∨ d=3 := by simpa using hd
      have lt : j+d < skeletonOrder I := by omega
      apply accumulated_edges C (cube k)
      · apply (cube_edge k (j+d) j (by omega)).mpr
        dsimp; omega
      · intro r _ hm
        have := (names_bounds C r _ hm).1
        exact (Nat.not_le_of_lt lt) this
    · obtain ⟨r,h⟩ := hc e item
      have hx : e.right ∈ names C r := List.mem_append_left _ (in_pair h)
      exact inserted_edge C _ _ (List.nodup_finRange _) r (List.mem_finRange _) _ _ hx
        (fun M => chain_path M _ (consecutive_append _ h) (names_nd C r))
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp cap
    let r : Fin I.bins := ⟨j,List.mem_range.mp hj⟩
    have hx : capName I r ∈ names C r := by simp [names]
    exact inserted_edge C _ _ (List.nodup_finRange _) r (List.mem_finRange _) _ _ hx
      (fun M => (chain_poles M (rootFace I r) _ (names_nd C r) hx).1)


theorem root_target (I : Instance) (hi : Valid I) (r : Fin I.bins) :
    (sourceTable I)[4*r.val]? =
      some (min 3 (4*r.val) + min 3 (4*I.bins+2-4*r.val) + (I.capacity+1)) := by
  let C := consecutiveColumns I hi
  have hr : 4*r.val < skeletonOrder I := (root_corners r).1
  have bound : 4*r.val < (sourceTable I).length := by rw [source_order]; omega
  have H := (columns_realize C hi).2.2 ⟨_,bound⟩
  rw [List.getElem?_eq_getElem bound, ← H]
  have K := mesh_degree_at_root C _ hr hi.1
  simpa [sourceMesh,bonusValue,r.isLt] using K

theorem cube_neighbors_distinct (k v : Nat) (hv : v < k+4) : ((cube k).neighbors v).Nodup := by
  induction k generalizing v with
  | zero => simp only [cube,tetra,ite_eq_left hv]; exact List.nodup_range.filter _
  | succ k ih =>
    change List.Nodup (if v = k+4 then _ else if _ then _ else _)
    split
    · simp [lastFace]
    · have old : v < k+4 := by omega
      split
      · apply List.nodup_cons.mpr
        exact ⟨fun h => (Nat.lt_irrefl _ ((cube_edge k _ _ old).mp h).1),ih v old⟩
      · exact ih v old

end Recognition.SourceMap
