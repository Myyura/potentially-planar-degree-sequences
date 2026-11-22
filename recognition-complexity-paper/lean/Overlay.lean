import FrontierStep
import Outline

/-! Compress the face dual at an actual replay prefix. A retained edge has a
midpoint. Delete those midpoints temporarily from the read dual and contract
each remaining connected patch to a hub. Its incidences with the retained
midpoints form the spokes. This avoids choosing a Steiner tree inside each
read component. -/
namespace Recognition.Overlay
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep

abbrev Id (fs : List Face) := Fin fs.length
def flags (fs : List Face) (i : Id fs) : List Edge := (fs.get i).sides.map Event.edge
def adjacency (fs : List Face) (allow : Edge → Prop) (i j : Id fs) : Prop :=
  ∃ e, e ∈ flags fs i ∧ e ∈ flags fs j ∧ allow e

private theorem sym {fs : List Face} {allow : Edge → Prop} {i j : Id fs}
    (h : adjacency fs allow i j) : adjacency fs allow j i := by
  obtain ⟨e,a,b,c⟩ := h
  exact ⟨e,b,a,c⟩

def patchRel (fs : List Face) (keep : List Edge) : Setoid (Id fs) where
  r := Walk (adjacency fs (· ∉ keep))
  iseqv := ⟨fun _ => .refl,fun h => h.symm (fun _ _ => sym),fun h k => h.trans k⟩

abbrev Patch (fs : List Face) (keep : List Edge) := Quotient (patchRel fs keep)
def hub {fs : List Face} (keep : List Edge) (i : Id fs) : Patch fs keep := Quotient.mk _ i

private theorem eq_hub {fs keep} {i j : Id fs} :
    hub keep i = hub keep j ↔ Walk (adjacency fs (· ∉ keep)) i j :=
  ⟨Quotient.exact,Quotient.sound (s := patchRel fs keep)⟩

def indices (fs : List Face) (e : Edge) :=
  (List.finRange fs.length).filter (fun i => (flags fs i).contains e)

private theorem indices_mem {fs : List Face} {e : Edge} {i : Id fs} :
    i ∈ indices fs e ↔ e∈flags fs i := by simp [indices]

private theorem count_indices (fs : List Face) (e : Edge) :
    (indices fs e).length = occurrences (fs.flatMap Face.sides) e := by
  have L (is : List (Id fs)) :
      (is.filter (fun i => (flags fs i).contains e)).length =
        ((is.flatMap (flags fs)).count e) := by
    induction is with
    | nil => simp
    | cons i is ih =>
      have nd : (flags fs i).Nodup := (fs.get i).distinct_sides
      by_cases h : e∈flags fs i <;> simp_all [nd.count,Nat.add_comm]
  rw [indices,L,occurrences]
  have table : (List.finRange fs.length).map fs.get = fs := by
    apply List.ext_getElem <;> simp
  rw [List.map_flatMap]
  have h := congrArg (fun xs : List Face => (xs.flatMap (fun f => f.sides.map Event.edge)).count e) table
  unfold flags
  exact (List.flatMap_map fs.get (fun f => f.sides.map Event.edge) (List.finRange fs.length)) ▸ h

def retained (s : Inventory) := (s.pending ++ retain (live s) s).eraseDups

def contacts (fs : List Face) (keep : List Edge) :=
  keep.flatMap (fun e => (indices fs e).map (e,·))

private theorem contacts_mem {fs : List Face} {keep : List Edge} {e : Edge} {i : Id fs} :
    (e,i) ∈ contacts fs keep ↔ e∈keep ∧ e∈flags fs i := by
  simp [contacts,List.mem_flatMap,indices_mem]

theorem contacts_bound (fs : List Face) (s : Inventory) (ok : replay (fs.flatMap Face.sides)=some s) :
    (contacts fs (retained s)).length ≤ 2*(retained s).length := by
  have aux (keep : List Edge) : (contacts fs keep).length ≤ 2*keep.length := by
    induction keep with
    | nil => simp [contacts]
    | cons e es ih =>
      have cap := (replay_accurate ok).cap e
      rw [← count_indices] at cap
      simp only [contacts,List.flatMap_cons,List.length_append,List.length_map,List.length_cons] at *
      omega
  exact aux _

def spokes (fs : List Face) (keep : List Edge) : List (Edge × Patch fs keep) :=
  (contacts fs keep).map (fun p => (p.1,hub keep p.2))

private theorem spoke_mem {fs : List Face} {keep : List Edge} {e : Edge} {p : Patch fs keep} :
    (e,p)∈spokes fs keep ↔ e∈keep ∧ ∃ i : Id fs, e∈flags fs i ∧ hub keep i=p := by
  simp only [spokes,List.mem_map,Prod.exists,Prod.mk.injEq,contacts_mem]
  grind

def dualLink {P : Type} (sp : List (Edge × P)) (a b : P) : Prop :=
  ∃ e, (e,a)∈sp ∧ (e,b)∈sp

/-- The decoder uses only the dual spokes; primal segments never connect
different read-face blocks. -/
def decoded {P : Type} (sp : List (Edge × P)) (e f : Edge) : Prop :=
  ∃ a b, (e,a) ∈ sp ∧ (f,b) ∈ sp ∧ Walk (dualLink sp) a b

def sameBlock (fs : List Face) (e f : Edge) : Prop :=
  ∃ i j : Id fs, e∈flags fs i ∧ f∈flags fs j ∧ Walk (adjacency fs (fun _ => True)) i j

private theorem full_of_equal {fs : List Face} {keep : List Edge} {i j : Id fs}
    (h : hub keep i = hub keep j) : Walk (adjacency fs (fun _ => True)) i j := by
  exact Walk.map id (fun _ _ ⟨e,a,b,_⟩ => ⟨e,a,b,trivial⟩) (eq_hub.mp h)

private theorem project {fs : List Face} {keep : List Edge} {i j : Id fs}
    (h : Walk (adjacency fs (fun _ => True)) i j) :
    Walk (dualLink (spokes fs keep)) (hub keep i) (hub keep j) := by
  induction h with
  | refl => exact .refl
  | @step j k _ edge ih =>
    obtain ⟨e,a,b,_⟩ := edge
    by_cases pin : e∈keep
    · exact ih.step ⟨e,spoke_mem.mpr ⟨pin,j,a,rfl⟩,spoke_mem.mpr ⟨pin,k,b,rfl⟩⟩
    · exact (eq_hub.mpr (Walk.step Walk.refl ⟨e,a,b,pin⟩)) ▸ ih

private theorem liftWalk {fs : List Face} {keep : List Edge} {i : Id fs} {p : Patch fs keep}
    (h : Walk (dualLink (spokes fs keep)) (hub keep i) p) :
    ∀ j : Id fs, p = hub keep j → Walk (adjacency fs (fun _ => True)) i j := by
  induction h with
  | refl => exact fun _ => full_of_equal
  | step _ edge ih =>
    obtain ⟨e,m,n⟩ := edge
    obtain ⟨_,a,ha,pa⟩ := spoke_mem.mp m
    obtain ⟨_,b,hb,pb⟩ := spoke_mem.mp n
    exact fun _ last => ((ih _ pa.symm).step ⟨e,ha,hb,trivial⟩).trans (full_of_equal (pb.trans last))

theorem blocks_correct (fs : List Face) (s : Inventory) {e f : Edge}
    (a : e∈s.pending) (b : f∈s.pending) :
    decoded (spokes fs (retained s)) e f ↔ sameBlock fs e f := by
  have keep {g : Edge} (h : g∈s.pending) : g∈retained s := by simp [retained,h]
  constructor
  · rintro ⟨p,q,hp,hq,walk⟩
    obtain ⟨_,i,hi,rfl⟩ := spoke_mem.mp hp
    obtain ⟨_,j,hj,rfl⟩ := spoke_mem.mp hq
    exact ⟨i,j,hi,hj,liftWalk walk _ rfl⟩
  · rintro ⟨i,j,hi,hj,walk⟩
    exact ⟨_,_,spoke_mem.mpr ⟨keep a,i,hi,rfl⟩,spoke_mem.mpr ⟨keep b,j,hj,rfl⟩,project walk⟩


/-- Original vertices, marked edge midpoints, and face or patch centres. -/
inductive Node (P : Type) where
  | vertex (v : Nat)
  | point (e : Edge)
  | centre (p : P)

def segments {P : Type} (keep : List Edge) : List (Node P × Node P) :=
  keep.flatMap fun e => [(.vertex e.lo,.point e),(.vertex e.hi,.point e)]

def edges (fs : List Face) (s : Inventory) :=
  segments (P := Patch fs (retained s)) (retained s) ++
  (spokes fs (retained s)).map (fun p => (.point p.1,.centre p.2))

def vertices (fs : List Face) (s : Inventory) : List (Node (Patch fs (retained s))) :=
  (activeNames s).eraseDups.map .vertex ++ (retained s).map .point ++
  (spokes fs (retained s)).map (fun p => .centre p.2)

private theorem segments_length {P : Type} (keep : List Edge) :
    (segments (P := P) keep).length = 2*keep.length := by
  induction keep with
  | nil => rfl
  | cons e es ih => simp [segments] at *; omega

theorem size (fs : List Face) (s : Inventory) (ok : replay (fs.flatMap Face.sides)=some s) :
    (edges fs s).length ≤ 4*(retained s).length ∧
    (vertices fs s).length ≤ (activeNames s).eraseDups.length + 3*(retained s).length := by
  have cap := contacts_bound fs s ok
  simp [edges,vertices,segments_length,spokes]
  omega

/-- The vertex-edge and edge-face part of the barycentric subdivision of
the underlying triangular complex. -/
def flagAdj (fs : List Face) : Node (Id fs) → Node (Id fs) → Prop
  | .vertex v,.point e | .point e,.vertex v => touches e v
  | .point e,.centre i | .centre i,.point e => e∈flags fs i
  | _,_ => False

private theorem flagSym {fs : List Face} (a b) : flagAdj fs a b → flagAdj fs b a := by
  cases a <;> cases b <;> exact id

/-- The branch assignment gives every retained midpoint its own singleton.
An unretained midpoint incident with a read face belongs to that face's
patch, independent of which incident face is chosen. -/
noncomputable def site (fs : List Face) (keep : List Edge) :
    Node (Id fs) → Option (Node (Patch fs keep))
  | .vertex v => some (.vertex v)
  | .centre i => some (.centre (hub keep i))
  | .point e => if e∈keep then some (.point e) else
      if h : ∃ i, e∈flags fs i then some (.centre (hub keep (Classical.choose h))) else none


private theorem hidden_site {fs keep e} {i : Id fs} (outside : e∉keep) (inc : e∈flags fs i) :
    site fs keep (.point e) = some (.centre (hub keep i)) := by
  classical
  have h : ∃ j, e∈flags fs j := ⟨i,inc⟩
  have H : hub keep (Classical.choose h) = hub keep i := eq_hub.mpr
    (Walk.step Walk.refl ⟨e,Classical.choose_spec h,inc,outside⟩)
  simp [site,outside,h,H]

def strand (fs : List Face) (keep : List Edge) (p : Node (Patch fs keep))
    (a b : Node (Id fs)) : Prop :=
  flagAdj fs a b ∧ site fs keep a = some p ∧ site fs keep b = some p

private theorem strandSym {fs keep p} (a b) (h : strand fs keep p a b) :
    strand fs keep p b a := ⟨flagSym _ _ h.1,h.2.2,h.2.1⟩

private theorem through {fs keep} {i j : Id fs} (h : hub keep i = hub keep j) :
    Walk (strand fs keep (.centre (hub keep i))) (.centre i) (.centre j) := by
  have w := eq_hub.mp h
  clear h
  induction w with
  | refl => exact .refl
  | @step j k path side ih =>
    obtain ⟨e,a,b,hidden⟩ := side
    have ij : hub keep i = hub keep j := eq_hub.mpr path
    have jk : hub keep j = hub keep k := eq_hub.mpr (Walk.step Walk.refl ⟨e,a,b,hidden⟩)
    have centreJ : site fs keep (.centre j) = some (.centre (hub keep i)) := by simp [site,ij]
    have mid : site fs keep (.point e) = some (.centre (hub keep i)) := by rw [ij]; exact hidden_site hidden a
    have centreK : site fs keep (.centre k) = some (.centre (hub keep i)) := by simp [site,ij,jk]
    have half : Walk (strand fs keep (.centre (hub keep i))) (.centre i) (.point e) := ih.step ⟨a,centreJ,mid⟩
    exact half.step ⟨b,mid,centreK⟩

private theorem toSite {fs keep} {i : Id fs} {x : Node (Id fs)}
    (assigned : site fs keep x = some (.centre (hub keep i))) :
    Walk (strand fs keep (.centre (hub keep i))) (.centre i) x := by
  classical
  cases x with
  | vertex v => simp [site] at assigned
  | centre j => exact through (by simpa [site] using assigned.symm)
  | point e =>
    by_cases pin : e∈keep
    · simp [site,pin] at assigned
    · by_cases h : ∃ j, e∈flags fs j
      · let j := Classical.choose h
        have inc : e∈flags fs j := Classical.choose_spec h
        have same : hub keep i = hub keep j := by simpa [site,pin,h,j] using assigned.symm
        exact (through same).step ⟨inc,by simp [site,same],assigned⟩
      · simp [site,pin,h] at assigned

/-- Explicit branch-set model: the fibres of one partial function are
disjoint, give connected nonempty branches for the listed vertices, and
every overlay edge is realized by an incidence between its two fibres. -/
structure BranchModel {A B : Type} (vs : List A) (es : List (A×A)) (adj : B → B → Prop) where
  branch : B → Option A
  nonempty : ∀ a ∈ vs, ∃ x, branch x=some a
  connected : ∀ a ∈ vs, ∀ x y, branch x=some a → branch y=some a →
    Walk (fun u v => adj u v ∧ branch u=some a ∧ branch v=some a) x y
  realize : ∀ a b, (a,b) ∈ es → ∃ x y, branch x=some a ∧ branch y=some b ∧ adj x y

private theorem point_unique {fs keep e} (x : Node (Id fs))
    (h : site fs keep x = some (.point e)) : x = .point e := by
  cases x with
  | vertex v => simp [site] at h
  | centre i => simp [site] at h
  | point f =>
    by_cases m : f∈keep
    · simpa [site,m] using h
    · unfold site at h
      simp only [m,↓reduceIte] at h
      split at h <;> simp_all

private theorem vertex_unique {fs keep v} (x : Node (Id fs))
    (h : site fs keep x = some (.vertex v)) : x = .vertex v := by
  cases x with
  | vertex a => simpa [site] using h
  | centre i => simp [site] at h
  | point f =>
    by_cases m : f∈keep <;> by_cases inc : ∃ i, f∈flags fs i <;> simp [site,m,inc] at h

noncomputable def branchModel (fs : List Face) (s : Inventory) :
    BranchModel (vertices fs s) (edges fs s) (flagAdj fs) := by
  classical
  let K := retained s
  refine {branch := site fs K, nonempty := ?_, connected := ?_, realize := ?_}
  · intro a m
    simp only [vertices,List.mem_append,List.mem_map,Prod.exists] at m
    rcases m with ((⟨v,_,rfl⟩|⟨e,he,rfl⟩)|⟨e,p,sp,rfl⟩)
    · exact ⟨.vertex v,rfl⟩
    · exact ⟨.point e,by simp [site,K,he]⟩
    · obtain ⟨_,i,_,rfl⟩ := spoke_mem.mp sp
      exact ⟨.centre i,rfl⟩
  · intro a m x y hx hy
    cases a with
    | vertex v =>
      obtain rfl := vertex_unique x hx
      obtain rfl := vertex_unique y hy
      exact .refl
    | point e =>
      obtain rfl := point_unique x hx
      obtain rfl := point_unique y hy
      exact .refl
    | centre p =>
      obtain ⟨i,rfl⟩ := Quotient.exists_rep p
      exact ((toSite hx).symm strandSym).trans (toSite hy)
  · intro a b m
    simp only [edges,List.mem_append,segments,List.mem_flatMap,List.mem_cons,List.not_mem_nil,
      or_false,List.mem_map,Prod.exists] at m
    rcases m with ⟨e,he,h|h⟩|⟨e,p,sp,eq⟩
    · cases h
      exact ⟨.vertex e.lo,.point e,rfl,by simp [K,site,he],by simp [flagAdj,touches]⟩
    · cases h
      exact ⟨.vertex e.hi,.point e,rfl,by simp [K,site,he],by simp [flagAdj,touches]⟩
    · cases eq
      obtain ⟨he,i,inc,rfl⟩ := spoke_mem.mp sp
      exact ⟨.point e,.centre i,by simp [K,site,he],rfl,inc⟩

theorem branch_assignment (fs : List Face) (s : Inventory) :
    (branchModel fs s).branch=site fs (retained s) := rfl

theorem barycentric_minor (fs : List Face) (s : Inventory) :
    Nonempty (BranchModel (vertices fs s) (edges fs s) (flagAdj fs)) := ⟨branchModel fs s⟩

end Recognition.Overlay

namespace Recognition.Overlay
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep

theorem distinct_names {α : Type} [DecidableEq α] (xs : List α) : xs.eraseDups.Nodup := by
  have loop (ls acc : List α) (h : acc.Nodup) :
      (List.eraseDupsBy.loop (· == ·) ls acc).Nodup := by
    induction ls generalizing acc with
    | nil =>
      exact List.pairwise_reverse.mpr (h.imp Ne.symm)
    | cons v vs ih =>
      unfold List.eraseDupsBy.loop
      split
      · exact ih _ h
      · next no =>
        apply ih
        apply List.nodup_cons.mpr
        exact ⟨fun m => by have yes : (acc.any (fun x => v == x))=true := List.any_eq_true.mpr ⟨v,m,by simp⟩; grind,h⟩
  exact loop xs [] (by simp)

def flagEdges (fs : List Face) (s : Inventory) : List (Node (Id fs) × Node (Id fs)) :=
  segments (retained s) ++ (contacts fs (retained s)).map (fun p => (.point p.1,.centre p.2))

def contractNode {fs : List Face} (K : List Edge) : Node (Id fs) → Node (Patch fs K)
  | .vertex x => .vertex x
  | .point e => .point e
  | .centre i => .centre (hub K i)

private theorem segments_map (fs : List Face) (K es : List Edge) :
    (segments (P := Id fs) es).map (Prod.map (contractNode K) (contractNode K)) = segments es := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [segments,Prod.map,contractNode] using ih

/-- A witness for every edge occurrence, including parallel spokes.
Distinct spokes in the overlay come from distinct barycentric incidences. -/
theorem flag_edges (fs : List Face) (s : Inventory) :
    (flagEdges fs s).Nodup ∧
    (flagEdges fs s).map (Prod.map (contractNode (retained s)) (contractNode (retained s))) = edges fs s ∧
    ∀ u v, (u,v)∈flagEdges fs s → flagAdj fs u v ∧
      site fs (retained s) u=some (contractNode (retained s) u) ∧
      site fs (retained s) v=some (contractNode (retained s) v) := by
  let K := retained s
  have nk : K.Nodup := distinct_names _
  have seg {P : Type} : (segments (P := P) K).Nodup := by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro e _
      have ne := Nat.ne_of_lt e.increasing
      simp [ne]
    · apply nk.imp
      intro e f ne a ha b hb
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha hb
      rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> grind
  have ct : (contacts fs K).Nodup := by
    apply List.pairwise_flatMap.mpr
    constructor
    · intro e _
      apply List.pairwise_map.mpr
      exact ((List.nodup_finRange _).filter _).imp (fun h eq => h (congrArg Prod.snd eq))
    · apply nk.imp
      rintro e f ne a ha b hb
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
      exact fun eq => ne (congrArg Prod.fst eq)
  constructor
  · apply List.nodup_append.mpr
    refine ⟨seg,List.pairwise_map.mpr (ct.imp (fun h eq => by
      rcases ‹Edge × Id fs› with ⟨_,_⟩
      grind)),?_⟩
    rintro a ha b hb eq
    obtain ⟨e,_,h⟩ := List.mem_flatMap.mp ha
    obtain ⟨p,_,rfl⟩ := List.mem_map.mp hb
    simp at h
    rcases h with rfl|rfl <;> cases eq
  constructor
  · simp [flagEdges,List.map_append,segments_map,List.map_map,edges,spokes,Prod.map,contractNode,
      Function.comp_def]
  · intro u v h
    simp only [flagEdges,List.mem_append,segments,List.mem_flatMap,List.mem_cons,List.not_mem_nil,
      or_false,List.mem_map,Prod.exists] at h
    rcases h with ⟨e,he,eq|eq⟩|⟨e,i,ct,eq⟩
    · cases eq; simp [flagAdj,site,contractNode,he,touches]
    · cases eq; simp [flagAdj,site,contractNode,he,touches]
    · cases eq
      obtain ⟨m,inc⟩ := contacts_mem.mp ct
      simp [flagAdj,site,contractNode,m,inc]

def readSpokes {P : Type} (es : List (Node P × Node P)) : List (Edge × P) :=
  es.filterMap fun | (.point e,.centre p) => some (e,p) | _ => none

theorem spokes_read (fs : List Face) (s : Inventory) :
    readSpokes (edges fs s) = spokes fs (retained s) := by
  simp only [readSpokes,edges,List.filterMap_append]
  have cancel {P : Type} (es : List (Edge × P)) :
      readSpokes (es.map (fun p => (.point p.1,.centre p.2)))=es := by
    induction es with
    | nil => rfl
    | cons x xs ih => simp [readSpokes] at *; exact ih
  have no {P : Type} (es : List Edge) : readSpokes (segments (P := P) es)=[] := by
    induction es with
    | nil => rfl
    | cons x xs ih => simpa [readSpokes,segments] using ih
  change readSpokes (segments (retained s)) ++ _ = _
  rw [no,List.nil_append]
  exact cancel _

end Recognition.Overlay

namespace Recognition.Overlay
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep

/-- An open midpoint has one spoke, a retained sealed midpoint has two.
This can be read off the multigraph even if the spokes end at the same hub. -/
def incidentCount {P : Type} (es : List (Node P × Node P)) (e : Edge) :=
  ((readSpokes es).map Prod.fst).count e

private theorem spoke_count {fs : List Face} (e : Edge) (K : List Edge) (nd : K.Nodup) :
    ((spokes fs K).map Prod.fst).count e =
      if e∈K then (indices fs e).length else 0 := by
  have H (as : List Edge) (h : as.Nodup) :
      ((contacts fs as).map Prod.fst).count e = if e∈as then (indices fs e).length else 0 := by
    induction as with
    | nil => simp [contacts]
    | cons g gs ih =>
      have ⟨notin,tail⟩ := List.nodup_cons.mp h
      change (((indices fs g).map (g,·) ++ contacts fs gs).map Prod.fst).count e = _
      rw [List.map_append,List.count_append,List.map_map,ih tail]
      have same : ((indices fs g).map (Prod.fst ∘ (g,·))).count e =
          if g=e then (indices fs g).length else 0 := by
        have mp (xs : List (Id fs)) :
            (xs.map (Prod.fst ∘ (g,·))).count e = if g=e then xs.length else 0 := by
          by_cases eq : g=e <;> induction xs <;> simp_all
        exact mp _
      rw [same]
      by_cases eq : g=e <;> simp_all [Ne.symm]
  simpa [spokes,List.map_map,Function.comp_def] using H K nd

theorem counted (fs : List Face) (s : Inventory) (ok : replay (fs.flatMap Face.sides)=some s)
    (e : Edge) :
    (incidentCount (edges fs s) e = 1 ↔ e∈s.pending) ∧
    (incidentCount (edges fs s) e = 2 ↔ e∈retain (live s) s) := by
  have acc := replay_accurate ok
  rw [incidentCount,spokes_read,spoke_count e (retained s) (distinct_names _),count_indices]
  have p := acc.pending e
  have sealeq := acc.sealed e
  have r : e∈retained s ↔ e∈s.pending ∨ e∈retain (live s) s := by simp [retained]
  have sub (h : e∈retain (live s) s) : e∈s.sealed := (List.mem_filter.mp h).1
  by_cases m : e∈retained s
  · simp only [m,↓reduceIte]
    constructor
    · exact p.symm
    · rcases r.mp m with a|a
      · have one := p.mp a
        grind
      · have two := sealeq.mp (sub a)
        simp [two,a]
  · simp only [m,↓reduceIte]
    grind

/-- The actual labelled prefix has a bounded multigraph minor from which
the open edges, retained sealed edges, and read-component partition can
all be recovered. The final inequality uses only sparsity of the retained
simple graph on the distinct active vertices. -/
theorem prefix_overlay (fs : List Face) (s : Inventory) (ok : replay (fs.flatMap Face.sides)=some s)
    (sparse : (retained s).length ≤ 3*(activeNames s).eraseDups.length) :
    let es := edges fs s
    let vs := vertices fs s
    let b := (activeNames s).eraseDups.length
    Nonempty (BranchModel vs es (flagAdj fs)) ∧ es.length ≤ 12*b ∧ vs.length ≤ 10*b ∧
    (∀ e, (incidentCount es e=1 ↔ e∈s.pending) ∧
      (incidentCount es e=2 ↔ e∈retain (live s) s)) ∧
    ∀ e∈s.pending, ∀ f∈s.pending, decoded (readSpokes es) e f ↔ sameBlock fs e f := by
  dsimp only
  have ⟨edgesLim,verticesLim⟩ := size fs s ok
  refine ⟨barycentric_minor fs s,by omega,by omega,counted fs s ok,?_⟩
  intro e a f b
  rw [spokes_read]
  exact blocks_correct fs s a b

#print axioms flag_edges
#print axioms prefix_overlay
end Recognition.Overlay

namespace Recognition.Overlay
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep

/-- On one separator-chosen order, every prefix has the concrete compressed
overlay and the bit-cost bound on its actual current counters. The geometric
inputs used here are the separator and sparsity of each retained graph. -/
theorem bounded_overlays (vs : List Nat) (faces : List Face) (red : List Edge)
    (distinct : vs.Nodup) (names : ∀ f∈faces, ∀ v∈corners f, v∈vs)
    (paired : ∀ e, occurrences (faces.flatMap Face.sides) e = 0 ∨
        occurrences (faces.flatMap Face.sides) e = 2)
    (redSide : ∀ f∈faces, ∀ a∈f.sides, a.red=true → a.edge∈red)
    (total : (vs.map (simpleDegree red)).sum ≤ 6*vs.length)
    (oracle : Outline.Separators vs (Outline.cofacial faces) (fun x => cost (simpleDegree red x)))
    (sparse : ∀ read todo : List Face, (read++todo).Perm faces → ∀ s, replay (read.flatMap Face.sides)=some s →
      (retained s).length ≤ 3*(activeNames s).eraseDups.length) :
    ∃ seq : List Face, seq.Perm faces ∧ ∀ read todo, seq=read++todo → ∃ s,
      replay (read.flatMap Face.sides) = some s ∧
      let active := (activeNames s).eraseDups
      let bits := (active.map (fun v => cost (s.redDegree v))).sum
      let es := edges read s
      let vs' := vertices read s
      bits*bits ≤ 220^2*vs.length ∧ active.length ≤ bits ∧
      Nonempty (BranchModel vs' es (flagAdj read)) ∧ es.length ≤ 12*active.length ∧
      vs'.length ≤ 10*active.length ∧
      (∀ e, (incidentCount es e=1 ↔ e∈s.pending) ∧ (incidentCount es e=2 ↔ e∈retain (live s) s)) ∧
      ∀ e∈s.pending, ∀ f∈s.pending, decoded (readSpokes es) e f ↔ sameBlock read e f := by
  obtain ⟨seq,perm,order⟩ := Outline.face_order vs faces red distinct names paired redSide total oracle
  refine ⟨seq,perm,?_⟩
  intro read todo cut
  obtain ⟨s,ok,bounded⟩ := order read todo cut
  refine ⟨s,ok,?_⟩
  have positive (as : List Nat) : as.length ≤ (as.map (fun v => cost (s.redDegree v))).sum := by
    induction as with
    | nil => simp
    | cons v as ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; unfold cost at *; omega
  refine ⟨bounded _ (distinct_names _) ?_, positive _,prefix_overlay read s ok (sparse _ _ (cut ▸ perm) s ok)⟩
  intro v m
  simp only [activeNames,List.mem_eraseDups,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at m
  obtain ⟨e,he,h⟩ := m
  exact ⟨e,he,by simpa [touches] using h⟩

#print axioms bounded_overlays
end Recognition.Overlay
