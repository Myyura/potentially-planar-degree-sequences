import Std

/-! A disk cut open at one chord gives two pieces, each with a root edge.
A piece consists of its incident region and the pieces attached on other
edges of that region. Boundary labels in each region are 0,...,b−1 in
cyclic order. Face triples are stored in increasing order. -/
namespace DiskFullerene.Dissection

abbrev Face := Nat × Nat × Nat

def consecutive (b i j : Nat) : Prop :=
  i+1 = j ∨ j+1 = i ∨ (i = 0 ∧ j+1 = b) ∨ (j = 0 ∧ i+1 = b)

def contains (f : Face) (v : Nat) : Prop :=
  v = f.1 ∨ v = f.2.1 ∨ v = f.2.2

/-- Local data used by the argument. Any chordless triangulated region
can be supplied with these labels. Only the indicated incidence properties
are needed here; we do not use them to define a topological disk. -/
structure Region where
  boundary : Nat
  interior : Nat
  faces : List Face
  polygon : 3 ≤ boundary
  filled : faces ≠ []
  simple : faces.Nodup
  bounds : ∀ f ∈ faces, f.1 < f.2.1 ∧ f.2.1 < f.2.2 ∧ f.2.2 < boundary + interior
  chordless : ∀ f ∈ faces, ∀ u v, contains f u → contains f v →
    u < v → v < boundary → consecutive boundary u v

theorem triangle_of_empty (r : Region) (hi : r.interior = 0) :
    r.boundary = 3 ∧ r.faces = [(0,1,2)] := by
  have perface : ∀ f ∈ r.faces, r.boundary = 3 ∧ f = (0,1,2) := by
    rintro ⟨a,b,c⟩ hf
    obtain ⟨hab,hbc,ht⟩ := r.bounds _ hf
    change a < b at hab
    change b < c at hbc
    change c < r.boundary + r.interior at ht
    simp only [hi, Nat.add_zero] at ht
    have h₁ := r.chordless _ hf a b (Or.inl rfl) (Or.inr (Or.inl rfl)) hab (by omega)
    have h₂ := r.chordless _ hf b c (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hbc ht
    have h₃ := r.chordless _ hf a c (Or.inl rfl) (Or.inr (Or.inr rfl)) (by omega) ht
    simp only [consecutive] at h₁ h₂ h₃
    obtain ⟨ha,hb,hc,hd⟩ : a = 0 ∧ b = 1 ∧ c = 2 ∧ r.boundary = 3 := by omega
    simp [ha,hb,hc,hd]
  have simple := r.simple
  cases he : r.faces with
  | nil => exact (r.filled he).elim
  | cons f fs =>
    have ⟨hb,hf⟩ := perface f (by simp [he])
    subst f
    cases fs with
    | nil => exact ⟨hb,rfl⟩
    | cons g gs =>
      have hg := (perface g (by simp [he])).2
      subst g
      simp [he] at simple

/-- A witnessed interior star of an end. Every indicated neighbor is
distinct and strictly interior. Adjacency is witnessed by an actual face. -/
structure EndStar (r : Region) where
  center : Fin r.interior
  neighbors : List (Fin r.interior)
  distinct : (center :: neighbors).Nodup
  degree : 5 ≤ neighbors.length
  incident : ∀ v ∈ neighbors, ∃ f ∈ r.faces,
    contains f (r.boundary + center.val) ∧ contains f (r.boundary + v.val)

theorem six_of_star {r : Region} (star : EndStar r) : 6 ≤ r.interior := by
  have sub : star.center :: star.neighbors ⊆ List.finRange r.interior :=
    fun a _ => List.mem_finRange a
  have h := star.distinct.length_le_of_subset sub
  have hg := star.degree
  simp at h; omega

/- A child slot records the index of its glued edge in the parent region.
Slot 0 is reserved for the parent edge. -/
mutual
inductive Piece
  | node (r : Region) (children : Branches)
inductive Branches
  | nil
  | cons (slot : Nat) (child : Piece) (tail : Branches)
end

mutual
def mass : Piece → Nat | .node r bs => r.interior + branchMass bs
def branchMass : Branches → Nat
  | .nil => 0
  | .cons _ child tail => mass child + branchMass tail
end

mutual
def support : Piece → Prop
  | .node r .nil => Nonempty (EndStar r)
  | .node _ (.cons _ p ps) => support p ∧ branchSupport ps
def branchSupport : Branches → Prop
  | .nil => True
  | .cons _ p ps => support p ∧ branchSupport ps
end

def slots : Branches → List Nat
  | .nil => []
  | .cons slot _ tail => slot :: slots tail

mutual
def proper : Piece → Prop
  | .node r bs => (slots bs).Nodup ∧ (∀ i ∈ slots bs, 0 < i ∧ i < r.boundary) ∧ properBranches bs
def properBranches : Branches → Prop
  | .nil => True
  | .cons _ p ps => proper p ∧ properBranches ps
end

/-- Every finite piece has an end. Induction follows any first child
until it reaches a region without children. -/
theorem mass_six (p : Piece) (s : support p) : 6 ≤ mass p := by
  match p with
  | .node r .nil =>
    obtain ⟨star⟩ := s
    simpa [mass, branchMass] using six_of_star star
  | .node r (.cons _ p ps) =>
    have h := mass_six p s.1
    simp only [mass,branchMass]
    omega

/-- A concrete serial decomposition: the last region has six interior
vertices; every earlier region has the single triangle (0,1,2) and no
interior vertices. The tree is not assumed to be a path. -/
inductive ToEnd : Piece → Prop
  | stop (r : Region) : r.interior = 6 → ToEnd (.node r .nil)
  | across (r : Region) (slot : Nat) {p : Piece} :
    r.interior = 0 → r.boundary = 3 → r.faces = [(0,1,2)] →
    ToEnd p → ToEnd (.node r (.cons slot p .nil))

theorem path_of_six (p : Piece) (s : support p) (bound : mass p ≤ 6) : ToEnd p := by
  match p with
  | .node r .nil =>
    obtain ⟨star⟩ := s
    have h := six_of_star star
    simp [mass,branchMass] at bound
    exact .stop r (by omega)
  | .node r (.cons slot p .nil) =>
    have lo := mass_six p s.1
    simp [mass,branchMass] at bound
    have zero : r.interior = 0 := by omega
    obtain ⟨hb,hf⟩ := triangle_of_empty r zero
    exact .across r slot zero hb hf (path_of_six p s.1 (by omega))
  | .node r (.cons slot p (.cons slot' q qs)) =>
    have hp := mass_six p s.1
    have hq := mass_six q s.2.1
    simp only [mass,branchMass] at bound
    omega

/-- Open at any one boundary chord. Each side contributes at least six
interior vertices. At equality both sides are literal chains of triangles
ending in a six-interior-vertex end. -/
theorem cut_extremal (p q : Piece) (sp : support p) (sq : support q) {s : Nat}
    (count : mass p + mass q = 6 + s) :
    6 ≤ s ∧ (s = 6 → ToEnd p ∧ ToEnd q) := by
  have hp := mass_six p sp
  have hq := mass_six q sq
  refine ⟨by omega, ?_⟩
  intro eq
  exact ⟨path_of_six p sp (by omega), path_of_six q sq (by omega)⟩

end DiskFullerene.Dissection

namespace DiskFullerene.Dissection

mutual
def arcLength : Piece → Nat
  | .node r bs => (r.boundary-1-(slots bs).length) + branchArcs bs
def branchArcs : Branches → Nat
  | .nil => 0
  | .cons _ p ps => arcLength p + branchArcs ps
end

mutual
def regions : Piece → Nat
  | .node _ bs => 1 + branchCount bs
def branchCount : Branches → Nat
  | .nil => 0
  | .cons _ p ps => regions p + branchCount ps
end

mutual
def hexEnds : Piece → Prop
  | .node r .nil => r.boundary = 6
  | .node _ (.cons _ p ps) => hexEnds p ∧ hexBranches ps
def hexBranches : Branches → Prop
  | .nil => True
  | .cons _ p ps => hexEnds p ∧ hexBranches ps
end

private theorem path_arc {p : Piece} (h : ToEnd p) (hh : hexEnds p) :
    arcLength p = regions p + 4 := by
  induction h with
  | stop r _ =>
    change r.boundary = 6 at hh
    simp [arcLength,slots,branchArcs,regions,branchCount,hh]
  | across r slot _ hb _ _ ih =>
    have h := ih hh.1
    simp [arcLength,branchArcs,regions,branchCount,slots,hb]; omega

/-- Traversing each boundary arc replaces a glued edge by the free arc of
the adjacent piece. For two six-sided ends at equality, subtracting the
two end regions leaves exactly h−10 strip triangles. -/
theorem strip_triangle_count (p q : Piece) (sp : support p) (sq : support q)
    (budget : mass p + mass q = 12) (hp : hexEnds p) (hq : hexEnds q)
    (h : Nat) (boundary : arcLength p + arcLength q = h) :
    regions p + regions q - 2 = h - 10 := by
  obtain ⟨a,b⟩ := (cut_extremal p q sp sq (s:=6) budget).2 rfl
  have ha := path_arc a hp
  have hb := path_arc b hq
  omega

/-- Chords in cyclically ordered labels, with the lesser endpoint first.
A polygon produced during cutting may omit any of the original vertices:
its boundary order is the induced cyclic order on the surviving labels. -/
structure Chord where
  l : Nat
  r : Nat
  deriving DecidableEq, Repr

def diagonal (S : Nat → Prop) (c : Chord) : Prop :=
  c.l < c.r ∧ S c.l ∧ S c.r ∧
  (∃ z, S z ∧ c.l < z ∧ z < c.r) ∧ (∃ z, S z ∧ (z < c.l ∨ c.r < z))

def within (a b : Chord) : Prop := a.l ≤ b.l ∧ b.r ≤ a.r
instance (a b : Chord) : Decidable (within a b) := by unfold within; infer_instance

/-- Disjoint relative interiors, nesting, or endpoint contact. The
alternating-endpoints case is excluded. -/
def noncrossing (a b : Chord) : Prop :=
  a.r ≤ b.l ∨ b.r ≤ a.l ∨ within a b ∨ within b a

def innerSide (S : Nat → Prop) (c : Chord) (v : Nat) := S v ∧ c.l ≤ v ∧ v ≤ c.r

def outerSide (S : Nat → Prop) (c : Chord) (v : Nat) := S v ∧ (v ≤ c.l ∨ c.r ≤ v)

private theorem endpoints_differ {a b : Chord} (hne : a ≠ b) : a.l ≠ b.l ∨ a.r ≠ b.r := by
  cases a; cases b; simp_all; omega

theorem diagonal_inside {S : Nat → Prop} {a b : Chord}
    (ha : diagonal S a) (hb : diagonal S b) (hn : a ≠ b) (inside : within a b) :
    diagonal (innerSide S a) b := by
  obtain ⟨aa,al,ar,_,_⟩ := ha
  obtain ⟨bb,bl,br,⟨u,hu,ub,bu⟩,_⟩ := hb
  obtain ⟨left,right⟩ := inside
  have hne := endpoints_differ hn
  refine ⟨bb,⟨bl,by omega,by omega⟩,⟨br,by omega,by omega⟩,
    ⟨u,⟨hu,by omega,by omega⟩,ub,bu⟩,?_⟩
  by_cases h : a.l < b.l
  · exact ⟨a.l,⟨al,by omega,by omega⟩,Or.inl h⟩
  · exact ⟨a.r,⟨ar,by omega,by omega⟩,Or.inr (by omega)⟩

theorem diagonal_outside {S : Nat → Prop} {a b : Chord}
    (ha : diagonal S a) (hb : diagonal S b) (hn : a ≠ b) (cross : noncrossing a b)
    (out : ¬within a b) : diagonal (outerSide S a) b := by
  obtain ⟨aa,al,ar,_,_⟩ := ha
  obtain ⟨bb,bl,br,⟨u,hu,ub,bu⟩,⟨v,hv,vb⟩⟩ := hb
  have hne := endpoints_differ hn
  simp only [noncrossing, within] at cross out
  refine ⟨bb,⟨bl,by omega⟩,⟨br,by omega⟩,?_,?_⟩
  · by_cases h : u ≤ a.l ∨ a.r ≤ u
    · exact ⟨u,⟨hu,h⟩,ub,bu⟩
    · by_cases j : b.l < a.l
      · exact ⟨a.l,⟨al,Or.inl (Nat.le_refl _)⟩,j,by omega⟩
      · exact ⟨a.r,⟨ar,Or.inr (Nat.le_refl _)⟩,by omega,by omega⟩
  · by_cases h : v ≤ a.l ∨ a.r ≤ v
    · exact ⟨v,⟨hv,h⟩,vb⟩
    · by_cases j : a.l < b.l
      · exact ⟨a.l,⟨al,Or.inl (Nat.le_refl _)⟩,Or.inl j⟩
      · exact ⟨a.r,⟨ar,Or.inr (Nat.le_refl _)⟩,Or.inr (by omega)⟩

/-- Indexed cut history. Every actual cut must be a diagonal in the
*current* polygon. Its two children carry precisely the remaining assigned
chords. The list may be supplied in any order. -/
inductive Cuts : (Nat → Prop) → List Chord → Type where
  | stop (S) : Cuts S []
  | split {S c cs} : diagonal S c →
    Cuts (innerSide S c) (cs.filter (fun d => decide (within c d))) →
    Cuts (outerSide S c) (cs.filter (fun d => !(decide (within c d)))) →
    Cuts S (c::cs)

def cutAll (S : Nat → Prop) (cs : List Chord)
    (good : ∀ c ∈ cs, diagonal S c)
    (pair : cs.Pairwise (fun a b => a ≠ b ∧ noncrossing a b)) : Cuts S cs := by
  match cs with
  | [] => exact .stop S
  | c :: cs =>
    obtain ⟨hc,ht⟩ := List.pairwise_cons.mp pair
    have cdiag := good c (by simp)
    refine .split cdiag (cutAll _ _ ?_ ?_) (cutAll _ _ ?_ ?_)
    · intro b hb
      obtain ⟨hmem,hIn⟩ := List.mem_filter.mp hb
      exact diagonal_inside cdiag (good b (by simp [hmem])) (hc b hmem).1 (by simpa using hIn)
    · exact ht.filter _
    · intro b hb
      obtain ⟨hmem,hOut⟩ := List.mem_filter.mp hb
      exact diagonal_outside cdiag (good b (by simp [hmem])) (hc b hmem).1 (hc b hmem).2
        (by simpa using hOut)
    · exact ht.filter _
termination_by cs.length
decreasing_by all_goals have := List.length_filter_le (l:=cs) (p:=fun d => decide (within c d)); have := List.length_filter_le (l:=cs) (p:=fun d => !(decide (within c d))); simp; omega

def cellCount {S cs} : Cuts S cs → Nat
  | .stop _ => 1
  | .split _ left right => cellCount left + cellCount right

private theorem lengths {α : Type} (p : α → Bool) (as : List α) :
    (as.filter p).length + (as.filter (fun a => !(p a))).length = as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => cases e : p a <;> simp [e] <;> omega

theorem cut_cell_count {S cs} (cuts : Cuts S cs) : cellCount cuts = cs.length+1 := by
  induction cuts with
  | stop => rfl
  | @split S c cs _ _ _ ih jh =>
    simp only [cellCount, ih, jh, List.length_cons]
    have := lengths (fun d => decide (within c d)) cs
    omega

end DiskFullerene.Dissection
