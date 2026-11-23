import Std

/-! The outer annulus of a six-interior-vertex end, once the core is a
pentagonal wheel and the five rim fans each traverse one or two outer
edges (Lemma 5). We keep *all* 32 subdivision patterns, all choices of
a marked edge, and its two possible positions in a split fan. -/
namespace DiskFullerene.CapRing

abbrev Index := Fin 5
abbrev Pattern := Fin 32

def splitAt (p : Pattern) (i : Index) : Bool := p.val.testBit i.val

def next (i : Index) : Index := ⟨(i.val+1)%5, Nat.mod_lt _ (by decide)⟩

inductive BVertex
  | corner (i : Index) -- meeting point of the fans at i-1 and i
  | midpoint (i : Index) -- present only in a split fan
  deriving DecidableEq, Repr

/-- The first edge in fan i always exists. Its second edge exists
exactly when i is split. -/
def first (i : Index) (second : Bool) : BVertex :=
  if second then .midpoint i else .corner i

def last (p : Pattern) (i : Index) (second : Bool) : BVertex :=
  if splitAt p i && !second then .midpoint i else .corner (next i)

/-- Every corner sees two rim vertices and two other boundary vertices.
A subdivision vertex sees just one rim vertex and two boundary vertices. -/
def diskDegree : BVertex → Nat
  | .corner _ => 4
  | .midpoint _ => 3

def present (p : Pattern) : BVertex → Bool
  | .corner _ => true
  | .midpoint i => splitAt p i

/-- The punctured triangle on the other side must supply at least two
neighbors to at least one endpoint. With global degree at most six,
and two common separating-triangle neighbors at either endpoint, this
forces a load of at most two at one of the marked endpoints. -/
def Compatible (p : Pattern) (i : Index) (second : Bool) : Prop :=
  (second = true → splitAt p i = true) ∧
  (∀ j : Index, present p (.midpoint j) = true →
    .midpoint j ≠ first i second → .midpoint j ≠ last p i second →
    5 ≤ 1 + diskDegree (.midpoint j)) ∧
  (diskDegree (first i second) - 1 ≤ 2 ∨ diskDegree (last p i second) - 1 ≤ 2)

instance (p : Pattern) (i : Index) (s : Bool) : Decidable (Compatible p i s) := by
  unfold Compatible; infer_instance

/-- Rotating the canonical split puts it at i, and reflecting about the
middle of that fan interchanges its two edges. Thus i and second are
exactly the dihedral choices in the normal form. -/
def singletonPattern (i : Index) : Pattern := ⟨2^i.val % 32, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem classify : ∀ (p : Pattern) (i : Index) (second : Bool),
    Compatible p i second ↔ p = singletonPattern i := by decide +kernel

/-- Both orientations really give the claimed endpoint loads, computed on
the rim fans. The contribution from the other side is not included here. -/
theorem seam_loads : ∀ (i : Index) (s : Bool),
    (diskDegree (first i s) - 1, diskDegree (last (singletonPattern i) i s) - 1) =
      if s then (2,3) else (3,2) := by decide +kernel

/-- Actual unoriented triangles of the wheel and its five exterior fans.
Vertex 0 is the center; the next three blocks of five are rim vertices,
corners and optional subdivision vertices. Inactive labels are isolated. -/
abbrev Label := Fin 16
abbrev Triangle := Nat × Nat × Nat

def rim (i : Index) := 1+i.val
def corner (i : Index) := 6+i.val
def midpoint (i : Index) := 11+i.val

def faces (p : Pattern) : List Triangle :=
  (List.finRange 5).flatMap fun i =>
    [(0, rim i, rim (next i)), (rim i, rim (next i), corner (next i))] ++
      (if splitAt p i then
         [(rim i, corner i, midpoint i), (rim i, midpoint i, corner (next i))]
       else [(rim i, corner i, corner (next i))])

def includesVertex (t : Triangle) (u : Nat) :=
  u == t.1 || u == t.2.1 || u == t.2.2

def adjacent (p : Pattern) (u v : Nat) : Bool :=
  u != v && (faces p).any (fun t => includesVertex t u && includesVertex t v)

def degree (p : Pattern) (u : Nat) :=
  (List.range 16).countP (adjacent p u)

theorem corner_degree : ∀ p i, degree p (corner i) = diskDegree (.corner i) := by
  set_option maxRecDepth 8192 in
  set_option maxHeartbeats 0 in
  decide +kernel

theorem midpoint_degree : ∀ p i, splitAt p i = true →
    degree p (midpoint i) = diskDegree (.midpoint i) := by
  set_option maxRecDepth 8192 in
  set_option maxHeartbeats 0 in
  decide +kernel

/-- The label permutation taking the split in fan 0 to fan i. As the
corners lie *between* two rim fans, their reflection has a one-step shift. -/
def relabel (i : Index) (reflect : Bool) (v : Label) : Label :=
  let rotate (j : Nat) := (i.val+j)%5
  let sendRim (j : Nat) := rotate (if reflect then 5-j else j)
  let sendCorner (j : Nat) := rotate (if reflect then 6-j else j)
  ⟨(if v.val = 0 then 0 else if v.val < 6 then 1+sendRim (v.val-1)
        else if v.val < 11 then 6+sendCorner (v.val-6)
        else 11+sendRim (v.val-11)) % 16, Nat.mod_lt _ (by decide)⟩

def boundaryLabel : BVertex → Nat
  | .corner i => corner i
  | .midpoint i => midpoint i

def marked (p : Pattern) (i : Index) (s : Bool) (v : Label) : Bool :=
  v.val == boundaryLabel (first i s) || v.val == boundaryLabel (last p i s)

/-- Graph isomorphism, respecting the marked edge as an unordered pair.
The unused subdivision labels are also carried bijectively to unused ones. -/
def PreservesMarkedDisk (p : Pattern) (i : Index) (s : Bool) : Prop :=
  (∀ u v, relabel i s u = relabel i s v → u = v) ∧
  (∀ v, ∃ u, relabel i s u = v) ∧
  (∀ u v, adjacent (singletonPattern 0) u.val v.val =
    adjacent p (relabel i s u).val (relabel i s v).val) ∧
  (∀ v, marked (singletonPattern 0) 0 false v = marked p i s (relabel i s v))

instance (p : Pattern) (i : Index) (s : Bool) : Decidable (PreservesMarkedDisk p i s) := by
  unfold PreservesMarkedDisk; infer_instance

private theorem rotation_reflection : ∀ i s, PreservesMarkedDisk (singletonPattern i) i s := by
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 0 in
  decide +kernel

theorem marked_ring_unique {p : Pattern} {i : Index} {s : Bool} (h : Compatible p i s) :
    PreservesMarkedDisk p i s := by
  rw [(classify p i s).mp h]
  exact rotation_reflection i s

/-- In a link graph of maximum degree two, the vertices of a triangle
have no neighbors outside it. With a connected link this leaves exactly
three neighbors of the original vertex. -/
inductive Walk {V : Type} (E : V → V → Prop) : V → V → Prop where
  | nil (a) : Walk E a a
  | snoc {a b c} : Walk E a b → E b c → Walk E a c

theorem triangle_link {V : Type} (E : V → V → Prop) {x y z : V}
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (symm : ∀ a b, E a b → E b a)
    (edges : E x y ∧ E y z ∧ E z x)
    (atMostTwo : ∀ a b c d, E a b → E a c → E a d → b = c ∨ b = d ∨ c = d)
    {u : V} (hu : Walk E x u) : u = x ∨ u = y ∨ u = z := by
  obtain ⟨exy,eyz,ezx⟩ := edges
  induction hu with
  | nil => exact Or.inl rfl
  | @snoc b c _ e ih =>
    rcases ih with rfl | rfl | rfl
    · rcases atMostTwo _ _ _ _ exy (symm _ _ ezx) e with h|h|h
      · exact (hyz h).elim
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h.symm)
    · rcases atMostTwo _ _ _ _ eyz (symm _ _ exy) e with h|h|h
      · exact (hzx h).elim
      · exact Or.inr (Or.inr h.symm)
      · exact Or.inl h.symm
    · rcases atMostTwo _ _ _ _ ezx (symm _ _ eyz) e with h|h|h
      · exact (hxy h).elim
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h.symm)

/-- In the complementary disk at the separating triangle x,y,w, call
the third vertices on xy, wx, yw respectively t, u, v. If neither x
nor y had two exterior neighbors, u and v would both equal t. The
three resulting corners would close the link of t, contradicting its
fourth neighbor. These hypotheses describe just the indicated stars;
they still have to be extracted from a general sphere triangulation. -/
theorem exterior_needs_two {V : Type} [DecidableEq V]
    (outsideNeighbor linkNeighbor : V → V → Prop) (inLink : V → V → V → Prop)
    {x y w t u v : V} (hxy : x ≠ y) (hyw : y ≠ w) (hwx : w ≠ x)
    (hxt : outsideNeighbor x t) (hyt : outsideNeighbor y t)
    (hxu : outsideNeighbor x u) (hyv : outsideNeighbor y v)
    (ht : inLink t x y) (hu : inLink u w x) (hv : inLink v y w)
    (linkSymm : ∀ a b, inLink t a b → inLink t b a)
    (linkDeg : ∀ a b c d, inLink t a b → inLink t a c → inLink t a d →
      b = c ∨ b = d ∨ c = d)
    (linkConn : ∀ a, linkNeighbor t a → Walk (inLink t) x a)
    (fourth : ∃ a, linkNeighbor t a ∧ a ≠ x ∧ a ≠ y ∧ a ≠ w) :
    (∃ a b, outsideNeighbor x a ∧ outsideNeighbor x b ∧ a ≠ b) ∨
      (∃ a b, outsideNeighbor y a ∧ outsideNeighbor y b ∧ a ≠ b) := by
  by_cases hu' : u = t
  · by_cases hv' : v = t
    · subst u; subst v
      obtain ⟨a,ha,hax,hay,haw⟩ := fourth
      obtain h|h|h := triangle_link (inLink t) hxy hyw hwx linkSymm
        ⟨ht,hv,hu⟩ linkDeg (linkConn a ha)
      · exact (hax h).elim
      · exact (hay h).elim
      · exact (haw h).elim
    · exact Or.inr ⟨v,t,hyv,hyt,hv'⟩
  · exact Or.inl ⟨u,t,hxu,hxt,hu'⟩

end DiskFullerene.CapRing
