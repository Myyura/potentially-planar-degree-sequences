import Std

namespace DiskFullerene.Lower

/-! A simple graph on at most five labelled vertices, padded with isolated
vertices to order five. Bit j(j-1)/2+i records edge ij, i < j < 5. -/
abbrev FiveGraph := Fin 1024

def adjacent (G : FiveGraph) (x y : Nat) : Bool :=
  x != y && G.val.testBit (max x y * (max x y - 1) / 2 + min x y)

private def slots : List (Nat × Nat) :=
  [(0,1), (0,2), (1,2), (0,3), (1,3), (2,3), (0,4), (1,4), (2,4), (3,4)]

/-- Pack an arbitrary adjacency function on five labels into its ten undirected bits. -/
def encode (r : Nat → Nat → Bool) : FiveGraph :=
  let bits := BitVec.ofBoolListLE (slots.map (fun (a,b) => r a b))
  ⟨bits.toNat, by
    have e : 2 ^ slots.length = 1024 := by decide
    simpa only [List.length_map, e] using bits.isLt⟩

private theorem slots_ok : ∀ x y : Fin 5, x ≠ y →
    slots[max x.val y.val * (max x.val y.val - 1) / 2 + min x.val y.val]? =
      some (min x.val y.val, max x.val y.val) := by decide

theorem encode_adjacent (r : Nat → Nat → Bool)
    (loopless : ∀ x : Fin 5, r x.val x.val = false)
    (symm : ∀ x y : Fin 5, r x.val y.val = r y.val x.val) (x y : Fin 5) :
    adjacent (encode r) x.val y.val = r x.val y.val := by
  by_cases h : x = y
  · subst y; simp [adjacent, loopless]
  have hn : x.val ≠ y.val := fun he => h (Fin.ext he)
  simp only [adjacent, bne_iff_ne.mpr hn, Bool.true_and]
  change (BitVec.ofBoolListLE (slots.map (fun (a,b) => r a b))).getLsbD _ = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_map, slots_ok x y h]
  by_cases hxy : x.val ≤ y.val
  · simp [Nat.min_eq_left hxy, Nat.max_eq_right hxy]
  · have hyx : y.val ≤ x.val := by omega
    simp [Nat.min_eq_right hyx, Nat.max_eq_left hyx, symm y x]

private def vertices := [0, 1, 2, 3, 4]

def neighborsIn (G : FiveGraph) (vs : List Nat) (u : Nat) : List Nat :=
  vs.filter (adjacent G u)

private def quadruples : List (List Nat) :=
  [[0,1,2,3], [0,1,2,4], [0,1,3,4], [0,2,3,4], [1,2,3,4]]

/-- A K₄, or the vertex set of an induced four- or five-cycle. On four
or five vertices a 2-regular simple graph is a single cycle. -/
def hasObstruction (G : FiveGraph) : Bool :=
  quadruples.any (fun vs => vs.all (fun v => (neighborsIn G vs v).length == 3)) ||
  (vertices :: quadruples).any
    (fun vs => vs.all (fun v => (neighborsIn G vs v).length == 2))

/-- A non-isolated vertex that is a leaf, or whose two neighbors are adjacent. -/
def ear (G : FiveGraph) (v : Nat) : Bool :=
  match neighborsIn G vertices v with
  | [_] => true
  | [a,b] => adjacent G a b
  | _ => false

def candidates (G : FiveGraph) : List Nat := vertices.filter (ear G)

def hasEdge (G : FiveGraph) : Bool :=
  vertices.any (fun u => vertices.any (adjacent G u))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
/-- Finite graph lemma used for a putative end with at most five interior
vertices. No graph generator, planarity oracle or external solver is used. -/
theorem two_ears : ∀ G : FiveGraph, hasEdge G = true →
    hasObstruction G = false → 2 ≤ (candidates G).length := by
  decide +kernel

private theorem ear_degree_le_two (G : FiveGraph) (u : Nat) (hu : ear G u = true) :
    (neighborsIn G vertices u).length ≤ 2 := by
  cases h : neighborsIn G vertices u with
  | nil => simp
  | cons a l =>
    cases l with
    | nil => simp
    | cons b l =>
      cases l with
      | nil => simp
      | cons c l => simp [ear, h] at hu

/-- Local rotation data of an end for the small-core contradiction. Labels of
boundary vertices and core vertices live in separate copies of Nat. The
long-fan statement records that a run of at least three boundary neighbors
has a middle vertex with precisely one core neighbor. -/
structure EndFans (G : FiveGraph) where
  x : Nat
  y : Nat
  z : Nat
  touches : Nat → Nat → Prop  -- interior vertex, boundary vertex
  boundaryNeighbors : Nat → Nat
  minDegree : ∀ u ∈ candidates G,
    5 ≤ (neighborsIn G vertices u).length + boundaryNeighbors u
  earFan : ∀ u ∈ candidates G, 3 ≤ boundaryNeighbors u →
    ∃ b, touches u b ∧ ∀ v, touches v b → v = u
  ordinary : ∀ u b, touches u b → b ≠ x → b ≠ y →
    ∃ v, touches v b ∧ v ≠ u
  atX : touches z x
  atY : touches z y

theorem EndFans.only_marked (F : EndFans G) {u : Nat} (hu : u ∈ candidates G) : u = F.z := by
  have he := (List.mem_filter.mp hu).2
  have hedeg := ear_degree_le_two G u he
  have d := F.minDegree u hu
  obtain ⟨b,hb,uniq⟩ := F.earFan u hu (by omega)
  by_cases hx : b = F.x
  · subst b; exact (uniq _ F.atX).symm
  by_cases hy : b = F.y
  · subst b; exact (uniq _ F.atY).symm
  obtain ⟨v, hv, hd⟩ := F.ordinary u b hb hx hy
  exact False.elim (hd (uniq v hv))

/-- A nonempty small inner graph with no K₄ or induced cycle of order four or five
cannot carry the boundary incidences of an end. -/
theorem no_small_end (G : FiveGraph) (e : hasEdge G = true)
    (p : hasObstruction G = false) (F : EndFans G) : False := by
  have lo := two_ears G e p
  have nd : (candidates G).Nodup := List.Nodup.sublist List.filter_sublist (by decide : vertices.Nodup)
  have sub : candidates G ⊆ [F.z] := by
    intro u hu
    simp [F.only_marked hu]
  have hi := nd.length_le_of_subset sub
  simp at hi
  omega

/-- A leaf block with its outer cycle, the remaining vertices, and the
neighbors of one enclosed vertex. The vertex is not counted among its own
neighbors. -/
structure LeafBlock where
  rim : Nat
  buried : Nat
  enclosed : 0 < buried
  center : Fin (rim + buried)
  neighbors : List (Fin (rim + buried))
  nodup : (center :: neighbors).Nodup
  minDegree : 5 ≤ neighbors.length

theorem LeafBlock.six (B : LeafBlock) : 6 ≤ B.rim + B.buried := by
  have sub : B.center :: B.neighbors ⊆ List.finRange (B.rim + B.buried) :=
    fun x _ => List.mem_finRange x
  have hi := B.nodup.length_le_of_subset sub
  have lo := B.minDegree
  simp at hi
  omega

/-- For every non-leaf block the contribution to the global vertex count is
its order minus one. This convention also covers bridges (contribution one,
outer walk length two). -/
structure OtherBlock where
  contribution : Nat
  positive : 0 < contribution
  perimeter : Nat
  outerBound : perimeter ≤ contribution + 1

def extraOrder (bs : List OtherBlock) := (bs.map OtherBlock.contribution).sum
def extraWalk (bs : List OtherBlock) := (bs.map OtherBlock.perimeter).sum

private theorem positive_cost (bs : List OtherBlock) : bs.length ≤ extraOrder bs := by
  induction bs with
  | nil => simp [extraOrder]
  | cons b bs ih =>
    simp only [extraOrder, List.map_cons, List.sum_cons, List.length_cons] at *
    have := b.positive
    omega

/-- Numerical block incidence identities for a chordless disk. For several
blocks, choose any two leaf blocks. Every further block appears in others.
No bound on the number of further blocks or their arrangement is assumed. -/
inductive BlockAccounts (t walk : Nat) : Type where
  | single (a : LeafBlock) (order : t = a.rim + a.buried) (outer : walk = a.rim)
  | several (a b : LeafBlock) (others : List OtherBlock)
      (order : t + 1 = a.rim + a.buried + b.rim + b.buried + extraOrder others)
      (outer : walk = a.rim + b.rim + extraWalk others)

/-- The common critical block profile, retaining the actual block
decomposition rather than just its numerical totals. -/
def Tight {t walk : Nat} (B : BlockAccounts t walk) : Prop :=
  ∃ a b : LeafBlock, ∃ m : OtherBlock,
    a.rim = 5 ∧ b.rim = 5 ∧ a.buried = 1 ∧ b.buried = 1 ∧
    m.contribution = 1 ∧ m.perimeter = 2 ∧
    ∃ ho hw, B = BlockAccounts.several a b [m] ho hw

/-- Under the disk counting identities, the only possible chordless profile
at s ≤ 6 is the critical case, with two six-vertex leaves, one remaining
two-vertex block and five vertices on each outer cycle. -/
theorem chordless_critical {h s boundarySix : Nat}
    (hh : 12 ≤ h) (hs : s ≤ 6)
    (B : BlockAccounts (6+s) (h+boundarySix)) :
    h = 12 ∧ s = 6 ∧ boundarySix = 0 ∧ Tight B := by
  cases B with
  | single a ho hw => have := a.enclosed; omega
  | several a b others ho hw =>
    have ha := a.six; have hb := b.six
    have ca := a.enclosed; have cb := b.enclosed
    have len := positive_cost others
    cases others with
    | nil => simp [extraOrder, extraWalk] at ho hw; omega
    | cons m ms =>
      have pos := m.positive
      have per := m.outerBound
      cases ms with
      | nil =>
        simp [extraOrder, extraWalk] at ho hw
        refine ⟨by omega, by omega, by omega, a, b, m, by omega, by omega, by omega,
          by omega, by omega, by omega, _, _, rfl⟩
      | cons n ns =>
        simp at len
        omega

/-- In particular, a chordless disk admitting the block data cannot occur
with fewer than six hexagons. This implication does not use the wheel
analysis of the equality case. -/
theorem chordless_lower {h s boundarySix : Nat}
    (hh : 12 ≤ h) (B : BlockAccounts (6+s) (h+boundarySix)) : 6 ≤ s := by
  by_cases small : s ≤ 6
  · have eq := (chordless_critical hh small B).2.1; omega
  · omega

/-- An unattached rim vertex has three wheel neighbors and just one run of
boundary neighbors. The bridge endpoint is allowed an arbitrary degree. -/
structure WheelAtBridge where
  bridgeDegree : Nat
  runs : List Nat
  four : runs.length = 4
  noLongRun : ∀ r ∈ runs, r ≤ 2

def WheelAtBridge.degrees (W : WheelAtBridge) : List Nat :=
  5 :: W.bridgeDegree :: W.runs.map (3 + ·)

theorem WheelAtBridge.at_most_one_six (W : WheelAtBridge) : W.degrees.count 6 ≤ 1 := by
  have absent : 6 ∉ W.runs.map (3 + ·) := by
    intro h
    obtain ⟨r, hr, he⟩ := List.mem_map.mp h
    have := W.noLongRun r hr
    omega
  have h0 := List.count_eq_zero.mpr absent
  by_cases e : W.bridgeDegree = 6 <;> simp [WheelAtBridge.degrees, e, h0]

/-- The geometric step not contained in the numerical block argument is
explicit: in the tight profile the two induced blocks are wheels, with the
indicated boundary runs accounting for all remaining incident edges. -/
theorem chordless_impossible {h s boundarySix : Nat}
    (hh : 12 ≤ h) (hs : s ≤ 6) (B : BlockAccounts (6+s) (h+boundarySix))
    (wheels : Tight B → ∃ A C : WheelAtBridge,
      s = boundarySix + (A.degrees ++ C.degrees).count 6) : False := by
  obtain ⟨_, seq, boundary, tight⟩ := chordless_critical hh hs B
  obtain ⟨A, C, eq⟩ := wheels tight
  rw [List.count_append] at eq
  have := A.at_most_one_six
  have := C.at_most_one_six
  omega

/-- The two end interiors are represented by actual vertex lists in the
same t-vertex disk. In either end, a core of size at most five must yield
the graph and the local incidences checked above. This is a geometric
input, not a decision procedure for extracting them from a map. -/
structure ChordEnds (t : Nat) where
  left : List (Fin t)
  right : List (Fin t)
  disjointNodup : (left ++ right).Nodup
  smallCore : ∀ xs ∈ [left,right], xs.length ≤ 5 →
    ∃ G : FiveGraph, hasEdge G = true ∧ hasObstruction G = false ∧ Nonempty (EndFans G)

theorem ChordEnds.end_size (E : ChordEnds t) (xs) (mem : xs ∈ [E.left,E.right]) :
    6 ≤ xs.length := by
  by_cases h : xs.length ≤ 5
  · obtain ⟨G, e, p, ⟨F⟩⟩ := E.smallCore xs mem h
    exact False.elim (no_small_end G e p F)
  · omega

theorem ChordEnds.count (E : ChordEnds t) :
    12 ≤ t ∧ (t = 12 → E.left.length = 6 ∧ E.right.length = 6) := by
  have l := E.end_size E.left (by simp)
  have r := E.end_size E.right (by simp)
  have sub : E.left ++ E.right ⊆ List.finRange t := fun x _ => List.mem_finRange x
  have hi := E.disjointNodup.length_le_of_subset sub
  simp at hi
  omega

/-- Lower bound for every disk supplied with either the chordless block
incidences or two chordal end incidences. No assumption directly bounds the
number of hexagons. -/
theorem six_of_disk_accounts {h s : Nat} (hh : 12 ≤ h)
    (classification : (∃ boundarySix, Nonempty (BlockAccounts (6+s) (h+boundarySix))) ∨
      Nonempty (ChordEnds (6+s))) : 6 ≤ s := by
  rcases classification with hblocks | hends
  · obtain ⟨b, ⟨B⟩⟩ := hblocks
    exact chordless_lower hh B
  · obtain ⟨E⟩ := hends
    have := E.count.1; omega

end DiskFullerene.Lower
