import Std

/-! Linear codes for the tree and non-tree edges of a rooted plane map. -/
namespace PlanarDegrees.MapCode

/-- A perfect pairing on positions `0,…,n−1`. The last field forbids two
arcs with interleaved endpoints in the linear order from the root corner. -/
structure Chords (n : Nat) where
  mate : Nat → Nat
  bound : ∀ i, i<n → mate i<n
  undo : ∀ i, i<n → mate (mate i)=i
  distinct : ∀ i, i<n → mate i ≠ i
  noncrossing : ∀ i j, i<j → j<mate i → mate i<mate j → mate j<n → False

structure Stack where
  pending : List Nat := []
  pairs : List (Nat × Nat) := []
deriving DecidableEq

/-- Read a single half-edge, with position measured among non-tree half-edges. -/
def readBit (i : Nat) (opening : Bool) (s : Stack) : Option Stack :=
  if opening then some {s with pending := i :: s.pending}
  else match s.pending with
    | [] => none
    | a :: rest => some ⟨rest, (a,i) :: s.pairs⟩

def scan (bit : Nat → Bool) : Nat → Option Stack
  | 0 => some {}
  | k+1 => (scan bit k).bind (readBit k (bit k))

def decodeChords (bits : List Bool) : Option (List (Nat × Nat)) := do
  let s ← scan (fun i => bits[i]?.getD false) bits.length
  if s.pending.isEmpty then some s.pairs else none

def Chords.bit {n} (C : Chords n) (i : Nat) := decide (i<C.mate i)

def Chords.bits {n} (C : Chords n) := (List.range n).map C.bit

private structure Valid {n} (C : Chords n) (k : Nat) (s : Stack) : Prop where
  sorted : s.pending.Pairwise (· > ·)
  waiting : ∀ j, j ∈ s.pending ↔ j<k ∧ k≤C.mate j
  paired : ∀ a b, (a,b) ∈ s.pairs ↔ a<b ∧ b<k ∧ C.mate b=a

private theorem scan_correct {n} (C : Chords n) (k : Nat) (bound : k≤n) :
    ∃ s, scan C.bit k = some s ∧ Valid C k s := by
  induction k with
  | zero =>
    exact ⟨{},rfl,by constructor <;> simp⟩
  | succ k ih =>
    have hk : k<n := by omega
    obtain ⟨s,hs,hv⟩ := ih (by omega)
    have swap (j) (hj : j<n) : C.mate j = k ↔ j = C.mate k := by
      constructor
      · intro h
        simpa [C.undo j hj] using congrArg C.mate h
      · intro h; rw [h, C.undo k hk]
    by_cases opening : k<C.mate k
    · let t := {s with pending := k :: s.pending}
      refine ⟨t,by simp [scan,hs,Chords.bit,opening,readBit,t],?_⟩
      constructor
      · exact List.pairwise_cons.mpr ⟨fun j h => ((hv.waiting j).mp h).1, hv.sorted⟩
      · intro j
        change j ∈ k :: s.pending ↔ _
        rw [List.mem_cons, hv.waiting]
        by_cases hj : j = k
        · subst j; omega
        · by_cases lt : j<k
          · have hn : C.mate j ≠ k := fun h => by have := (swap j (by omega)).mp h; omega
            omega
          · omega
      · intro a b
        change (a,b) ∈ s.pairs ↔ _
        rw [hv.paired]
        by_cases hb : b=k
        · subst b; omega
        · omega
    · have closed : C.mate k < k := by have := C.distinct k hk; omega
      have hm := C.undo k hk
      have has : C.mate k ∈ s.pending := (hv.waiting _).mpr ⟨closed, by omega⟩
      cases hp : s.pending with
      | nil => simp [hp] at has
      | cons j js =>
        have hji := (hv.waiting j).mp (by simp [hp])
        have order := List.pairwise_cons.mp (hp ▸ hv.sorted)
        have htop : C.mate k ≤ j := by
          rw [hp] at has
          rcases List.mem_cons.mp has with h|h
          · omega
          · have := order.1 _ h; omega
        have hmatch : j = C.mate k := by
          by_cases eq : j=C.mate k
          · exact eq
          · have hj : k<C.mate j := by have := mt (swap j (by omega)).mp eq; omega
            exact False.elim (C.noncrossing (C.mate k) j (by omega) (by omega) (by omega)
              (C.bound j (by omega)))
        subst j
        let t : Stack := ⟨js,(C.mate k,k) :: s.pairs⟩
        refine ⟨t,by simp [scan,hs,Chords.bit,opening,readBit,hp,t],?_⟩
        constructor
        · exact order.2
        · intro u
          have hu := hv.waiting u
          rw [hp, List.mem_cons] at hu
          change u ∈ js ↔ _
          by_cases eq : u=C.mate k
          · subst u
            have absent : C.mate k ∉ js := fun h => Nat.lt_irrefl _ (order.1 _ h)
            simp [absent, C.undo k hk]
          · simp only [eq,false_or] at hu
            rw [hu]
            by_cases small : u≤k
            · have ne := mt (swap u (by omega)).mp eq
              by_cases uk : u=k
              · subst u; omega
              · omega
            · omega
        · intro a b
          change (a,b) ∈ (C.mate k,k) :: s.pairs ↔ _
          rw [List.mem_cons, hv.paired]
          simp only [Prod.mk.injEq]
          by_cases hb : b=k
          · subst b; omega
          · omega

private theorem scan_congr {g h : Nat → Bool} {k : Nat} (eqv : ∀ i, i<k → g i = h i) :
    scan g k = scan h k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [scan,scan,ih (fun i hi => eqv i (by omega)), eqv k (by omega)]

/-- The single opening/closing bit at each position determines the entire
noncrossing pairing. The decoder rejects an unmatched close or leftover opens. -/
theorem chord_round_trip {n} (C : Chords n) :
    C.bits.length = n ∧ ∃ pairs, decodeChords C.bits = some pairs ∧
      ∀ a b, (a,b) ∈ pairs ↔ a<b ∧ b<n ∧ C.mate b=a := by
  have len : C.bits.length = n := by simp [Chords.bits]
  obtain ⟨s,hs,hv⟩ := scan_correct C n (Nat.le_refl _)
  have noOpen : s.pending = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro j h
    obtain ⟨hj,hm⟩ := (hv.waiting _).mp h
    have := C.bound j hj
    omega
  have compat : scan (fun i => C.bits[i]?.getD false) n = scan C.bit n := by
    apply scan_congr
    intro i hi
    simp [Chords.bits, hi]
  exact ⟨len,s.pairs,by simp [decodeChords,len,compat,hs,noOpen],hv.paired⟩

end PlanarDegrees.MapCode

namespace PlanarDegrees.MapCode

/-- A finite alphabet of marks, represented by exactly w bits. -/
abbrev Mark (w : Nat) := {xs : List Bool // xs.length = w}

/-- An ordered forest of child excursions and non-tree half-edges in the
corners along the contour. An excursion's mark may encode both its edge
mark and the mark of the newly reached vertex. -/
inductive Contour (w : Nat) where
  | empty
  | bud (mark : Mark w) (rest : Contour w)
  | child (mark : Mark w) (inside rest : Contour w)
deriving DecidableEq

inductive Symbol (w : Nat) where
  | bud (mark : Mark w)
  | down (mark : Mark w)
  | up
deriving DecidableEq

def Contour.symbols {w} : Contour w → List (Symbol w)
  | .empty => []
  | .bud m rest => .bud m :: rest.symbols
  | .child m inner rest => .down m :: (inner.symbols ++ .up :: rest.symbols)

/-- Number of tree edges and non-tree half-edges, respectively. -/
def Contour.treeEdges {w} : Contour w → Nat
  | .empty => 0
  | .bud _ rest => rest.treeEdges
  | .child _ inner rest => 1+inner.treeEdges+rest.treeEdges

def Contour.buds {w} : Contour w → Nat
  | .empty => 0
  | .bud _ rest => rest.buds+1
  | .child _ inner rest => inner.buds+rest.buds

theorem Contour.symbol_count {w} (t : Contour w) :
    t.symbols.length = 2*t.treeEdges+t.buds := by
  induction t <;> simp_all [Contour.symbols,Contour.treeEdges,Contour.buds] <;> omega

def parse {w} : Nat → List (Symbol w) → Option (Contour w × List (Symbol w))
  | 0, _ => none
  | _+1, [] => some (.empty,[])
  | _+1, .up :: tail => some (.empty,.up :: tail)
  | k+1, .bud m :: tail => do
    let (rest,rem) ← parse k tail
    return (.bud m rest,rem)
  | k+1, .down m :: tail => do
    let (inner,.up :: rem) ← parse k tail | none
    let (rest,rem') ← parse k rem
    return (.child m inner rest,rem')

private theorem parse_correct {w} (t : Contour w) (tail : List (Symbol w))
    (delim : tail = [] ∨ ∃ rem, tail = .up :: rem) (fuel : Nat) (hf : t.symbols.length < fuel) :
    parse fuel (t.symbols ++ tail) = some (t,tail) := by
  induction t generalizing fuel tail with
  | empty =>
    cases fuel with
    | zero => omega
    | succ k => rcases delim with rfl|⟨_,rfl⟩ <;> rfl
  | bud m rest ih =>
    cases fuel with
    | zero => omega
    | succ k =>
      simp only [Contour.symbols,List.length_cons] at hf
      simp [Contour.symbols,parse,ih tail delim k (by omega)]
  | child m inner rest ih₁ ih₂ =>
    cases fuel with
    | zero => omega
    | succ k =>
      simp only [Contour.symbols,List.length_cons,List.length_append] at hf
      have first := ih₁ (.up :: (rest.symbols ++ tail)) (Or.inr ⟨_,rfl⟩) k (by omega)
      have second := ih₂ tail delim k (by omega)
      simp [Contour.symbols, List.append_assoc, parse, first, second]

/-- 00 and 01 introduce a marked bud and down-step. 10 is the up-step;
11 terminates the contour and starts the chord bit stream. -/
def block {w} : Symbol w → List Bool
  | .bud m => false :: false :: m.val
  | .down m => false :: true :: m.val
  | .up => [true,false]

def symbolBlocks {w} (xs : List (Symbol w)) := xs.flatMap block

def readSymbols (w : Nat) : Nat → List Bool → Option (List (Symbol w) × List Bool)
  | 0, _ => none
  | _+1, true :: true :: rest => some ([],rest)
  | k+1, true :: false :: rest => do
    let (xs,tail) ← readSymbols w k rest
    return (.up :: xs,tail)
  | k+1, false :: tag :: rest => do
    if h : w ≤ rest.length then
      let m : Mark w := ⟨rest.take w,by simp [Nat.min_eq_left h]⟩
      let (xs,tail) ← readSymbols w k (rest.drop w)
      return ((if tag then .down m else .bud m) :: xs,tail)
    else none
  | _+1, _ => none

private theorem block_bounds {w} (xs : List (Symbol w)) :
    xs.length ≤ (symbolBlocks xs).length ∧ (symbolBlocks xs).length ≤ (w+2)*xs.length := by
  induction xs with
  | nil => simp [symbolBlocks]
  | cons s xs ih =>
    simp only [symbolBlocks, List.flatMap_cons, List.length_append, List.length_cons]
    change _ ≤ (block s).length + (symbolBlocks xs).length ∧
      (block s).length + (symbolBlocks xs).length ≤ _
    have hh : 1 ≤ (block s).length ∧ (block s).length ≤ w+2 := by
      cases s with
      | bud m | down m => simp [block,m.property]
      | up => simp [block]
    rw [Nat.mul_add]
    omega

private theorem read_symbols_correct {w} (xs : List (Symbol w)) (tail : List Bool)
    (fuel : Nat) (hf : xs.length < fuel) :
    readSymbols w fuel (symbolBlocks xs ++ true :: true :: tail) = some (xs,tail) := by
  induction xs generalizing fuel with
  | nil =>
    cases fuel with
    | zero => omega
    | succ k => rfl
  | cons s xs ih =>
    cases fuel with
    | zero => omega
    | succ k =>
      simp only [List.length_cons] at hf
      have h := ih k (by omega)
      simp only [symbolBlocks] at *
      cases s with
      | up => simp [block, readSymbols, h]
      | bud m =>
        obtain ⟨bits,rfl⟩ := m
        simp [block,List.append_assoc,readSymbols,h]
      | down m =>
        obtain ⟨bits,rfl⟩ := m
        simp [block,List.append_assoc,readSymbols,h]

/-- The contour carries all local marks. Its buds are numbered in their
order around the spanning tree; the matching supplies the non-tree edges. -/
def encode {w} (t : Contour w) (C : Chords t.buds) :=
  symbolBlocks t.symbols ++ true :: true :: C.bits

def decode (w : Nat) (src : List Bool) : Option (Contour w × List (Nat × Nat)) := do
  let (xs,bits) ← readSymbols w (src.length+1) src
  let (t,[]) ← parse (xs.length+1) xs | none
  if bits.length ≠ t.buds then none else
    let pairs ← decodeChords bits
    return (t,pairs)

theorem map_round_trip {w} (t : Contour w) (C : Chords t.buds) :
    ∃ pairs, decode w (encode t C) = some (t,pairs) ∧
      ∀ a b, (a,b) ∈ pairs ↔ a<b ∧ b<t.buds ∧ C.mate b=a := by
  obtain ⟨len,pairs,hp,valid⟩ := chord_round_trip C
  have ps := parse_correct t [] (Or.inl rfl) (t.symbols.length+1) (by omega)
  simp only [List.append_nil] at ps
  have hl : t.symbols.length < (encode t C).length+1 := by
    have := (block_bounds t.symbols).1
    simp [encode]
    omega
  have rs := read_symbols_correct t.symbols C.bits ((encode t C).length+1) hl
  change readSymbols w _ (encode t C) = _ at rs
  exact ⟨pairs,by simp [decode,rs,ps,len,hp],valid⟩

/-- With `m` tree and non-tree edges combined, and a fixed w-bit mark
alphabet, the entire contour and pairing take at most `(2w+6)m+2` bits. -/
theorem map_bit_bound {w} (t : Contour w) (chords : Nat) (matched : t.buds = 2*chords)
    (C : Chords t.buds) :
    (encode t C).length ≤ (2*w+6)*(t.treeEdges+chords)+2 := by
  have len := (chord_round_trip C).1
  have hi := (block_bounds t.symbols).2
  simp only [encode, List.length_append, List.length_cons,len]
  rw [t.symbol_count,matched] at hi
  rw [matched]
  simp only [Nat.mul_add,Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm w 2] at hi ⊢
  omega

end PlanarDegrees.MapCode

namespace PlanarDegrees.MapCode

private theorem scan_size (bit : Nat → Bool) {k : Nat} {s : Stack}
    (h : scan bit k = some s) : s.pending.length + 2*s.pairs.length = k := by
  induction k generalizing s with
  | zero =>
    simp [scan] at h
    subst s
    rfl
  | succ k ih =>
    cases hs : scan bit k with
    | none => simp [scan,hs] at h
    | some prev =>
      have H := ih hs
      cases hb : bit k with
      | true =>
        simp [scan,hs,readBit,hb] at h
        subst s
        simp only [List.length_cons]
        omega
      | false =>
        cases hp : prev.pending with
        | nil => simp [scan,hs,readBit,hb,hp] at h
        | cons i xs =>
          simp [scan,hs,readBit,hb,hp] at h
          subst s
          rw [hp,List.length_cons] at H
          simp only [List.length_cons]
          omega

theorem decoded_length {bits : List Bool} {pairs : List (Nat × Nat)}
    (h : decodeChords bits = some pairs) : 2*pairs.length = bits.length := by
  cases hs : scan (fun i => bits[i]?.getD false) bits.length with
  | none => simp [decodeChords,hs] at h
  | some s =>
    have tall := scan_size _ hs
    cases hp : s.pending with
    | nil =>
      simp [decodeChords,hs,hp] at h
      subst pairs
      simpa [hp] using tall
    | cons i xs => simp [decodeChords,hs,hp] at h

/-- Include the mark of the root vertex, which has no incoming tree edge. -/
def encodeRoot {w} (root : Mark w) (t : Contour w) (C : Chords t.buds) :=
  root.val ++ encode t C

def decodeRoot (w : Nat) (src : List Bool) : Option (Mark w × Contour w × List (Nat × Nat)) := do
  if h : w ≤ src.length then
    let root : Mark w := ⟨src.take w, by simp [Nat.min_eq_left h]⟩
    let (t,pairs) ← decode w (src.drop w)
    return (root,t,pairs)
  else none

/-- Complete binary round trip, including the root mark and every paired
edge. The length estimate counts the graph edges of the decoded record. -/
theorem rooted_map_code {w} (root : Mark w) (t : Contour w) (C : Chords t.buds) :
    ∃ pairs, decodeRoot w (encodeRoot root t C) = some (root,t,pairs) ∧
      (∀ a b, (a,b) ∈ pairs ↔ a<b ∧ b<t.buds ∧ C.mate b=a) ∧
      (encodeRoot root t C).length ≤ (2*w+6)*(t.treeEdges+pairs.length) + w+2 := by
  obtain ⟨pairs,hd,rel⟩ := map_round_trip t C
  obtain ⟨hSize,ps,hps,_⟩ := chord_round_trip C
  have ep : ps = pairs := by
    have cr := parse_correct t [] (Or.inl rfl) (t.symbols.length+1) (by omega)
    simp only [List.append_nil] at cr
    have lb := (block_bounds t.symbols).1
    have hr := read_symbols_correct t.symbols C.bits ((encode t C).length+1)
      (by simp [encode]; omega)
    change readSymbols w _ (encode t C) = _ at hr
    simpa [decode,hr,cr,hSize,hps] using hd
  subst ps
  have even : t.buds = 2*pairs.length := hSize.symm.trans (decoded_length hps).symm
  refine ⟨pairs,?_,rel,?_⟩
  · obtain ⟨r,rfl⟩ := root
    simp [decodeRoot,encodeRoot,hd]
  · have hi := map_bit_bound t pairs.length even C
    simp [encodeRoot,root.property]
    omega

end PlanarDegrees.MapCode
