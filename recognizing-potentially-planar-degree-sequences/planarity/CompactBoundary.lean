import MapCode
import SparseOverlay
import OverlayCoverage

/-! The two explicitly delimited words of the manuscript, followed by two-bit
vertex and edge roles and one self-delimiting counter per original vertex. -/
namespace Recognition.CompactBoundary
open PlanarDegrees.MapCode PlanarDegrees.Frontier

abbrev Tag := Bool × Bool
def original : Tag := (false,false)

def lengthTag (n : Nat) := List.replicate n true ++ [false]

def readPrefix : List Bool → Option (Nat × List Bool)
  | [] => none
  | false::bs => some (0,bs)
  | true::bs => (readPrefix bs).map fun (n,rest) => (n+1,rest)

theorem read_prefix (n : Nat) (xs : List Bool) : readPrefix (lengthTag n ++ xs)=some (n,xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [lengthTag,List.replicate_succ,readPrefix] using ih

def field (n : Nat) (bits : List Bool) := lengthTag n ++ bits

def readField (w : Nat) (xs : List Bool) : Option (List Bool × List Bool) := do
  let (n,rest) ← readPrefix xs
  if w*n≤rest.length then return (rest.take (w*n),rest.drop (w*n)) else none

theorem read_field (w n : Nat) (xs rest : List Bool) (eq : xs.length=w*n) :
    readField w (field n xs ++ rest)=some (xs,rest) := by
  simp [field,List.append_assoc,readField,read_prefix,←eq]

def tagBits (ts : List Tag) := ts.flatMap fun t => [t.1,t.2]

def readTags : Nat → List Bool → Option (List Tag × List Bool)
  | 0,bs => some ([],bs)
  | n+1,p::q::bs => (readTags n bs).map fun (ts,tail) => ((p,q)::ts,tail)
  | _+1,_ => none

theorem read_tags (ts : List Tag) (rest : List Bool) :
    readTags ts.length (tagBits ts ++ rest)=some (ts,rest) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simpa [tagBits,readTags] using congrArg (Option.map (fun (v : List Tag × List Bool) => (t::v.1,v.2))) ih

private theorem tags_width (ts : List Tag) : (tagBits ts).length=2*ts.length := by
  induction ts with | nil => rfl | cons t ts ih => simp_all [tagBits]; omega

def digits : Nat → Nat → List Bool
  | 0,_ => []
  | k+1,p => decide (p%2=1) :: digits k (p/2)

def readDigits : List Bool → Nat
  | [] => 0
  | b::bs => b.toNat+2*readDigits bs

private theorem digit_len (k n : Nat) : (digits k n).length=k := by
  induction k generalizing n <;> simp_all [digits]

private theorem digits_ok (k n : Nat) (h : n<2^k) : readDigits (digits k n)=n := by
  induction k generalizing n with
  | zero => simp [digits,readDigits] at *; omega
  | succ k ih =>
    rw [pow_succ] at h
    simp only [digits,readDigits,ih (n/2) (by omega)]
    by_cases one : n%2=1 <;> simp [one] <;> omega

def counter (p : Nat) := field (cost p) (digits (cost p) (p+1))

def readCounter (src : List Bool) : Option (Nat × List Bool) := do
  let (ds,tail) ← readField 1 src
  let x := readDigits ds
  if 0<x ∧ ds.length=cost (x-1) then return (x-1,tail) else none

theorem read_counter (p : Nat) (rest : List Bool) :
    readCounter (counter p ++ rest)=some (p,rest) := by
  have cap := (cost_brackets p).2
  simp [readCounter,counter,read_field 1 (cost p) (digits (cost p) (p+1)) rest (by simp [digit_len]),
    digits_ok _ _ (show p+1<2^cost p by omega),digit_len]

def counts (ps : List Nat) := ps.flatMap counter

def readCounts : Nat → List Bool → Option (List Nat × List Bool)
  | 0,bs => some ([],bs)
  | n+1,bs => do
    let (p,tail) ← readCounter bs
    let (ps,rest) ← readCounts n tail
    return (p::ps,rest)

theorem read_counts (ps : List Nat) (rest : List Bool) :
    readCounts ps.length (counts ps ++ rest)=some (ps,rest) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change (do let (x,s) ← readCounter ((counter p ++ counts ps) ++ rest)
               let (xs,t) ← readCounts ps.length s
               return (x::xs,t))=_
    rw [List.append_assoc,read_counter]
    simp [ih]

theorem counter_width (ps : List Nat) : (counts ps).length ≤ 3*(ps.map cost).sum := by
  induction ps with
  | nil => simp [counts]
  | cons p ps ih =>
    have costPos : 0<cost p := by simp [cost]
    change ((counter p)++counts ps).length≤_
    simp only [counter,field,lengthTag,List.length_append,List.length_replicate,List.length_cons,
      List.length_nil,digit_len,List.map_cons,List.sum_cons]
    omega

structure Drawing where
  tree : Contour 0
  pairs : List (Nat × Nat)
  vertexTags : List Tag
  edgeTags : List Tag
  redDegrees : List Nat

/-- The length prefixes measure symbols; vertex and edge field counts are
obtained from the decoded tree and its chords, and the vertex tags give the
number of counter fields. -/
def decode : List Bool → Option (Option Drawing)
  | [false] => some none
  | true::bs => do
    let (word,more) ← readField 2 bs
    let (arcs,marks) ← readField 1 more
    let (t,ps) ← PlanarDegrees.MapCode.decode 0 (word++true::true::arcs)
    let (vs,remain) ← readTags (t.treeEdges+1) marks
    let (es,tail) ← readTags (t.treeEdges+ps.length) remain
    let (ds,rest) ← readCounts (vs.count original) tail
    if rest.isEmpty then return some ⟨t,ps,vs,es,ds⟩ else none
  | _ => none

def fixedFields (t : Contour 0) (C : Chords t.buds) (vs es : List Tag) :=
  true::(field t.symbols.length (symbolBlocks t.symbols) ++
    (field C.bits.length C.bits ++ (tagBits vs ++ tagBits es)))

def encode (t : Contour 0) (C : Chords t.buds) (vs es : List Tag) (ps : List Nat) :=
  fixedFields t C vs es ++ counts ps

private theorem blocks_width (xs : List (Symbol 0)) : (symbolBlocks xs).length=2*xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have w : (block x).length=2 := by
      cases x with
      | up => rfl
      | bud m | down m => simp only [block,List.length_cons,m.property]
    change (block x++symbolBlocks xs).length=_
    simp [w,ih]; omega

private theorem parsed_count {bs : List Bool} {t : Contour 0} {ps}
    (h : PlanarDegrees.MapCode.decode 0 bs=some (t,ps)) : 2*ps.length=t.buds := by
  unfold PlanarDegrees.MapCode.decode at h
  obtain ⟨⟨xs,bits⟩,_,next⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨tree,rest⟩,_,ok⟩ := Option.bind_eq_some_iff.mp next
  cases rest with
  | cons _ _ => contradiction
  | nil =>
    by_cases eq : bits.length=tree.buds
    · simp only [eq,ne_eq,not_true_eq_false,ite_false] at ok
      obtain ⟨pairs,rd,last⟩ := Option.bind_eq_some_iff.mp ok
      cases (Option.some.inj last)
      exact (decoded_length rd).trans eq
    · simp [eq] at ok

/-- The number of chords is even in endpoints, with exactly the decoded
pairs as non-tree edges. The complete code recovers the ordered tree,
the unordered chord endpoints, every mark, and every active degree. -/
theorem round_trip (t : Contour 0) (C : Chords t.buds)
    (vs es : List Tag) (ds : List Nat) (vcount : vs.length=t.treeEdges+1)
    (ecount : es.length=t.treeEdges+t.buds/2) (dcount : ds.length=vs.count original) :
    ∃ ps, decode (encode t C vs es ds)=some (some ⟨t,ps,vs,es,ds⟩) ∧
      2*ps.length=t.buds ∧ ∀ a b,(a,b)∈ps ↔ a<b ∧ b<t.buds ∧ C.mate b=a := by
  obtain ⟨ps,ok,rel⟩ := map_round_trip t C
  have size := parsed_count ok
  refine ⟨ps,?_,size,rel⟩
  have e : es.length=t.treeEdges+ps.length := by omega
  have h := read_field 2 t.symbols.length (symbolBlocks t.symbols)
      (field C.bits.length C.bits ++ (tagBits vs ++ (tagBits es ++ counts ds))) (blocks_width _)
  have k := read_field 1 C.bits.length C.bits (tagBits vs ++ (tagBits es ++ counts ds)) (by simp)
  have o : PlanarDegrees.MapCode.decode 0 (symbolBlocks t.symbols++true::true::C.bits)=some (t,ps) := ok
  have rc : readCounts ds.length (counts ds)=some (ds,[]) := by simpa using read_counts ds []
  simp [encode,fixedFields,List.append_assoc,decode,h,k,o,←vcount,←e,←dcount,read_tags,rc]

/-- The unmarked empty drawing uses a single bit. -/
theorem empty_round_trip : decode [false]=some none := rfl

theorem fixed_width (t : Contour 0) (C : Chords t.buds) (vs es : List Tag)
    (hv : vs.length=t.treeEdges+1) (he : es.length=t.treeEdges+t.buds/2) :
    (fixedFields t C vs es).length≤14*es.length+5 := by
  obtain ⟨lb,p,rd,_⟩ := chord_round_trip C
  have even := (decoded_length rd).trans lb
  simp only [fixedFields,field,lengthTag,List.length_cons,List.length_append,List.length_replicate,
    List.length_nil,blocks_width,t.symbol_count,lb,tags_width]; omega

/-- Euler sparsity and the cost of at most one bridge per existing vertex
give the bound for actual prefixes, including disconnected overlays. -/
theorem edge_budget {v f : Nat} (C : PlanarDegrees.Topology.ClosedTrace v f)
    (terminal : (f+1)+4=2*(v+1)) (rd todo : List Face) (p : (rd++todo).Perm (List.ofFn C.faces))
    (s : Inventory) (ok : replay (rd.flatMap Face.sides)=some s) :
    (Overlay.edges rd s).length+(Overlay.vertices rd s).length ≤ 22*(PlanarDegrees.FrontierStep.activeNames s).eraseDups.length := by
  have bounds := Overlay.size rd s ok
  have sparse := SparseOverlay.retained_bound C terminal rd todo p s ok
  omega

/-- Least natural number whose square is at least n. -/
def ceilRoot (n : Nat) := if n=0 then 0 else (n-1).sqrt+1

theorem ceilRoot_le_iff (n k : Nat) : ceilRoot n≤k ↔ n≤k*k := by
  by_cases eq : n=0
  · simp [ceilRoot,eq]
  · simp only [ceilRoot,eq,ite_false]
    rw [Nat.add_one_le_iff,Nat.sqrt_lt]; omega

theorem record_width (t : Contour 0) (C : Chords t.buds) (vs es : List Tag) (ds : List Nat)
    (hv : vs.length=t.treeEdges+1) (he : es.length=t.treeEdges+t.buds/2)
    {b n : Nat} (order : 0<n) (size : es.length≤22*b) (active : b≤(ds.map cost).sum)
    (weight : (ds.map cost).sum*(ds.map cost).sum≤220^2*n) :
    (encode t C vs es ds).length≤100000*ceilRoot n := by
  have sq := (ceilRoot_le_iff n (ceilRoot n)).mp le_rfl
  have cap : (ds.map cost).sum≤220*ceilRoot n := by
    apply Nat.mul_self_le_mul_self_iff.mp
    nlinarith [Nat.mul_le_mul_left (220^2) sq]
  have pos : 0<ceilRoot n := by
    by_contra! h
    have e : ceilRoot n=0 := by omega
    rw [e] at sq; omega
  have fw := fixed_width t C vs es hv he
  have cw := counter_width ds
  simp only [encode,List.length_append]; omega

end Recognition.CompactBoundary
