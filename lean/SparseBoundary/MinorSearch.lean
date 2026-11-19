import SparseBoundary.Graph

namespace SparseBoundary.MinorSearch

open Graph

/-- Vertex-set and open-neighborhood bit masks. A neighbor may also
    belong to the set. -/
structure Bag where
  verts : Nat
  neighbors : Nat
deriving DecidableEq, BEq

def vmask {n : Nat} : List (Fin n) → Nat
  | [] => 0
  | x :: s => (2 ^ x.val) ||| vmask s

def neigh {n : Nat} (g : Graph n) (v : Fin n) : Nat :=
  vmask ((List.finRange n).filter (g.adj v))

def encode {n : Nat} (g : Graph n) : List (Fin n) → Bag
  | [] => ⟨0,0⟩
  | v :: s => ⟨(2 ^ v.val) ||| (encode g s).verts, neigh g v ||| (encode g s).neighbors⟩

theorem test_vmask {n : Nat} (s : List (Fin n)) (k : Nat) :
    (vmask s).testBit k = true ↔ ∃ x ∈ s, x.val = k := by
  induction s with
  | nil => simp [vmask]
  | cons v s ih => simp [vmask, Nat.testBit_two_pow, ih]

private theorem eVerts {n : Nat} (g : Graph n) (s : List (Fin n)) :
    (encode g s).verts = vmask s := by
  induction s <;> simp [encode, vmask, *]

private theorem eNbors {n : Nat} (g : Graph n) (s : List (Fin n)) (v : Fin n) :
    (encode g s).neighbors.testBit v.val = true ↔ ∃ x ∈ s, g.adj x v = true := by
  induction s with
  | nil => simp [encode]
  | cons w s ih =>
    simp only [encode,Nat.testBit_or,Bool.or_eq_true,ih,neigh,test_vmask,
      List.mem_filter,List.mem_finRange,true_and,List.mem_cons,or_and_right,exists_or]
    constructor
    · rintro (⟨u, hu, eq⟩ | h)
      · exact Or.inl ⟨w,rfl,((Fin.ext eq : u = v) ▸ hu)⟩
      · exact Or.inr h
    · rintro (h|h)
      · obtain ⟨_,rfl,he⟩ := h
        exact Or.inl ⟨v,he,rfl⟩
      · exact Or.inr h

def extend {n : Nat} (g : Graph n) (b : Bag) (v : Fin n) : Bag :=
  ⟨(2 ^ v.val) ||| b.verts, neigh g v ||| b.neighbors⟩

def admits (catalog : Array (Option Nat)) (b : Bag) : Bool :=
  catalog[b.verts]?.join == some b.neighbors

/-- Entries are indexed by their vertex mask. Closure under adjoining an
    incident vertex proves that the table includes every connected list. -/
def covers {n : Nat} (g : Graph n) (cat : Array (Option Nat)) : Bool :=
  (List.finRange n).all (fun v => admits cat (encode g [v])) &&
  (List.range cat.size).all (fun m => match cat[m]?.join with
    | none => true
    | some a => (List.finRange n).all fun v =>
      !a.testBit v.val || admits cat (extend g ⟨m,a⟩ v))

theorem covered {n : Nat} {g : Graph n} {cat} (hc : covers g cat = true) :
    ∀ s, g.connected s = true → admits cat (encode g s) = true := by
  simp only [covers,Bool.and_eq_true,List.all_eq_true] at hc
  intro s; induction s with
  | nil => simp [connected]
  | cons v s ih =>
    cases s with
    | nil => exact fun _ => hc.1 v (List.mem_finRange v)
    | cons w tail =>
      intro hs
      simp only [connected, Bool.and_eq_true] at hs
      obtain ⟨h1, h2⟩ := hs
      have hi := ih h2
      change cat[(encode g (w :: tail)).verts]?.join == some (encode g (w :: tail)).neighbors at hi
      have hentry := beq_iff_eq.mp hi
      have hlt : (encode g (w::tail)).verts < cat.size := by
        apply Classical.byContradiction; intro h
        rw [Array.getElem?_eq_none (by omega)] at hentry
        cases hentry
      have hrow := hc.2 _ (List.mem_range.mpr hlt)
      rw [hentry] at hrow
      have hv := List.all_eq_true.mp hrow v (List.mem_finRange v)
      have edge := List.any_eq_true.mp h1
      obtain ⟨u, hu, hAdj⟩ := edge
      have hbit := (eNbors g (w::tail) v).mpr ⟨u, hu, by rwa [Graph.adj_comm]⟩
      simp only [hbit,Bool.not_true,Bool.false_or] at hv
      exact hv

def distinctBags (b c : Bag) : Bool := b.verts &&& c.verts == 0
def touchBags (b c : Bag) : Bool := b.neighbors &&& c.verts != 0

theorem distinct_of {n : Nat} {g : Graph n} {s t : List (Fin n)}
    (h : disjoint s t = true) : distinctBags (encode g s) (encode g t) = true := by
  simp only [disjoint,List.all_eq_true,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at h
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and,eVerts,Nat.zero_testBit,Bool.and_eq_false_iff]
  by_cases hbit : (vmask s).testBit i = true
  · obtain ⟨x,hx,ex⟩ := (test_vmask s i).mp hbit
    right; apply Bool.eq_false_iff.mpr; intro ht
    obtain ⟨y,hy,ey⟩ := (test_vmask t i).mp ht
    exact h x hx ((Fin.ext (ey.trans ex.symm) : y = x) ▸ hy)
  · exact Or.inl (Bool.eq_false_iff.mpr hbit)

theorem touch_of {n : Nat} {g : Graph n} {s t : List (Fin n)}
    (h : links g s t = true) : touchBags (encode g s) (encode g t) = true := by
  obtain ⟨x,hx,hxy⟩ := List.any_eq_true.mp h
  obtain ⟨y,hy,hxy⟩ := List.any_eq_true.mp hxy
  apply bne_iff_ne.mpr; intro h0
  have hh := congrArg (fun q : Nat => q.testBit y.val) h0
  have b1 := (eNbors g s y).mpr ⟨x,hx,hxy⟩
  have b2 := (test_vmask t y.val).mpr ⟨y,hy,rfl⟩
  simp [eVerts,b1,b2] at hh


def pool (cat : Array (Option Nat)) : List Bag :=
  (List.range cat.size).filterMap fun m => (cat[m]?.join).map (fun a => ⟨m,a⟩)

theorem in_pool {cat : Array (Option Nat)} {b : Bag}
    (h : admits cat b = true) : b ∈ pool cat := by
  obtain ⟨m,a⟩ := b
  have eq := beq_iff_eq.mp h
  change cat[m]?.join = some a at eq
  have hlt : m < cat.size := by
    apply Classical.byContradiction; intro hn
    rw [Array.getElem?_eq_none (by omega)] at eq; cases eq
  apply List.mem_filterMap.mpr
  exact ⟨m,List.mem_range.mpr hlt,by simp [eq]⟩

def compat (required : Bool) (b c : Bag) : Bool :=
  distinctBags b c && (!required || touchBags b c)

/-- Select one branch set per index. Filter the remaining domains as
    soon as the new branch set is selected. -/
def search {k : Nat} (R : Fin k → Fin k → Bool) :
    List (Fin k) → (Fin k → List Bag) → Bool
  | [], _ => true
  | i::is, opts => (opts i).any fun b =>
    search R is (fun j => (opts j).filter (compat (R i j) b))

private theorem search_complete {n k : Nat} {G : Graph n} {R : Fin k → Fin k → Bool}
    {bags} (h : G.minorTest R bags = true) (is : List (Fin k)) (hn : is.Nodup)
    (opts : Fin k → List Bag) (hm : ∀ i ∈ is, encode G (bags i) ∈ opts i) :
    search R is opts = true := by
  induction is generalizing opts with
  | nil => rfl
  | cons i is ih =>
    simp only [List.nodup_cons] at hn
    apply List.any_eq_true.mpr
    refine ⟨_,hm i (List.mem_cons_self ..),ih hn.2 _ ?_⟩
    intro j hj
    apply List.mem_filter.mpr
    refine ⟨hm j (List.mem_cons_of_mem _ hj),?_⟩
    have row := List.all_eq_true.mp h i (List.mem_finRange i)
    simp only [Bool.and_eq_true] at row
    have cell := List.all_eq_true.mp row.2 j (List.mem_finRange j)
    simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at cell
    have ne : i ≠ j := by intro eq; subst j; exact hn.1 hj
    have hd := distinct_of (g:=G) (cell.1.resolve_left ne)
    simp only [compat,hd,Bool.true_and,Bool.or_eq_true]
    exact cell.2.imp_right touch_of

theorem planar_of_search {n : Nat} (G : Graph n) (cat : Array (Option Nat))
    (hc : covers G cat = true)
    (ha : search clique5 (List.finRange 5) (fun _ => pool cat) = false)
    (hb : search biclique33 (List.finRange 6) (fun _ => pool cat) = false) :
    G.Planar := by
  have eqtrue {k : Nat} {R : Fin k → Fin k → Bool} {bags}
      (h : G.minorTest R bags = true) :
      search R (List.finRange k) (fun _ => pool cat) = true := by
    apply search_complete h _ (List.nodup_finRange _)
    intro i _
    have row := List.all_eq_true.mp h i (List.mem_finRange i)
    simp only [Bool.and_eq_true] at row
    exact in_pool (covered hc _ row.1)
  constructor
  · rintro ⟨bags, h⟩; have := eqtrue h; simp_all
  · rintro ⟨bags, h⟩; have := eqtrue h; simp_all


/-- Form the candidate table. Its completeness is checked separately
    by covers, and its faithfulness is unnecessary for a negative search. -/
def makeCatalog {n : Nat} (G : Graph n) : Array (Option Nat) :=
  ((List.range (2^n)).map fun m =>
    let vertices := (List.finRange n).filter (fun v => m.testBit v.val)
    let expand := fun seen : Nat =>
      vertices.foldl (fun s v => if seen.testBit v.val then s ||| neigh G v else s) seen &&& m
    match vertices with
    | [] => none
    | v :: _ =>
      let component := (List.range n).foldl (fun s _ => expand s) (2^v.val)
      if component == m then some (encode G vertices).neighbors else none).toArray


/-- A compact bit-vector description may impose any necessary conditions
    on a branch set. Every entry in the covering catalog is checked. -/
structure BagBounds (w : Nat) where
  allowed : BitVec w → Bool
  neighbors : BitVec w → BitVec w

def validates {w : Nat} (cat : Array (Option Nat)) (spec : BagBounds w) : Bool :=
  (pool cat).all fun b =>
    let v := BitVec.ofNat w b.verts
    spec.allowed v && v.toNat == b.verts && (spec.neighbors v).toNat == b.neighbors

theorem forbidden_of_bounds {n k w : Nat} (g : Graph n)
    (cat : Array (Option Nat)) (spec : BagBounds w) (R : Fin k → Fin k → Bool)
    (hc : covers g cat = true) (hs : validates cat spec = true)
    (hn : ∀ f : Fin k → BitVec w,
      (∀ i, spec.allowed (f i) = true) →
      (∀ i j, i ≠ j → f i &&& f j = 0) →
      (∀ i j, R i j = true → spec.neighbors (f i) &&& f j ≠ 0) → False) :
    ¬ ∃ bags, g.minorTest R bags = true := by
  rintro ⟨bags,h⟩
  let f := fun i => BitVec.ofNat w (encode g (bags i)).verts
  have row i := List.all_eq_true.mp h i (List.mem_finRange i)
  simp only [Bool.and_eq_true] at row
  have specRow i := List.all_eq_true.mp hs _ (in_pool (covered hc _ (row i).1))
  change ∀ i, (spec.allowed (f i) && ((f i).toNat == _) && ((spec.neighbors (f i)).toNat == _)) = true at specRow
  simp only [Bool.and_eq_true,beq_iff_eq] at specRow
  apply hn f (fun i => (specRow i).1.1)
  · intro i j hij
    have cell := List.all_eq_true.mp (row i).2 j (List.mem_finRange j)
    simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at cell
    have hh := distinct_of (g:=g) (cell.1.resolve_left hij)
    have eq := beq_iff_eq.mp hh
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and,(specRow i).1.2,(specRow j).1.2]
    exact eq
  · intro i j hr he
    have cell := List.all_eq_true.mp (row i).2 j (List.mem_finRange j)
    simp only [Bool.and_eq_true,hr,Bool.not_true,Bool.false_or] at cell
    have hh := bne_iff_ne.mp (touch_of cell.2)
    apply hh
    have eq := congrArg BitVec.toNat he
    have z : ((0 : BitVec w).toNat) = 0 := by simp
    rw [z] at eq
    simpa only [BitVec.toNat_and,(specRow i).2,(specRow j).1.2] using eq

end SparseBoundary.MinorSearch
