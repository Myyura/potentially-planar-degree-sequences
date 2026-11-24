import StepCost
import DecodeMeter

/-! Meter the postprocessing of the two witness-carrying search variants.
Operations cover finite scans, edge tests, bit accesses to the packed
adjacency matrix, and construction of the graph in the input's label order. -/
namespace Recognition.OutputCost
open SparseBoundary QuotientDP WitnessTable PlanarDegrees.Frontier

def select (bound : Nat) : List (Entry n) → Option (Entry n) × Nat
  | [] => (none,1)
  | e::xs =>
    let check := 8*(n+1)^2+e.raw.remaining.card+16
    if finished bound e.raw then (some e,check) else
      let (res,w) := select bound xs
      (res,check+w)

theorem select_eq (bound : Nat) (xs : List (Entry n)) :
    (select bound xs).1=xs.find? (fun e => finished bound e.raw) := by
  induction xs with
  | nil => rfl
  | cons e xs ih => cases eq : finished bound e.raw <;> simp [select,List.find?,eq,ih]

private theorem select_cost (bound : Nat) (xs : List (Entry n))
    (rem : ∀e∈xs,e.raw.remaining.card≤n) :
    (select bound xs).2 ≤ (xs.length+1)*(n+32)^3 := by
  induction xs with
  | nil => simp only [select,List.length_nil,zero_add,one_mul]; have := Nat.pow_le_pow_left (show 1≤n+32 by omega) 3; simpa using this
  | cons e xs ih =>
    have this := rem e (by simp)
    have later := ih (fun a ha => rem a (by simp [ha]))
    have check : 8*(n+1)^2+e.raw.remaining.card+16 ≤ (n+32)^3 := by nlinarith
    simp only [select,List.length_cons]
    split <;> nlinarith

/-- Charge the recursive last-occurrence test on the actual event tails. -/
def redRows : List Event → List Edge × Nat
  | [] => ([],1)
  | a::p =>
    let (es,w) := redRows p
    (if occurrences p a.edge=0 ∧ a.red then a.edge::es else es,w+8*(p.length+1))

theorem redRows_eq (xs : List Event) : (redRows xs).1=reds xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [redRows,reds,ih]

theorem redRows_bounds (xs : List Event) :
    (redRows xs).1.length≤xs.length ∧ (redRows xs).2≤8*(xs.length+1)^2 := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    simp only [redRows,List.length_cons]
    split <;> (try simp only [List.length_cons]) <;> constructor <;> nlinarith [ih.1,ih.2]

private theorem rows_length (fs : List (Triangle n)) : (FullDegrees.rows fs).length=3*fs.length := by
  induction fs with
  | nil => rfl
  | cons a fs ih =>
    change ((FullDegrees.row a).sides++FullDegrees.rows fs).length=_
    simp [ih,Face.sides,Nat.mul_add]

theorem pair_budget (n : Nat) : pairCount n≤n*n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pairCount]; nlinarith

/-- Packing a relation constructs triangular rows and writes the resulting
bit vector. The quadratic factor in its bit length also covers the cost
of arbitrary-width bit shifts during packing. -/
def packFee (n lookup : Nat) := 8*(pairCount n+1)*(lookup+(n+1)^2+8)

def redGraph (fs : List (Triangle n)) : Graph n × Nat :=
  let (es,w) := redRows (FullDegrees.rows fs)
  (Witness.graph n es,64*(fs.length+1)+w+packFee n (12*(es.length+1)))

@[simp] theorem redGraph_eq (fs : List (Triangle n)) : (redGraph fs).1=LabelWitness.redGraph fs := by
  simp [redGraph,LabelWitness.redGraph,redRows_eq]

private theorem redGraph_cost (fs : List (Triangle n)) (h : fs.length≤2*n) :
    (redGraph fs).2≤(n+32)^5 := by
  obtain ⟨e,w⟩ := redRows_bounds (FullDegrees.rows fs)
  rw [rows_length] at e w
  have p := pair_budget n
  change 64*(fs.length+1)+(redRows (FullDegrees.rows fs)).2+
    8*(pairCount n+1)*(12*((redRows (FullDegrees.rows fs)).1.length+1)+(n+1)^2+8)≤_
  have mult := Nat.mul_le_mul (Nat.mul_le_mul_left 8 (Nat.add_le_add_right p 1))
    (show 12*((redRows (FullDegrees.rows fs)).1.length+1)+(n+1)^2+8 ≤12*(6*n+1)+(n+1)^2+8 by omega)
  have tail := w.trans (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left (by omega : 3*fs.length+1≤6*n+1) 2))
  apply (Nat.add_le_add (Nat.add_le_add (by omega : 64*(fs.length+1)≤64*(2*n+1)) tail) mult).trans
  nlinarith [Nat.zero_le (n^3),Nat.zero_le (n^4),Nat.zero_le (n^5)]

/-- The degree function is already cached by the caller. Each attempted
match charges a scan and an erase, even if a failure stops one of them. -/
def positions (val : Fin n → Nat) : List Nat → List (Fin n) → Option (List (Fin n)) × Nat
  | [],vs => (if vs.isEmpty then some [] else none,1)
  | a::as,vs =>
    let w := 8*(vs.length+1)
    match vs.find? (fun x => val x==a) with
    | none => (none,w)
    | some x =>
      let (out,later) := positions val as (vs.erase x)
      (out.map (x::·),w+later)

theorem positions_eq (val : Fin n → Nat) (ds) (vs) :
    (positions val ds vs).1=LabelWitness.positions val ds vs := by
  induction ds generalizing vs with
  | nil => rfl
  | cons a as ih =>
    simp only [positions,LabelWitness.positions]
    cases ok : vs.find? (fun x => val x==a) with
    | none => rfl
    | some x =>
      simp only [ih,bind,Option.bind_some]
      cases LabelWitness.positions val as (vs.erase x) <;> rfl

private theorem positions_cost (val : Fin n → Nat) (ds) (vs) :
    (positions val ds vs).2≤8*(vs.length+1)*(ds.length+1) := by
  induction ds generalizing vs with
  | nil => simp [positions]; omega
  | cons a as ih =>
    simp only [positions,List.length_cons]
    split
    · nlinarith
    · rename_i x eq
      have short : (vs.erase x).length ≤ vs.length := List.length_erase_le
      have h := (ih (vs.erase x)).trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right short 1)))
      nlinarith

/-- Cache all degrees before consuming the candidate labels. A failed
matching attempt returns its charge. The relabelled graph uses actual
list lookup for the matched labels and is packed a second time. -/
def relabel (G : Graph n) (ds : List Nat) : Option (Graph ds.length) × Nat :=
  let vals := Vector.ofFn G.degree
  let (out,w) := positions (fun i => vals[i.val]) ds (List.finRange n)
  let degreeFee := 8*(n+1)^2*(pairCount n+n+8)
  match out with
  | none => (none,w+degreeFee+1)
  | some names =>
    if h : names.length=ds.length then
      (some (G.restrict fun i => names[i.val]'(by omega)),w+degreeFee+packFee ds.length (4*(n+1)+pairCount n+8))
    else (none,w+degreeFee+ds.length+1)

@[simp] theorem relabel_eq (G : Graph n) (ds) : (relabel G ds).1=LabelWitness.relabel G ds := by
  simp only [relabel,LabelWitness.relabel,Vector.getElem_ofFn,positions_eq]
  split <;> simp_all only [bind,Option.bind_none,Option.bind_some]
  split <;> rfl

private theorem relabel_cost (G : Graph n) (ds) (h : ds.length=n) :
    (relabel G ds).2≤(n+32)^5 := by
  have pos := positions_cost G.degree ds (List.finRange n)
  rw [h,List.length_finRange] at pos
  have p := pair_budget n
  have pack : packFee ds.length (4*(n+1)+pairCount n+8) ≤
      8*(n*n+1)*(4*(n+1)+n*n+8+(n+1)^2+8) := by
    unfold packFee; rw [h]
    exact Nat.mul_le_mul (by omega) (by omega)
  have degree := Nat.mul_le_mul_left (8*(n+1)^2) (show pairCount n+n+8≤n*n+n+8 by omega)
  simp only [relabel,Vector.getElem_ofFn]
  split
  · nlinarith
  · split <;> nlinarith

def finish (ds : List Nat) (bound : Nat) (xs : List (Entry n)) : Option (Graph ds.length) × Nat :=
  let (picked,w) := select bound xs
  match picked with
  | none => (none,w)
  | some e =>
    let (G,r) := redGraph e.past
    let (H,l) := relabel G ds
    (H,w+r+l)

theorem finish_eq (cmp : State (v+1) → State (v+1) → Bool) (table) (ds) (f) :
    (finish ds (f+1) (layer cmp table (f+1) ds (f+1))).1=WitnessTable.realize cmp table ds f := by
  simp only [finish,WitnessTable.realize,select_eq,redGraph_eq,relabel_eq]
  cases eq : (layer cmp table (f+1) ds (f+1)).find? (fun e => finished (f+1) e.raw) <;> rfl

theorem finish_cost (ds : List Nat) (bound : Nat) (xs : List (Entry n)) (hlen : ds.length=n)
    (hb : bound≤2*n) (lens : ∀e∈xs,e.past.length≤bound) (rem : ∀e∈xs,e.raw.remaining.card≤n) :
    (finish ds bound xs).2 ≤ (xs.length+1)*(n+32)^24 := by
  have sel := select_cost bound xs rem
  let z := n+32
  have pos : 1≤z := by dsimp [z]; omega
  have up : z^3≤z^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have last : (xs.length+1)*z^5+z^5+z^5≤(xs.length+1)*z^24 := by
    have m : 3≤z^19 := (by decide : 3≤32^19).trans (Nat.pow_le_pow_left (by dsimp [z]; omega : 32≤z) 19)
    rw [show 24=5+19 by decide,Nat.pow_add,←Nat.mul_assoc]
    have inc := Nat.mul_le_mul_left ((xs.length+1)*z^5) m
    nlinarith [Nat.le_mul_of_pos_left (z^5) (Nat.succ_pos xs.length)]
  change (select bound xs).2 ≤ (xs.length+1)*z^3 at sel
  have s := sel.trans (Nat.mul_le_mul_left _ up)
  unfold finish
  dsimp only
  split
  · exact le_trans (by omega) last
  · rename_i e eq
    rw [select_eq] at eq
    have hit := List.mem_of_find?_eq_some eq
    have r := redGraph_cost e.past ((lens e hit).trans hb)
    have l := relabel_cost (redGraph e.past).1 ds hlen
    change (redGraph e.past).2≤z^5 at r
    change (relabel (redGraph e.past).1 ds).2≤z^5 at l
    exact (Nat.add_le_add (Nat.add_le_add s r) l).trans last

private theorem history_len {xs : List (Triangle n)} {s : State n} (h : FullRun bound target xs U s) :
    xs.length≤bound := by
  cases h with
  | init => simp
  | step prev a elig ok =>
    unfold fullAdvance at ok
    split at ok
    · rename_i yes
      have prev_len := (FullDegrees.facts prev).faces
      have guard := (of_decide_eq_true yes).2.2.1
      simp; omega
    · contradiction

theorem realize_cost (cmp : State (v+1) → State (v+1) → Bool) (table ds f)
    (hlen : ds.length=v+1) (hb : f+1≤2*(v+1)) :
    (finish ds (f+1) (layer cmp table (f+1) ds (f+1))).2 ≤ (table.length+1)*(v+1+32)^24 := by
  apply (finish_cost ds _ _ hlen hb ?_ ?_).trans
  · exact Nat.mul_le_mul_right _ (Nat.add_le_add_right (layer_bound ..) 1)
  · intro e he
    exact history_len (layer_sound _ _ _ _ _ e he)
  · intro e he
    have good := layer_sound _ _ _ _ _ e he
    have r : e.raw.remaining ≤ (ds : Multiset Nat) := by rw [←FullDegrees.histogram good]; exact Multiset.le_add_right ..
    simpa [hlen] using Multiset.card_le_card r

/-- Uniform bound for the final scan and labelled output construction,
independent of the choice of the exact state comparator. -/
theorem catalogue_cost (x : Nat) (ds : List Nat) (cmp : State (ds.length+1) → State (ds.length+1) → Bool) (f)
    (hb : f+1≤2*(ds.length+1)) (mass : (x::ds).sum≤6*(x::ds).length) :
    (finish (x::ds) (f+1) (layer cmp (ShortBoundary.catalogue (x::ds)) (f+1) (x::ds) (f+1))).2
      ≤ 2^(268957*((x::ds).length.sqrt+1)) := by
  let D := x::ds
  let S := D.length.sqrt+1
  have pos : 0<S := by simp [S]
  have largest := realize_cost cmp (ShortBoundary.catalogue D) D f rfl hb
  have c := PreprocessCost.catalogue_single_exponential D mass
  have one : 0<2^(268428*S) := Nat.two_pow_pos _
  have bound : (ShortBoundary.catalogue D).length+1≤2^(268429*S) := by
    have c' : (ShortBoundary.catalogue D).length+1≤2^(268428*S+1) := by
      rw [Nat.pow_succ]
      change _≤2^(268428*S) at c
      omega
    exact c'.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have poly : D.length+32≤2^(22*S) := (by omega :
    D.length+32≤D.length+BoundaryState.cutoff D.length+32).trans (DecodeMeter.factors D.length)
  have all := Nat.mul_le_mul bound (Nat.pow_le_pow_left poly 24)
  rw [←Nat.pow_mul,←Nat.pow_add,show 268429*S+22*S*24=268957*S by omega] at all
  exact largest.trans all

#print axioms catalogue_cost
#print axioms realize_cost
#print axioms finish_eq
end Recognition.OutputCost
