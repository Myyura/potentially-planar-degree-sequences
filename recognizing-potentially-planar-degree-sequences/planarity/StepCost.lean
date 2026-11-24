import WitnessCost
import FullDegrees

/-! A dense word-access implementation of one triangle proposal. Input
relations are array-backed after each successful step. Units charge array
reads/writes, Boolean and index operations, and visited list cells. The
bounds below concern these operations on word-sized vertex and degree
indices, including failed proposals. -/
namespace Recognition.StepCost
open Recognition.QuotientDP Recognition.WitnessTable

/-- Tabulate values and accumulate the charges of the actual evaluations.
The returned closure only reads a cell of the materialized vector. -/
def tab (p : Fin n → α × Nat) : (Fin n → α) × Nat :=
  let a := Vector.ofFn p
  (fun i => a[i.val].1, ((List.finRange n).map (fun i => a[i.val].2+2)).sum+1)

@[simp] theorem tab_val (p : Fin n → α × Nat) (i : Fin n) : (tab p).1 i=(p i).1 := by simp [tab]

private theorem sum_bound (l : List ι) (F : ι → Nat) (u) (h : ∀ x,F x≤u) :
    (l.map F).sum≤l.length*u := by
  induction l with
  | nil => simp
  | cons x xs ih => simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm _ u] using Nat.add_le_add (h x) ih

theorem tab_cost (p : Fin n → α × Nat) (u) (h : ∀i,(p i).2≤u) : (tab p).2≤n*(u+2)+1 := by
  have range := sum_bound (List.finRange n) (fun i => (p i).2+2) (u+2) (fun i => Nat.add_le_add_right (h i) _)
  simpa [tab] using Nat.add_le_add_right range 1

def square (p : Side n → α × Nat) : (Side n → α) × Nat :=
  let rows := tab fun i => tab fun j => p (i,j)
  (fun x => rows.1 x.1 x.2,rows.2)

@[simp] theorem square_val (p : Side n → α × Nat) (x : Side n) : (square p).1 x=(p x).1 := by simp [square]

def squareBound (n u : Nat) := n*(n*(u+2)+3)+1

theorem square_cost (p : Side n → α × Nat) (u) (h : ∀ i,(p i).2≤u) :
    (square p).2 ≤ squareBound n u :=
  tab_cost _ _ (fun i => tab_cost _ _ (fun j => h (i,j)))

/-- The three slot comparisons in an `on`, `group` or `value` query have a
fixed size. Assign each cell a bound for its finite local Boolean circuit.
The global component guard, active-vertex lookups and histogram scans are
charged separately. -/
def dense (s : State n) (a : Triangle n) : State n × Nat :=
  let u := fullNext s a
  let pend := square fun e => (u.pending e,48)
  let closed :=  square fun e => (u.sealed e,52)
  let block := square fun e => square fun f => (u.blocks e f,256)
  let deg := tab fun x => (u.current x,64)
  ({u with pending := pend.1,sealed := closed.1,blocks := block.1,current := deg.1},
   pend.2+closed.2+block.2+deg.2)

@[simp] theorem dense_val (s : State n) (a : Triangle n) : (dense s a).1=fullNext s a := by
  simp [dense,square,tab]

def denseBound (n : Nat) := squareBound n 48+squareBound n 52+
  squareBound n (squareBound n 256)+(n*(64+2)+1)

theorem dense_cost (s : State n) (a : Triangle n) : (dense s a).2≤denseBound n := by
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (square_cost _ 48 (fun _ => le_rfl))
    (square_cost _ 52 (fun _ => le_rfl))) (square_cost _ _ (fun _ => square_cost _ 256 (fun _ => le_rfl))))
    (tab_cost _ 64 (fun _ => le_rfl))

/-- Scan all ordered pairs for the final-closing or surviving-component
test. This includes the cost of examining both the open and block flags. -/
def existsNames (p : Fin n → Bool × Nat) : Bool × Nat :=
  let a := tab p
  ((List.finRange n).any a.1,a.2+n+1)

@[simp] theorem existsNames_val (p : Fin n → Bool × Nat) :
    (existsNames p).1=true ↔ ∃ i,(p i).1=true := by simp [existsNames]

theorem existsNames_cost (p : Fin n → Bool × Nat) (u) (h : ∀ i,(p i).2≤u) :
    (existsNames p).2 ≤ n*(u+3)+2 := by
  have z := tab_cost p u h
  change (tab p).2+n+1≤_; rw [show n*(u+3)=n*(u+2)+n by ring]; omega

def anyPair (p : Side n → Bool × Nat) : Bool × Nat :=
  existsNames fun x => existsNames fun y => p (x,y)

@[simp] theorem anyPair_val (p : Side n → Bool × Nat) : (anyPair p).1=true ↔ ∃e,(p e).1=true := by
  simp [anyPair,Prod.exists]

def anyPairBound (n u : Nat) := n*(n*(u+3)+5)+2

theorem anyPair_cost (p : Side n → Bool × Nat) (u) (h : ∀e,(p e).2≤u) :
    (anyPair p).2≤anyPairBound n u :=
  existsNames_cost _ _ (fun x => existsNames_cost _ _ (fun y => h (x,y)))

def frontier (bound : Nat) (s : State n) (a : Triangle n) : Bool × Nat :=
  if s.faces+1=bound then
    let z := anyPair fun e => (opened s a e,48)
    (!z.1,z.2+2)
  else anyPair fun e => (opened s a e && group s a e,128)

theorem frontier_val (bound : Nat) (s : State n) (a : Triangle n) : (frontier bound s a).1 ↔
    (if s.faces+1=bound then ∀ e,opened s a e=false else ∃e,opened s a e=true ∧ group s a e=true) := by
  unfold frontier; split
  · simp only [Bool.not_eq_true']; simpa only [not_exists,Bool.not_eq_true] using not_congr (anyPair_val (fun e => (opened s a e,48)))
  · simp

theorem frontier_cost (bound : Nat) (s : State n) (a : Triangle n) :
    (frontier bound s a).2 ≤ anyPairBound n 128+2 := by
  unfold frontier; split
  · apply Nat.add_le_add_right
    apply (anyPair_cost _ 48 (fun _ => le_rfl)).trans
    dsimp [anyPairBound]; gcongr; decide
  · exact (anyPair_cost _ 128 (fun _ => le_rfl)).trans (Nat.le_add_right ..)



/-- Check availability and remove each released degree in one pass over the
at most three requests. Each member/erase operation scans at most the
current residual length. -/
def debit : List Nat → Multiset Nat → Option (Multiset Nat) × Nat
  | [],r => (some r,1)
  | x::xs,r =>
    if x∈r then
      let z := debit xs (r.erase x)
      (z.1,2*(r.card+1)+z.2+2)
    else (none,r.card+2)

theorem debit_val (xs : List Nat) (r : Multiset Nat) : (debit xs r).1 =
    if (xs : Multiset Nat)≤r then some (r-(xs : Multiset Nat)) else none := by
  induction xs generalizing r with
  | nil => simp [debit]
  | cons x xs ih =>
    by_cases h : x∈r
    · have eq : ((x::xs : List Nat) : Multiset Nat) ≤ r ↔ (xs : Multiset Nat)≤r.erase x := by
        conv_lhs => rw [←Multiset.cons_erase h]
        rw [←Multiset.cons_coe]; exact Multiset.cons_le_cons_iff x
      simp only [debit,ite_eq_left h,eq,ih]; simp only [←Multiset.cons_coe,Multiset.sub_cons]
    · have ne : ¬ ((x::xs : List Nat) : Multiset Nat) ≤ r := fun k => h (Multiset.mem_of_le k (by simp))
      simp [debit,h,ne]

theorem debit_cost (xs : List Nat) (r : Multiset Nat) :
    (debit xs r).2≤xs.length*(2*(r.card+1)+2)+1 := by
  induction xs generalizing r with
  | nil => simp [debit]
  | cons x xs ih =>
    simp only [debit,List.length_cons]
    split
    · have less := (ih (r.erase x)).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Multiset.card_le_card (Multiset.erase_le x r)) _)) _)) _)
      calc
        _ ≤ 2*(r.card+1)+(xs.length*(2*(r.card+1)+2)+1)+2 := Nat.add_le_add_right (Nat.add_le_add_left less _) _
        _ = _ := by ring
    · rw [Nat.succ_mul]; omega

def activeScan (p : Side n → Bool) (unitCost : Nat) (v : Fin n) :=
  existsNames fun y => (p (v,y),unitCost)

@[simp] theorem activeScan_val (p : Side n → Bool) (unitCost v) :
    (activeScan p unitCost v).1=active p v := by
  apply Bool.eq_iff_iff.mpr; simp [activeScan,active]

/-- Three labelled corners. Each word stores its old/new liveness and its
new degree. Both liveness queries use finite scans from the dense guard. -/
def slotsInfo (s : State n) (a : Triangle n) :=
  tab fun k : Fin 3 =>
    let old := activeScan s.pending 1 (a.v k)
    let now := activeScan (opened s a) 48 (a.v k)
    ((old.1,now.1,value s a (a.v k)),old.2+now.2+64)

def releasedList (s : State n) (a : Triangle n) : List Nat :=
  let p := (slotsInfo s a).1
  ((List.finRange 3).filter fun k => !(p k).2.1).map (fun k => (p k).2.2)

@[simp] theorem released_val (s : State n) (a : Triangle n) :
    ((releasedList s a : List Nat) : Multiset Nat)=released s a := by simp [releasedList,slotsInfo,released]

theorem slot_cost (s : State n) (a : Triangle n) : (slotsInfo s a).2 ≤ 3*(55*n+70)+1 := by
  apply tab_cost _ (55*n+68)
  intro k
  have h := existsNames_cost (fun j => (s.pending (a.v k,j),1)) 1 (fun _ => le_rfl)
  have g := existsNames_cost (fun j => (opened s a (a.v k,j),48)) 48 (fun _ => le_rfl)
  dsimp [activeScan]; omega

theorem released_size (s : State n) (a : Triangle n) : (releasedList s a).length≤3 := by
  simp only [releasedList,List.length_map]
  exact (List.length_filter_le ..).trans_eq List.length_finRange

def small (s : State n) (seen : Finset (Fin n)) (a : Triangle n) (bound : Nat) : Bool :=
  let p := (slotsInfo s a).1
  decide ((∀ i, a.v i∈seen → (p i).1=true) ∧ Function.Injective a.v ∧
    s.used+tally (fun i => !(p i).1) ≤ n ∧ s.faces<bound ∧ ∀k,s.sealed (side a k)=false)

def charged (bound : Nat) (e : Entry n) (a : Triangle n) : Option (Entry n) × Nat :=
  let border := frontier bound e.raw a
  let debt := debit (releasedList e.raw a) e.raw.remaining
  let cost := border.2+debt.2+3*(slotsInfo e.raw a).2+20*(n+1)+128
  if small e.raw e.seen a bound && border.1 then
    match debt.1 with
    | none => (none,cost)
    | some r =>
      let m := dense e.raw a
      (some ⟨a::e.past,e.seen∪vertices a,{m.1 with remaining := r}⟩,cost+m.2)
  else (none,cost)

theorem charged_val (bound : Nat) (e : Entry n) (a : Triangle n) : (charged bound e a).1=step bound e a := by
  have sg : small e.raw e.seen a bound ↔
      (∀k,a.v k∈e.seen → active e.raw.pending (a.v k)=true) ∧ Function.Injective a.v ∧
      e.raw.used+fresh e.raw a≤n ∧ e.raw.faces<bound ∧ ∀k,e.raw.sealed (side a k)=false := by
    simp [small,slotsInfo,fresh]
  let eligible := ∀k,a.v k∈e.seen → active e.raw.pending (a.v k)=true
  let paid := released e.raw a≤e.raw.remaining
  let passed := small e.raw e.seen a bound && (frontier bound e.raw a).1
  have guards : eligible ∧ allowed bound e.raw a=true ↔ passed=true ∧ paid := by
    dsimp only [eligible,passed,paid]
    rw [Bool.and_eq_true,sg,frontier_val]
    simp only [allowed,decide_eq_true_eq]; tauto
  have shape : step bound e a = if eligible ∧ allowed bound e.raw a=true then
      some ⟨a::e.past,e.seen∪vertices a,fullNext e.raw a⟩ else none := by
    by_cases h : eligible <;> by_cases h' : allowed bound e.raw a=true <;>
      simp only [eligible] at h
    all_goals simp [step,fullAdvance,eligible,h,h']
  rw [shape,if_congr guards rfl rfl]
  unfold charged
  dsimp only
  change ((if passed then _ else _) : Option (Entry n) × Nat).1=_
  by_cases h : passed=true <;> by_cases k : released e.raw a≤e.raw.remaining <;>
    simp [h,paid,k,debit_val,dense_val,fullNext,nextState]

def budget (n m : Nat) := anyPairBound n 128+2+(3*(2*(m+1)+2)+1)+
  3*(3*(55*n+70)+1)+20*(n+1)+128+denseBound n

theorem charged_cost (bound : Nat) (e : Entry n) (a : Triangle n) {m : Nat} (limit : e.raw.remaining.card≤m) :
    (charged bound e a).2≤budget n m := by
  have b := frontier_cost bound e.raw a
  have d : (debit (releasedList e.raw a) e.raw.remaining).2≤3*(2*(m+1)+2)+1 :=
    (debit_cost ..).trans (Nat.add_le_add_right (Nat.mul_le_mul (released_size ..)
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right limit _)) _)) _)
  have s := slot_cost e.raw a
  have m := dense_cost e.raw a
  unfold charged budget
  dsimp only
  split
  · split <;> dsimp <;> omega
  · dsimp; omega

theorem budget_polynomial (n : Nat) : budget n n≤3000*(n+1)^4 := by
  simp only [budget,anyPairBound,denseBound,squareBound]
  nlinarith [Nat.zero_le n,Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4)]

theorem reachable_fee (bound : Nat) (target : Multiset Nat) (e : Entry n) (a : Triangle n)
    (good : Good bound target e) (inputs : target.card≤n) : (charged bound e a).2≤3000*(n+1)^4 := by
  have rem : e.raw.remaining≤target := by rw [← FullDegrees.histogram good]; exact Multiset.le_add_right .. 
  exact (charged_cost bound e a ((Multiset.card_le_card rem).trans inputs)).trans (budget_polynomial n)

/-- The fixed fee usable even under an unguarded universal fee parameter.
On the actual reached tables it dominates the measured charge. -/
def proposalFee (_ : Entry n) (_ : Triangle n) := 3000*(n+1)^4

theorem charged_on_layer (cmp : State n → State n → Bool) (table bound target k)
    (inputs : target.card≤n) {e : Entry n} (hit : e∈layer cmp table bound target k) (a : Triangle n) :
    (charged bound e a).2≤proposalFee e a :=
  reachable_fee _ _ _ _ (layer_sound _ _ _ _ _ _ hit) inputs

private theorem expand_congr (f g : α → List α × Nat) (xs : List α)
    (eq : ∀ x∈xs, f x=g x) : LayerCost.expand f xs=LayerCost.expand g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [LayerCost.expand,eq x (List.mem_cons_self ..),ih (fun a ha => eq a (List.mem_cons_of_mem _ ha))]

private theorem reachable_congr (cmp : State n → State n → Bool × Nat) (bound : Nat)
    (table : List (State n)) (target : Multiset Nat) (f g : Entry n → Triangle n → Nat) (k : Nat)
    (eq : ∀ j, ∀ e∈layer (fun x y => (cmp x y).1) table bound target j,∀a, f e a=g e a) :
    WitnessCost.run cmp f table bound target k=WitnessCost.run cmp g table bound target k := by
  induction k with
  | zero => rfl
  | succ j ih =>
    simp only [WitnessCost.run,ih]
    have same := expand_congr (WitnessCost.propose f bound) (WitnessCost.propose g bound)
      (WitnessCost.run cmp g table bound target j).1 (fun e he => by
        rw [WitnessCost.output] at he
        have h : f e=g e := funext (eq j e he)
        simp [WitnessCost.propose,h])
    rw [same]

/-- The aggregate layer charge uses the actual, state-dependent proposal
meter. Its uniform estimate only needs histogram bounds on reached entries. -/
theorem measured_work (cmp : State n → State n → Bool × Nat) (table : List (State n))
    (bound : Nat) (target : Multiset Nat) (k u : Nat) (size : target.card≤n)
    (compareFee : ∀ x y,(cmp x y).2≤u) :
    (WitnessCost.run cmp (fun e a => (charged bound e a).2) table bound target k).2 ≤
      (k+1)*((table.length+2)^2*(n^3*8+2)*(max u (3000*(n+1)^4)+8)) := by
  let fee (e : Entry n) (a : Triangle n) := min (charged bound e a).2 (proposalFee e a)
  have same := reachable_congr cmp bound table target (fun e a => (charged bound e a).2) fee k
    (fun j e h a => (Nat.min_eq_left (charged_on_layer _ _ _ _ j size h a)).symm)
  rw [same]
  exact WitnessCost.work cmp fee table bound target k _ (fun x y => (compareFee x y).trans (Nat.le_max_left ..))
    (fun e a => (Nat.min_le_right ..).trans (Nat.le_max_right ..))

#print axioms charged_val
#print axioms measured_work
end Recognition.StepCost
