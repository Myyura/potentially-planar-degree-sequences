import StateIncidence
import LabelWitness
import OrderInput

/-! Keep a concrete history at each table entry. Proposals are made on its
own permanent names. Two histories with isomorphic frontiers have precisely
the same available compact successors after allocating fresh names. -/
namespace Recognition.WitnessTable
open QuotientDP PlanarDegrees.Frontier SparseBoundary

private def cache (f : Fin n → α) : Fin n → α :=
  let a := Vector.ofFn f
  fun i => a[i.val]

private def sideCache (f : Side n → α) : Side n → α :=
  let rows := cache fun i => cache fun j => f (i,j)
  fun e => rows e.1 e.2

/-- Materialize the two edge tables, the block relation and the counters.
Every new step reads its predecessor through bounded array lookups. -/
def freeze (s : State n) : State n := {s with
  pending := sideCache s.pending
  sealed := sideCache s.sealed
  blocks := sideCache fun e => sideCache (s.blocks e)
  current := cache s.current}

@[simp] theorem freeze_eq (s : State n) : freeze s=s := by
  cases s
  simp [freeze,sideCache,cache]

structure Entry (n : Nat) where
  past : List (Triangle n)
  seen : Finset (Fin n)
  raw : State n

def init (target : Multiset Nat) : Entry n := ⟨[],∅,start target⟩
def Good (bound : Nat) (target : Multiset Nat) (e : Entry n) :=
  FullRun bound target e.past e.seen e.raw

def step (bound : Nat) (e : Entry n) (a : Triangle n) : Option (Entry n) := do
  if ∀ k, a.v k∈e.seen → active e.raw.pending (a.v k)=true then
    let raw ← fullAdvance bound e.raw a
    return ⟨a::e.past,e.seen∪vertices a,freeze raw⟩
  else none

def next (bound : Nat) (e : Entry n) := (candidates n).filterMap (step bound e)

/-- For each table key select the first compatible concrete history. -/
def index (cmp : State n → State n → Bool) (table : List (State n)) (cs : List (Entry n)) :=
  table.filterMap fun t => cs.find? (fun e => cmp (prune e.raw) t)

def layer (cmp : State n → State n → Bool) (table : List (State n)) (bound : Nat)
    (target : Multiset Nat) : Nat → List (Entry n)
  | 0 => index cmp table [init target]
  | k+1 => index cmp table ((layer cmp table bound target k).flatMap (next bound))

theorem next_sound (bound target) (e t : Entry n) (good : Good bound target e)
    (mem : t∈next bound e) : Good bound target t := by
  obtain ⟨a,_,eq⟩ := List.mem_filterMap.mp mem
  unfold step at eq
  split at eq <;> rename_i eligible
  · cases h : fullAdvance bound e.raw a with
    | none => simp [h] at eq
    | some raw =>
      simp only [h,bind,Option.bind_some,pure,Option.some.injEq,freeze_eq] at eq
      subst t
      exact .step good a eligible h
  · contradiction

private theorem selected {cmp : State n → State n → Bool} {table cs} {e : Entry n}
    (mem : e∈index cmp table cs) : e∈cs := by
  obtain ⟨_,_,h⟩ := List.mem_filterMap.mp mem
  exact List.mem_of_find?_eq_some h

private theorem select_target {cmp : State n → State n → Bool} {table cs} {x : State n}
    (test : ∀ a b,cmp a b=true ↔ Same a b) (ok : ∃ e∈cs,Same (prune e.raw) x)
    (coverage : Table.covered Same table x) :
    ∃ e∈index cmp table cs,Same (prune e.raw) x := by
  obtain ⟨t,mt,eq⟩ := coverage
  obtain ⟨y,my,ey⟩ := ok
  have someY : (cs.find? (fun z => cmp (prune z.raw) t)).isSome := by
    rw [List.isSome_find?,List.any_eq_true]; exact ⟨y,my,(test ..).mpr (equivalence.trans ey eq)⟩
  obtain ⟨e,h⟩ := Option.isSome_iff_exists.mp someY
  exact ⟨e,List.mem_filterMap.mpr ⟨t,mt,h⟩,equivalence.trans
    ((test ..).mp (List.find?_some (p := fun z : Entry n => cmp (prune z.raw) t) h)) (equivalence.symm eq)⟩

theorem layer_sound (cmp : State n → State n → Bool) (table) (bound target k) :
    ∀ e∈layer cmp table bound target k,Good bound target e := by
  induction k with
  | zero =>
    intro e mem
    have h := selected mem
    obtain rfl := List.mem_singleton.mp h; exact .init
  | succ k ih =>
    intro e mem
    obtain ⟨prev,m,reach⟩ := List.mem_flatMap.mp (selected mem)
    exact next_sound _ _ _ _ (ih prev m) reach

/-- Simulate a covered path while storing a permanently labelled witness
at an arbitrary first-match representative of each equivalence class. -/
theorem simulate (cmp : State n → State n → Bool) (test : ∀ a b,cmp a b=true ↔ Same a b)
    (table : List (State n)) (bound target) {k s} (path : Table.Path Same table (successors bound)
      (start target) k s) : ∃ e∈layer cmp table bound target k, Same (prune e.raw) s := by
  induction path with
  | start cov =>
    apply select_target test _ cov
    refine ⟨init target,List.mem_singleton_self _,?_⟩
    change Same (prune (start target : State n)) (start target)
    rw [prune_start]
    exact equivalence.refl _
  | @step k t u prev move cov ih =>
    obtain ⟨e,mem,iso⟩ := ih
    have good := layer_sound cmp table bound target k e mem
    obtain ⟨a,raw,fresh,valid,rel⟩ := lift_successor good iso move
    let y : Entry n := ⟨a::e.past,e.seen∪vertices a,raw⟩
    have one : step bound e a=some y := by simp only [step,ite_eq_left fresh,valid,bind,Option.bind_some,pure,freeze_eq,y]
    apply select_target test _ cov
    exact ⟨y,List.mem_flatMap.mpr ⟨e,mem,List.mem_filterMap.mpr ⟨a,all_candidates a,one⟩⟩,rel⟩

theorem layer_bound (cmp : State n → State n → Bool) (table) (bound target k) :
    (layer cmp table bound target k).length≤table.length := by
  cases k <;> apply List.length_filterMap_le

theorem next_bound (bound : Nat) (e : Entry n) : (next bound e).length≤8*n^3 := by
  exact (List.length_filterMap_le ..).trans (by rw [candidate_count,Nat.mul_comm])

/-- Search the final layer and return an edge-bit graph in input order. -/
def realize (cmp : State (v+1) → State (v+1) → Bool) (table : List (State (v+1)))
    (ds : List Nat) (f : Nat) : Option (Graph ds.length) := do
  let e ← (layer cmp table (f+1) ds (f+1)).find? (fun e => finished (f+1) e.raw)
  LabelWitness.relabel (LabelWitness.redGraph e.past) ds

theorem realize_sound (cmp : State (v+1) → State (v+1) → Bool) (table ds f G)
    (count : f+1+4=2*(v+1)) (yes : realize cmp table ds f=some G) : G.Planar ∧ G.Realizes ds := by
  unfold realize at yes
  cases hit : (layer cmp table (f+1) ds (f+1)).find? (fun e => finished (f+1) e.raw) with
  | none => simp [hit] at yes
  | some e =>
    simp only [hit,bind,Option.bind_some] at yes
    have good := layer_sound _ _ _ _ _ e (List.mem_of_find?_eq_some hit)
    have done := List.find?_some (p := fun e : Entry (v+1) => finished (f+1) e.raw) hit
    obtain ⟨H,eq,p,d⟩ := LabelWitness.output_graph ds good done count
    exact Option.some.inj (eq.symm.trans yes) ▸ ⟨p,d⟩

theorem realize_of_path (cmp : State (v+1) → State (v+1) → Bool) (test : ∀ a b,cmp a b=true ↔ Same a b)
    (table : List (State (v+1))) (ds : List Nat) (f : Nat) (s : State (v+1)) (count : f+1+4=2*(v+1)) (path : Table.Path Same table (successors (f+1))
      (start (ds : Multiset Nat)) (f+1) s) (terminal : finished (f+1) s) :
    ∃ G,realize cmp table ds f=some G ∧ G.Planar ∧ G.Realizes ds := by
  obtain ⟨e,mem,⟨p,iso⟩⟩ := simulate cmp test table _ _ path
  have accepts : finished (f+1) e.raw=true := (finish_iso iso _ ▸ terminal)
  have found : ((layer cmp table (f+1) ds (f+1)).find? (fun e => finished (f+1) e.raw)).isSome := by
    rw [List.isSome_find?,List.any_eq_true]; exact ⟨e,mem,accepts⟩
  obtain ⟨a,h⟩ := Option.isSome_iff_exists.mp found
  have good := layer_sound cmp table _ _ _ a (List.mem_of_find?_eq_some h)
  have done := List.find?_some (p := fun e : Entry (v+1) => finished (f+1) e.raw) h
  obtain ⟨G,out,pg,d⟩ := LabelWitness.output_graph ds good done count
  exact ⟨G,by simpa [realize,h] using out,pg,d⟩

end Recognition.WitnessTable
