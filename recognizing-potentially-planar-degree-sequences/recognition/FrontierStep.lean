import Frontier

/-! A concrete frontier transition at permanent vertex names. It forgets
sealed pairs touching a retired name, retains live red-degree counters,
and consumes the final degree of every vertex leaving the boundary. -/
namespace PlanarDegrees.FrontierStep
open Frontier

def live (s : Inventory) (v : Nat) := s.pending.any (touches · v)
def inside (A : Nat → Bool) (e : Edge) := A e.lo && A e.hi

def compact (s : Inventory) : Inventory := {
  pending := s.pending
  sealed := s.sealed.filter (inside (live s))
  redDegree v := if live s v then s.redDegree v else 0 }

structure Agree (A : Nat → Bool) (s t : Inventory) : Prop where
  pending : s.pending=t.pending
  sealed : s.sealed.filter (inside A) = t.sealed.filter (inside A)
  degree : ∀ v, A v → s.redDegree v=t.redDegree v

private theorem Agree.live_iff {A s t} (h : Agree A s t) (v : Nat) :
    live s v=live t v := by simp [live,h.pending]

private theorem Agree.tick {A s t} (h : Agree A s t) (a : Event) (ha : inside A a.edge) :
    (tick s a = none ∧ tick t a = none) ∨
    ∃ s' t', tick s a=some s' ∧ tick t a=some t' ∧ Agree A s' t' := by
  have test : a.edge ∈ s.sealed ↔ a.edge ∈ t.sealed := by
    simpa [ha] using (show a.edge ∈ s.sealed.filter (inside A) ↔ a.edge ∈ t.sealed.filter (inside A)
      from h.sealed ▸ Iff.rfl)
  by_cases shut : a.edge ∈ s.sealed
  · exact Or.inl ⟨by simp [Frontier.tick,shut],by simp [Frontier.tick,test.mp shut]⟩
  · have ht := mt test.mpr shut
    by_cases open_ : a.edge ∈ s.pending
    · have hot := h.pending ▸ open_
      simp only [Frontier.tick,ite_eq_right shut,ite_eq_right ht,ite_eq_left open_,ite_eq_left hot,
        reduceCtorEq,false_and,false_or,Option.some.injEq]
      refine ⟨_,_,rfl,rfl,?_⟩
      exact ⟨congrArg (List.filter (· != a.edge)) h.pending,by simp [ha,h.sealed],h.degree⟩
    · have hot : a.edge ∉ t.pending := h.pending ▸ open_
      simp only [Frontier.tick,ite_eq_right shut,ite_eq_right ht,ite_eq_right open_,ite_eq_right hot,
        reduceCtorEq,false_and,false_or,Option.some.injEq]
      refine ⟨_,_,rfl,rfl,?_⟩
      exact ⟨congrArg (List.cons a.edge) h.pending,h.sealed,fun v hv => by simp [h.degree v hv]⟩

/-- Visit the sides of an actual triangular face in the supplied order. -/
def runSides : List Event → Inventory → Option Inventory
  | [],s => some s
  | a::rest,s => (tick s a).bind (runSides rest)

private theorem Agree.run {A s t} (h : Agree A s t) (events : List Event)
    (valid : ∀ a ∈ events, inside A a.edge) :
    (runSides events s=none ∧ runSides events t=none) ∨
    ∃ s' t', runSides events s=some s' ∧ runSides events t=some t' ∧ Agree A s' t' := by
  induction events generalizing s t with
  | nil => exact Or.inr ⟨s,t,rfl,rfl,h⟩
  | cons a xs ih =>
    rcases h.tick a (valid a (by simp)) with ⟨hs,ht⟩|⟨s',t',hs,ht,agree⟩
    · exact Or.inl ⟨by simp [runSides,hs],by simp [runSides,ht]⟩
    · simpa [runSides,hs,ht] using ih agree (fun z hz => valid z (List.mem_cons_of_mem _ hz))

theorem runSides_replay {p : List Event} {s : Inventory} (hp : replay p=some s)
    (xs : List Event) : replay (xs.reverse ++ p) = runSides xs s := by
  induction xs generalizing p s with
  | nil => simpa [runSides] using hp
  | cons a xs ih =>
    simp only [List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append,runSides]
    have one : replay (a::p) = tick s a := by simp [replay,hp]
    cases ha : tick s a with
    | some t => simpa [ha] using ih (one.trans ha)
    | none =>
      have dead (ys : List Event) : replay (ys ++ a::p)=none := by
        induction ys with
        | nil => exact one.trans ha
        | cons e ys ih => simp [replay,ih]
      simpa using dead xs.reverse

private theorem pending_upper {s t : Inventory} {events : List Event} (run : runSides events s=some t)
    {v} (atEnd : live t v) : live s v ∨ ∃ a ∈ events, touches a.edge v := by
  induction events generalizing s with
  | nil => simp [runSides] at run; subst t; exact Or.inl atEnd
  | cons a es ih =>
    cases hs : tick s a with
    | none => simp [runSides,hs] at run
    | some u =>
      have rest : runSides es u=some t := by simpa [runSides,hs] using run
      rcases ih rest with earlier|⟨b,hb,hv⟩
      · obtain ⟨d,hd,hv⟩ := List.any_eq_true.mp earlier
        unfold tick at hs
        split at hs
        · contradiction
        · split at hs <;> simp only [Option.some.injEq] at hs <;> subst u
          · exact Or.inl (List.any_eq_true.mpr ⟨d,(List.mem_filter.mp hd).1,hv⟩)
          · rcases List.mem_cons.mp hd with rfl|hd
            · exact Or.inr ⟨a,by simp,hv⟩
            · exact Or.inl (List.any_eq_true.mpr ⟨d,hd,hv⟩)
      · exact Or.inr ⟨b,List.mem_cons_of_mem _ hb,hv⟩

def allowed (s : Inventory) (f : Face) (v : Nat) := live s v || (corners f).contains v

/-- Each proposed corner is live or is a genuinely new permanent name. -/
def available (p : List Event) (s : Inventory) (f : Face) : Prop :=
  ∀ v ∈ corners f, live s v ∨ ∀ a ∈ p, touches a.edge v = false

private theorem fresh_degree {p s} (hp : replay p=some s) {v : Nat}
    (fresh : ∀ a ∈ p, touches a.edge v=false) : s.redDegree v=0 := by
  rw [(replay_accurate hp).redDegree]
  apply List.countP_eq_zero.mpr
  intro d hd
  have hm : d ∈ p.map Event.edge := List.count_pos_iff.mp (reds_seen hd)
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
  simpa using fresh a ha

private theorem fresh_sealed {p s} (hp : replay p=some s) {v : Nat}
    (fresh : ∀ a ∈ p, touches a.edge v=false) {d} (hd : d ∈ s.sealed) : touches d v=false := by
  have h := ((replay_accurate hp).sealed d).mp hd
  have hm : d ∈ p.map Event.edge := List.count_pos_iff.mp (by change 0<occurrences p d; omega)
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
  exact fresh a ha

private theorem entry {p s} (hp : replay p=some s) (f : Face) (av : available p s f) :
    Agree (allowed s f) s (compact s) := by
  have applies {d} (hd : d ∈ s.sealed) {v} (hit : touches d v) (yes : allowed s f v) :
      live s v := by
    rcases Bool.or_eq_true_iff.mp yes with h|h
    · exact h
    · rcases av v (by simpa using h) with h|fresh
      · exact h
      · rw [fresh_sealed hp fresh hd] at hit; contradiction
  constructor
  · rfl
  · change s.sealed.filter _ = (s.sealed.filter _).filter _
    rw [List.filter_filter]
    apply List.filter_congr
    intro d hd
    by_cases h : inside (allowed s f) d
    · obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
      have lo := applies hd (show touches d d.lo by simp [touches]) a
      have hi := applies hd (show touches d d.hi by simp [touches]) b
      simp [inside,lo,hi] at *
    · simp [h]
  · intro v yes
    by_cases live_ : live s v
    · simp [compact,live_]
    · have hc : v ∈ corners f := by simpa [allowed,live_] using yes
      exact (fresh_degree hp ((av v hc).resolve_left live_)).trans (by simp [compact,live_])

private theorem side_corners (f : Face) {a : Event} (h : a ∈ f.sides) :
    a.edge.lo ∈ corners f ∧ a.edge.hi ∈ corners f := by
  simp [Face.sides] at h
  rcases h with rfl|rfl|rfl <;> simp [corners]

private theorem new_live_allowed {s t : Inventory} {f : Face} (hs : runSides f.sides s=some t)
    {v : Nat} (hv : live t v) : allowed s f v := by
  rcases pending_upper hs hv with h|⟨a,ha,touch⟩
  · simp [allowed,h]
  · obtain ⟨lo,hi⟩ := side_corners f ha
    simp [touches] at touch
    rcases touch with rfl|rfl <;> simp [allowed,lo,hi]

private theorem compact_eq {A s t} (h : Agree A s t) (scope : ∀ v, live s v → A v) :
    compact s=compact t := by
  have same : live s = live t := funext h.live_iff
  have fit (u : Inventory) :
      u.sealed.filter (inside (live s)) =
      (u.sealed.filter (inside A)).filter (inside (live s)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro d _
    by_cases h : inside (live s) d
    · obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp h
      exact (by simp [inside,hl,hr,scope _ hl,scope _ hr])
    · simp [h]
  have sealed : s.sealed.filter (inside (live s)) = t.sealed.filter (inside (live t)) := by
    rw [← same, fit s, h.sealed, ← fit t]
  have de : (fun v => if live s v then s.redDegree v else 0) =
      (fun v => if live t v then t.redDegree v else 0) := by
    funext v
    by_cases l : live s v <;> simp [←same,l]
    exact h.degree _ (scope v l)
  unfold compact
  rw [h.pending, sealed, de]

def activeNames (s : Inventory) := s.pending.flatMap (fun e => [e.lo,e.hi])

private theorem active_mem {v : Nat} {s : Inventory} : v ∈ activeNames s ↔ live s v := by
  simp [activeNames,live,touches,List.mem_flatMap,List.any_eq_true]

/-- Names to finalize at this step, each occurring exactly once. -/
def releases (s t : Inventory) (f : Face) :=
  ((activeNames s ++ corners f).eraseDups).filter (fun v => !(live t v))

theorem release_spec {s t f v} :
    v ∈ releases s t f ↔ allowed s f v = true ∧ live t v = false := by
  simp [releases,allowed,active_mem]

def consume : List Nat → List Nat → Option (List Nat)
  | [], left => some left
  | x::xs,left => if x ∈ left then consume xs (left.erase x) else none

/-- The full and compact transitions use the same face and remaining
histogram. Both produce a compacted boundary for the following step. -/
def step (s : Inventory) (remaining : List Nat) (f : Face) : Option (Inventory × List Nat) := do
  let t ← runSides f.sides s
  let left ← consume ((releases s t f).map t.redDegree) remaining
  return (compact t,left)

theorem face_step_exact {p : List Event} {s : Inventory} (hp : replay p=some s)
    (remaining : List Nat) (f : Face) (av : available p s f) :
    step (compact s) remaining f = step s remaining f := by
  let A := allowed s f
  have sides (a) (ha : a ∈ f.sides) : inside A a.edge := by
    obtain ⟨lo,hi⟩ := side_corners f ha
    simp [A,inside,allowed,lo,hi]
  rcases (entry hp f av).run f.sides sides with ⟨hs,ht⟩|⟨t,u,hs,hu,agree⟩
  · simp [step,hs,ht]
  · have eq := compact_eq agree (fun _ hv => new_live_allowed hs hv)
    have names : releases (compact s) u f = releases s t f := by
      unfold releases
      rw [← funext agree.live_iff]
      rfl
    have vals : (releases s t f).map u.redDegree = (releases s t f).map t.redDegree := by
      apply List.map_congr_left
      intro v hv
      exact (agree.degree v (release_spec.mp hv).1).symm
    simp [step,hs,hu,names,vals,eq]

end PlanarDegrees.FrontierStep

namespace PlanarDegrees.FrontierStep
open Frontier

def ever (p : List Event) (v : Nat) := p.any (fun a => touches a.edge v)

def permitted (seen : Nat → Bool) (s : Inventory) (f : Face) :=
  (corners f).all (fun v => live s v || !(seen v))

theorem permitted_iff {p s f} : permitted (ever p) s f ↔ available p s f := by
  simp [permitted,available,ever,List.all_eq_true]

private theorem seen_update (f : Face) (p : List Event) (v : Nat) :
    ever (f.sides.reverse ++ p) v = (ever p v || (corners f).contains v) := by
  simp [ever,Face.sides,touches,corners]
  grind

/-- The search retains the set of previously used permanent labels so that
a retired vertex can never return as a proposed fresh vertex. -/
structure State where
  boundary : Inventory
  remaining : List Nat
  seen : Nat → Bool

def advance (s : State) (f : Face) : Option State := do
  if permitted s.seen s.boundary f then
    let (b,left) ← step s.boundary s.remaining f
    return ⟨b,left,fun v => s.seen v || (corners f).contains v⟩
  else none

structure History where
  past : List Event
  remaining : List Nat

def summarize (h : History) : Option State := do
  let s ← replay h.past
  return ⟨compact s,h.remaining,ever h.past⟩

/-- Full-history reference transition. Its only eligibility restriction on
old labels is that a previously seen corner is still live. -/
def recordFace (h : History) (f : Face) : Option History := do
  let s ← replay h.past
  if permitted (ever h.past) s f then
    let t ← runSides f.sides s
    let left ← consume ((releases s t f).map t.redDegree) h.remaining
    return ⟨f.sides.reverse ++ h.past,left⟩
  else none

theorem next_exact (h : History) (f : Face) :
    (summarize h).bind (advance · f) = (recordFace h f).bind summarize := by
  cases hp : replay h.past with
  | none => simp [summarize,recordFace,hp]
  | some s =>
    have perm : permitted (ever h.past) (compact s) f = permitted (ever h.past) s f := rfl
    by_cases good : permitted (ever h.past) s f
    · have actual := face_step_exact hp h.remaining f (permitted_iff.mp good)
      have agreeSeen := funext (seen_update f h.past)
      cases ht : runSides f.sides s with
      | none =>
        have out : step (compact s) h.remaining f = none := actual.trans (by simp [step,ht])
        simp [summarize,advance,recordFace,hp,perm,good,ht,out]
      | some t =>
        cases hl : consume ((releases s t f).map t.redDegree) h.remaining with
        | none =>
          have out : step (compact s) h.remaining f = none := actual.trans (by simp [step,ht,hl])
          simp [summarize,advance,recordFace,hp,perm,good,ht,hl,out]
        | some left =>
          have out : step (compact s) h.remaining f = some (compact t,left) := actual.trans (by simp [step,ht,hl])
          have replayed := (runSides_replay hp f.sides).trans ht
          simp [summarize,advance,recordFace,hp,perm,good,ht,hl,out,replayed,agreeSeen]
    · simp [summarize,advance,recordFace,hp,perm,good]

def run (s : State) : List Face → Option State
  | [] => some s
  | f::fs => (advance s f).bind (fun t => run t fs)

def record (h : History) : List Face → Option History
  | [] => some h
  | f::fs => (recordFace h f).bind (fun t => record t fs)

/-- Exact simulation on every face sequence, with malformed sides, failed
histogram consumption, and attempted reuse of retired names included. -/
theorem run_exact (h : History) (fs : List Face) :
    (summarize h).bind (fun s => run s fs) = (record h fs).bind summarize := by
  induction fs generalizing h with
  | nil => simp [run,record]
  | cons f fs ih =>
    have bindEq := congrArg (fun x : Option State => x.bind (fun s => run s fs)) (next_exact h f)
    simp only [run,record]
    rw [← Option.bind_assoc,bindEq,Option.bind_assoc,Option.bind_assoc]
    cases recordFace h f with
    | none => rfl
    | some a => exact ih a

theorem consume_sound {xs ds rem : List Nat} (h : consume xs ds = some rem) :
    ds.Perm (xs ++ rem) := by
  induction xs generalizing ds with
  | nil => simp [consume] at h; subst ds; exact List.Perm.refl _
  | cons a xs ih =>
    by_cases ha : a ∈ ds
    · simp [consume,ha] at h
      exact (List.perm_cons_erase ha).trans ((ih h).cons a)
    · simp [consume,ha] at h

theorem consume_complete {xs ds rem : List Nat} (p : ds.Perm (xs ++ rem)) :
    ∃ r, consume xs ds = some r ∧ r.Perm rem := by
  induction xs generalizing ds with
  | nil => exact ⟨ds,rfl,p⟩
  | cons a xs ih =>
    have mem : a ∈ ds := p.mem_iff.mpr (by simp)
    have preserved := ((List.perm_cons_erase mem).symm.trans p)
    obtain ⟨r,hr,eq⟩ := ih (List.Perm.cons_inv preserved)
    exact ⟨r,by simpa [consume,mem] using hr,eq⟩

end PlanarDegrees.FrontierStep
