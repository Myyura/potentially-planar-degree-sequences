import Std

/-!
The edge inventory uses unordered endpoint pairs. The histogram bound below
counts all residual vectors for a fixed input by an elementary binary-slot
argument. All computations use natural numbers.
-/
namespace PlanarDegrees.Frontier

/-! ## Counting the residual degree histograms -/

/-- Entry zero of this list corresponds to degree `start`. -/
def mass (start : Nat) : List Nat → Nat
  | [] => 0
  | m :: tail => start * m + mass (start + 1) tail

/-- All residual multiplicity vectors obtainable by coordinatewise decrease. -/
def residuals : List Nat → List (List Nat)
  | [] => [[]]
  | m :: tail => (List.range (m + 1)).flatMap fun v => (residuals tail).map (v :: ·)

private theorem countChoices (values : List Nat) (tails : List (List Nat)) :
    (values.flatMap (fun v => tails.map (v :: ·))).length = values.length * tails.length := by
  induction values with
  | nil => simp
  | cons v vs ih => simp [ih, Nat.succ_mul, Nat.add_comm]

/-- A slot `(i,k)` records one bit of the remaining multiplicity of degree `i`. -/
abbrev Slot := Nat × Nat

def width (m : Nat) : Nat := if m = 0 then 0 else m.log2 + 1

def row (i m : Nat) : List Slot := (List.range (width m)).map (fun k => (i,k))

def slots (i : Nat) : List Nat → List Slot
  | [] => []
  | m :: tail => row i m ++ slots (i + 1) tail

private theorem upper_width (m : Nat) : m + 1 ≤ 2 ^ width m := by
  by_cases hm : m = 0
  · simp [hm, width]
  · simp [width, hm]
    have := Nat.lt_log2_self (n := m)
    omega

theorem residuals_le_pow_slots (i : Nat) (ms : List Nat) :
    (residuals ms).length ≤ 2 ^ (slots i ms).length := by
  induction ms generalizing i with
  | nil => simp [residuals, slots]
  | cons m tail ih =>
    rw [residuals, countChoices, List.length_range]
    simpa [slots, row, Nat.pow_add] using
      Nat.mul_le_mul (upper_width m) (ih (i+1))

private theorem slots_degree_ge {i : Nat} {ms : List Nat} {z : Slot} (hz : z ∈ slots i ms) :
    i ≤ z.1 := by
  induction ms generalizing i with
  | nil => simp [slots] at hz
  | cons m tail ih =>
    rcases List.mem_append.mp hz with h | h
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp h
      exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ i) (ih h)

private theorem slots_nodup (i : Nat) (ms : List Nat) : (slots i ms).Nodup := by
  induction ms generalizing i with
  | nil => simp [slots]
  | cons m tail ih =>
    apply List.nodup_append.mpr
    refine ⟨?_, ih (i+1), ?_⟩
    · apply List.pairwise_map.mpr
      exact List.nodup_range.imp (fun h e => h (congrArg Prod.snd e))
    · intro a ha b hb e
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
      subst b
      have := slots_degree_ge hb
      omega

def weight (z : Slot) : Nat := z.1 * 2 ^ z.2

/-- Enumerate the positive-degree slots of weight at most `h` by layers. -/
def cheap (h : Nat) : List Slot :=
  if h = 0 then [] else
    (List.range h).map (fun i => (i+1,0)) ++ (cheap (h/2)).map (fun z => (z.1,z.2+1))
termination_by h
decreasing_by omega

private theorem cheap_length (h : Nat) : (cheap h).length ≤ 2*h := by
  induction h using Nat.strongRecOn with
  | ind h ih =>
    rw [cheap]
    split
    · simp
    · simp only [List.length_append, List.length_map, List.length_range]
      have := ih (h/2) (by omega)
      omega

private theorem in_cheap {i k h : Nat} (hi : 0 < i) (hw : i * 2^k ≤ h) :
    (i,k) ∈ cheap h := by
  induction k generalizing h with
  | zero =>
    rw [cheap, ite_eq_right (by simp at hw; omega)]
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨i-1, List.mem_range.mpr (by simp at hw; omega), by simp [Nat.sub_add_cancel hi]⟩
  | succ k ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc] at hw
    have hpos := Nat.mul_pos hi (Nat.pow_pos (by decide : 0 < 2) (n := k))
    rw [cheap, ite_eq_right (by omega)]
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨(i,k), ih (h := h/2) (by omega), rfl⟩

private theorem row_mass (i w : Nat) :
    (((List.range w).map (fun k => i * 2^k)).sum) + i = i * 2^w := by
  induction w with
  | zero => simp
  | succ w ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.pow_succ, ← Nat.mul_assoc]
    omega

private theorem total_weight (i : Nat) (ms : List Nat) :
    ((slots i ms).map weight).sum ≤ 2 * mass i ms := by
  induction ms generalizing i with
  | nil => simp [slots, mass]
  | cons m tail ih =>
    have hrow : ((row i m).map weight).sum ≤ 2 * (i*m) := by
      by_cases hm : m = 0
      · simp [hm, row, width]
      · have hh := row_mass i (width m)
        have hp := Nat.mul_le_mul_left i ((Nat.le_log2 hm).mp (Nat.le_refl _))
        simp only [width, ite_eq_right hm, Nat.pow_succ, ← Nat.mul_assoc] at hh
        simp only [row, List.map_map, Function.comp_def, weight]
        simp only [width, ite_eq_right hm]
        omega
    simp only [slots, List.map_append, List.sum_append, mass, Nat.mul_add]
    exact Nat.add_le_add hrow (ih _)

private theorem charge (zs : List Slot) (h : Nat) :
    h * zs.length ≤ h * (zs.filter (fun z => decide (weight z ≤ h))).length +
      (zs.map weight).sum := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    by_cases ht : weight z ≤ h
    · simpa [ht, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        Nat.add_le_add ih (show h ≤ h + weight z by omega)
    · simp [ht, Nat.mul_add]
      omega

/-- If the positive-degree mass is at most `h²`, then the entire residual
multiplicity vector needs at most `4h` binary slots. Degree zero is separate. -/
theorem slots_length_le (ms : List Nat) (h : Nat) (hp : 0 < h) (hm : mass 1 ms ≤ h*h) :
    (slots 1 ms).length ≤ 4*h := by
  let zs := slots 1 ms
  let small := zs.filter (fun z => decide (weight z ≤ h))
  have hn : small.Nodup := List.Pairwise.filter _ (slots_nodup _ _)
  have hs : small ⊆ cheap h := by
    intro z hz
    obtain ⟨hin, hwt⟩ := List.mem_filter.mp hz
    exact in_cheap (slots_degree_ge hin) (of_decide_eq_true hwt)
  have hlen := Nat.le_trans (hn.length_le_of_subset hs) (cheap_length h)
  have hch := charge zs h
  change h * zs.length ≤ h * small.length + _ at hch
  have hm' := Nat.le_trans (total_weight 1 ms) (Nat.mul_le_mul_left 2 hm)
  have hh := Nat.add_le_add (Nat.mul_le_mul_left h hlen) hm'
  apply Nat.le_of_mul_le_mul_left (Nat.le_trans hch ?_) hp
  have e : h * (4*h) = h * (2*h) + 2*(h*h) := by grind
  rw [e]
  exact hh

/-- A fixed histogram with zero multiplicity `z` and positive-degree mass `M`
has at most `(z+1) * 2^(4*(sqrt M+1))` residual vectors. -/
theorem residual_histogram_bound (z : Nat) (ms : List Nat) :
    (residuals (z :: ms)).length ≤
      (z+1) * 2 ^ (4*((mass 1 ms).sqrt + 1)) := by
  rw [residuals, countChoices, List.length_range]
  apply Nat.mul_le_mul_left
  exact Nat.le_trans (residuals_le_pow_slots 1 ms)
    (Nat.pow_le_pow_right (by decide) (slots_length_le _ _ (by omega)
      (Nat.le_of_lt (Nat.lt_succ_sqrt _))))

end PlanarDegrees.Frontier

namespace PlanarDegrees.Frontier

/-! ## Edge updates in a triangle trace

For the invariant we keep a full inventory on permanent vertex names.
The lemma `retained_seal_iff` justifies dropping the entries for retired
vertices when testing a pair of currently available corners.
-/

/-- Ordered storage for an unordered, loop-free pair of permanent vertex names. -/
structure Edge where
  lo : Nat
  hi : Nat
  increasing : lo < hi
deriving DecidableEq

def touches (e : Edge) (v : Nat) : Bool := v == e.lo || v == e.hi

/-- A proposed color only takes effect at the first occurrence of the pair. -/
structure Event where
  edge : Edge
  red : Bool

structure Inventory where
  pending : List Edge
  sealed : List Edge
  redDegree : Nat → Nat

def empty : Inventory := ⟨[], [], fun _ => 0⟩

def tick (s : Inventory) (a : Event) : Option Inventory :=
  if a.edge ∈ s.sealed then none
  else if a.edge ∈ s.pending then
    some { s with pending := s.pending.filter (· != a.edge), sealed := a.edge :: s.sealed }
  else
    some { s with pending := a.edge :: s.pending,
                  redDegree := fun v => s.redDegree v + (a.red && touches a.edge v).toNat }

/-- In a reversed trace the newest side is the head of the list. -/
def replay : List Event → Option Inventory
  | [] => some empty
  | a :: past => (replay past).bind (tick · a)

def occurrences (past : List Event) (e : Edge) : Nat := (past.map Event.edge).count e

/-- The red edge list in the realized simple graph, computed directly from
the history using first occurrences and their colors. -/
def reds : List Event → List Edge
  | [] => []
  | a :: past =>
    if occurrences past a.edge = 0 ∧ a.red then a.edge :: reds past else reds past

def simpleDegree (edges : List Edge) (v : Nat) : Nat := edges.countP (touches · v)

theorem reds_seen {p : List Event} {e : Edge} (h : e ∈ reds p) : 0 < occurrences p e := by
  induction p with
  | nil => simp [reds] at h
  | cons a p ih =>
    simp only [reds] at h
    by_cases he : a.edge = e
    · simp [occurrences, he]
    · have ht : e ∈ reds p := by split at h <;> simpa [Ne.symm he] using h
      simpa [occurrences, he] using ih ht

theorem reds_nodup (p : List Event) : (reds p).Nodup := by
  induction p with
  | nil => simp [reds]
  | cons a p ih =>
    rw [reds]
    split
    · rename_i h
      exact List.nodup_cons.mpr ⟨fun he => by have := reds_seen he; omega, ih⟩
    · exact ih

structure Accurate (past : List Event) (s : Inventory) : Prop where
  pending : ∀ e, e ∈ s.pending ↔ occurrences past e = 1
  sealed : ∀ e, e ∈ s.sealed ↔ occurrences past e = 2
  cap : ∀ e, occurrences past e ≤ 2
  redDegree : ∀ v, s.redDegree v = simpleDegree (reds past) v

private theorem occur_cons (a : Event) (past : List Event) (e : Edge) :
    occurrences (a :: past) e = occurrences past e + (if a.edge = e then 1 else 0) := by
  by_cases h : a.edge = e <;> simp [occurrences, h]

private theorem accurate_empty : Accurate [] empty := by
  constructor <;> simp [empty, occurrences, reds, simpleDegree]

private theorem accurate_tick {past : List Event} {s t : Inventory} (hs : Accurate past s)
    {a : Event} (h : tick s a = some t) : Accurate (a :: past) t := by
  by_cases hsealed : a.edge ∈ s.sealed
  · simp [tick, hsealed] at h
  by_cases hopen : a.edge ∈ s.pending
  · have hcount := (hs.pending _).mp hopen
    simp only [tick, ite_eq_right hsealed, ite_eq_left hopen, Option.some.injEq] at h
    subst t
    constructor
    · intro e
      by_cases he : a.edge = e
      · subst e; simp [occur_cons, hcount]
      · simp [occur_cons, he, Ne.symm he, hs.pending]
    · intro e
      by_cases he : a.edge = e
      · subst e; simp [occur_cons, hcount]
      · simp [occur_cons, he, Ne.symm he, hs.sealed]
    · intro e
      by_cases he : a.edge = e
      · subst e; simp [occur_cons, hcount]
      · simpa [occur_cons, he] using hs.cap e
    · intro v
      simpa [reds, hcount] using hs.redDegree v
  · have hcount : occurrences past a.edge = 0 := by
      have h1 := mt (hs.pending a.edge).mpr hopen
      have h2 := mt (hs.sealed a.edge).mpr hsealed
      have h3 := hs.cap a.edge
      omega
    simp only [tick, ite_eq_right hsealed, ite_eq_right hopen, Option.some.injEq] at h
    subst t
    constructor
    · intro e
      by_cases he : a.edge = e
      · subst e; simp [occur_cons, hcount]
      · simp [occur_cons, he, Ne.symm he, hs.pending]
    · intro e
      by_cases he : a.edge = e
      · subst e; simp [occur_cons, hcount, hsealed]
      · simpa [occur_cons, he] using hs.sealed e
    · intro e
      by_cases he : a.edge = e
      · subst e; simp [occur_cons, hcount]
      · simpa [occur_cons, he] using hs.cap e
    · intro v
      cases hc : a.red <;> cases ht : touches a.edge v <;>
        simp [reds, hcount, hc, ht, hs.redDegree, simpleDegree]

/-- The executable transition counts red neighbors exactly once and rejects a
third use of any pair. This statement is independent of the proposed coloring
at the second occurrence. -/
theorem replay_accurate {p : List Event} {s : Inventory} (h : replay p = some s) :
    Accurate p s := by
  induction p generalizing s with
  | nil =>
    simp [replay] at h
    subst s
    exact accurate_empty
  | cons a p ih =>
    cases he : replay p with
    | none => simp [replay, he] at h
    | some t => exact accurate_tick (ih he) (by simpa [replay, he] using h)

/-- Conversely every trace with at most two visits per unordered pair passes
exactly these edge tests. Other frontier tests are treated separately. -/
theorem replay_succeeds_iff (p : List Event) :
    (∃ s, replay p = some s) ↔ ∀ e, occurrences p e ≤ 2 := by
  refine ⟨fun ⟨_,h⟩ => (replay_accurate h).cap, ?_⟩
  induction p with
  | nil => exact fun _ => ⟨empty,rfl⟩
  | cons a p ih =>
    intro hall
    obtain ⟨s, hs⟩ := ih (fun e => by have := hall e; rw [occur_cons] at this; omega)
    have hsealed : a.edge ∉ s.sealed := by
      intro he
      have hh := ((replay_accurate hs).sealed _).mp he
      have := hall a.edge
      simp [occur_cons, hh] at this
    by_cases hp : a.edge ∈ s.pending <;> simp [replay, hs, tick, hsealed, hp]

/-- A face specifies its three corners in increasing order. -/
structure Face where
  x : Nat
  y : Nat
  z : Nat
  xy : x < y
  yz : y < z
  redXY : Bool
  redXZ : Bool
  redYZ : Bool

def Face.sides (f : Face) : List Event :=
  [⟨⟨f.x,f.y,f.xy⟩,f.redXY⟩, ⟨⟨f.x,f.z,Nat.lt_trans f.xy f.yz⟩,f.redXZ⟩,
   ⟨⟨f.y,f.z,f.yz⟩,f.redYZ⟩]

theorem Face.distinct_sides (f : Face) : (f.sides.map Event.edge).Nodup := by
  have hxy := Nat.ne_of_lt f.xy
  have hyz := Nat.ne_of_lt f.yz
  simp [Face.sides, hxy, hyz]

/-- On closed, accepted traces every side is paired and the recorded degrees
are those of the loop-free simple red graph on the permanent names. -/
theorem closed_faces {faces : List Face} {s : Inventory}
    (h : replay (faces.flatMap Face.sides) = some s) (closed : s.pending = []) :
    (∀ e, occurrences (faces.flatMap Face.sides) e = 0 ∨
           occurrences (faces.flatMap Face.sides) e = 2) ∧
    (reds (faces.flatMap Face.sides)).Nodup ∧
    (∀ v, s.redDegree v = simpleDegree (reds (faces.flatMap Face.sides)) v) := by
  have H := replay_accurate h
  refine ⟨?_, reds_nodup _, H.redDegree⟩
  intro e
  have h1 := H.pending e
  have h2 := H.cap e
  simp [closed] at h1
  omega

/-- Retain sealed pairs only if both endpoints are still active. -/
def retain (active : Nat → Bool) (s : Inventory) : List Edge :=
  s.sealed.filter (fun e => active e.lo && active e.hi)

/-- A fresh corner has no old incident edge. Hence restricting the sealed
table to active endpoints preserves the rejection test for every candidate
whose corners are active or fresh. -/
theorem retained_seal_iff {active : Nat → Bool} {s : Inventory} {e : Edge}
    (available : ∀ v, touches e v → active v ∨ ∀ f ∈ s.sealed, ¬ touches f v) :
    e ∈ retain active s ↔ e ∈ s.sealed := by
  simp only [retain, List.mem_filter, Bool.and_eq_true]
  refine ⟨And.left, fun he => ⟨he, ?_, ?_⟩⟩
  · have ht : touches e e.lo := by simp [touches]
    exact (available _ ht).resolve_right fun hf => hf _ he ht
  · have ht : touches e e.hi := by simp [touches]
    exact (available _ ht).resolve_right fun hf => hf _ he ht

/-- The numerical step in the link-splitting argument. The last inequality
is the surface Euler bound after normalizing the vertex links. -/
theorem no_split_of_euler_bound {n faces edges extra : Nat}
    (hf : faces + 4 = 2*n) (he : 2*edges = 3*faces)
    (hχ : n + extra + faces ≤ edges + 2) :
    extra = 0 ∧ n + faces = edges + 2 := by omega

end PlanarDegrees.Frontier

namespace PlanarDegrees.Frontier

/-! ## Updating the partition of open sides

`α` labels previously read faces. An edge of `R` is a shared side. `P`
marks precisely the old faces that share a side with the new face. We regard
a component of a prefix as an equivalence class of `Walk R`.
-/

inductive Walk {α : Type} (R : α → α → Prop) (a : α) : α → Prop
  | refl : Walk R a a
  | step {b c : α} : Walk R a b → R b c → Walk R a c

namespace Walk

theorem trans {α : Type} {R : α → α → Prop} {a b c : α} (h : Walk R a b)
    (k : Walk R b c) : Walk R a c := by
  induction k with
  | refl => exact h
  | step _ edge ih => exact ih.step edge

theorem symm {α : Type} {R : α → α → Prop} (rs : ∀ a b, R a b → R b a)
    {a b : α} (p : Walk R a b) : Walk R b a := by
  induction p with
  | refl => exact .refl
  | step _ edge ih => exact (Walk.step Walk.refl (rs _ _ edge)).trans ih

theorem map {α β : Type} {R : α → α → Prop} {T : β → β → Prop} {a b : α}
    (f : α → β) (hf : ∀ x y, R x y → T (f x) (f y)) (p : Walk R a b) :
    Walk T (f a) (f b) := by
  induction p with
  | refl => exact .refl
  | step _ edge ih => exact ih.step (hf _ _ edge)

end Walk

/-- The dual adjacency after adjoining the single new face `none`. -/
def enlarged {α : Type} (R : α → α → Prop) (P : α → Prop) :
    Option α → Option α → Prop
  | some a, some b => R a b
  | some a, none => P a
  | none, some b => P b
  | none, none => False

def meets {α : Type} (R : α → α → Prop) (P : α → Prop) (a : α) : Prop :=
  ∃ b, Walk R a b ∧ P b

/-- The candidate partition obtained by merging all blocks that meet the new
face and leaving every other block intact. -/
def merged {α : Type} (R : α → α → Prop) (P : α → Prop) :
    Option α → Option α → Prop
  | some a, some b => Walk R a b ∨ (meets R P a ∧ meets R P b)
  | some a, none => meets R P a
  | none, some b => meets R P b
  | none, none => True

private theorem meets_back {α : Type} {R : α → α → Prop} {P : α → Prop}
    {a b : α} (p : Walk R a b) (hb : meets R P b) : meets R P a := by
  obtain ⟨u, q, hu⟩ := hb
  exact ⟨u, p.trans q, hu⟩

private theorem merged_step {α : Type} {R : α → α → Prop} {P : α → Prop}
    (rs : ∀ x y, R x y → R y x) {a b c : Option α}
    (h : merged R P a b) (e : enlarged R P b c) : merged R P a c := by
  cases a <;> cases b <;> cases c <;> simp only [merged, enlarged] at h e ⊢
  · exact ⟨_, .refl, e⟩
  · exact meets_back (.step .refl (rs _ _ e)) h
  · exact Or.inr ⟨h, _, .refl, e⟩
  · rcases h with q | ⟨ha,_⟩
    · exact ⟨_, q, e⟩
    · exact ha
  · rcases h with q | ⟨ha,hb⟩
    · exact Or.inl (q.step e)
    · exact Or.inr ⟨ha, meets_back (.step .refl (rs _ _ e)) hb⟩

private theorem to_new_face {α : Type} {R : α → α → Prop} {P : α → Prop}
    {a : α} (h : meets R P a) : Walk (enlarged R P) (some a) none := by
  obtain ⟨b,w,hb⟩ := h
  exact (w.map some (fun _ _ e => (show enlarged R P _ _ from e))).step hb

/-- Two boundary sides belong to the same new block exactly when their
incident faces are connected in the enlarged dual. The criterion also covers
an insertion that touches several pre-existing components or none at all. -/
theorem face_component_update {α : Type} {R : α → α → Prop} (P : α → Prop)
    (rs : ∀ a b, R a b → R b a) (a b : Option α) :
    Walk (enlarged R P) a b ↔ merged R P a b := by
  constructor
  · intro p
    induction p with
    | refl => cases a with
              | none => trivial
              | some a => exact Or.inl .refl
    | step _ e ih => exact merged_step rs ih e
  · have es : ∀ x y, enlarged R P x y → enlarged R P y x := by
      intro x y h
      cases x <;> cases y <;> first | exact h | exact rs _ _ h
    cases a <;> cases b <;> intro h
    · exact .refl
    · exact (to_new_face h).symm es
    · exact to_new_face h
    · rcases h with q | ⟨ha,hb⟩
      · exact q.map some (fun _ _ e => e)
      · exact (to_new_face ha).trans ((to_new_face hb).symm es)

/-- In a connected dual every proper, nonempty face component has a side
crossing its boundary. Thus a block with all its sides paired cannot survive
as a proper component of a finished connected surface. -/
theorem connected_cut_has_side {α : Type} {R : α → α → Prop}
    (connected : ∀ x y, Walk R x y) (inside : α → Prop)
    {a b : α} (ha : inside a) (hb : ¬inside b) :
    ∃ u v, inside u ∧ ¬inside v ∧ R u v := by
  classical
  apply Classical.byContradiction
  intro hnone
  apply hb
  clear hb
  have p := connected a b
  induction p with
  | refl => exact ha
  | @step u v _ e ih =>
    by_cases hc : inside v
    · exact hc
    · exact False.elim (hnone ⟨_, _, ih, hc, e⟩)

end PlanarDegrees.Frontier

namespace PlanarDegrees.Frontier

/-! ## Integer estimates for the weighted separator argument -/

/-- For a final red degree `d`, this is exactly `ceil(log₂(d+2))`, as expressed
by the two adjacent powers of two in `cost_brackets`. -/
def cost (d : Nat) := (d+1).log2+1

theorem cost_brackets (d : Nat) :
    2^(cost d - 1) < d+2 ∧ d+2 ≤ 2^cost d := by
  have h := (Nat.le_log2 (n := d+1) (by omega)).mp (Nat.le_refl _)
  have h' := Nat.lt_log2_self (n := d+1)
  simp only [cost, Nat.add_sub_cancel]
  omega

private theorem log_square (k : Nat) : (k+1)*(k+1) ≤ 9*2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    cases k with
    | zero => decide
    | succ j =>
      rw [Nat.pow_succ]
      grind

theorem cost_square (d : Nat) : cost d * cost d ≤ 9*(d+1) := by
  have h := (Nat.le_log2 (n := d+1) (by omega)).mp (Nat.le_refl _)
  exact Nat.le_trans (log_square _) (Nat.mul_le_mul_left 9 h)

def squareMass : List Nat → Nat
  | [] => 0
  | d :: ds => cost d * cost d + squareMass ds

private theorem mass_le_sum (ds : List Nat) : squareMass ds ≤ 9*(ds.sum+ds.length) := by
  induction ds with
  | nil => simp [squareMass]
  | cons d ds ih =>
    have hd := cost_square d
    simp only [squareMass, List.sum_cons, List.length_cons]
    omega

theorem total_square_mass (ds : List Nat) (h : ds.sum ≤ 6*ds.length) :
    squareMass ds ≤ 63*ds.length := by
  have := mass_le_sum ds
  omega

/-- A root-to-leaf sequence of separator costs. The two hypotheses on each
node are the outputs of the cited separator theorem, in integer form. -/
inductive SeparatorChain : Nat → List Nat → Prop
  | stop (w : Nat) : SeparatorChain w []
  | branch {w child c : Nat} {tail : List Nat}
      (budget : c*c ≤ 64*w) (half : 2*child ≤ w)
      (rest : SeparatorChain child tail) : SeparatorChain w (c :: tail)

private theorem spread (x y : Nat) : 21*(x+y)*(x+y) ≤ 70*x*x + 30*y*y := by
  have h := Int.sq_nonneg (7*(x:Int)-3*(y:Int))
  have g : (21:Int)*(x+y)*(x+y) ≤ 70*x*x + 30*y*y := by grind
  apply Int.ofNat_le.mp
  simpa only [Int.natCast_mul, Int.natCast_add, Int.cast_ofNat_Int] using g

theorem separator_chain_bound {w : Nat} {cs : List Nat} (p : SeparatorChain w cs) :
    cs.sum * cs.sum ≤ 768*w := by
  induction p with
  | stop => simp
  | @branch w child c tail budget half rest ih =>
    have h := spread c tail.sum
    simp only [List.sum_cons]
    grind

/-- The constant 220 in the face-ordering estimate with the square root
removed. The existence of a suitable separator chain is a geometric input. -/
theorem separator_cost_bound (ds : List Nat) (h : ds.sum ≤ 6*ds.length)
    {cs : List Nat} (p : SeparatorChain (squareMass ds) cs) :
    cs.sum * cs.sum ≤ 220^2 * ds.length := by
  have hm := total_square_mass ds h
  have hc := separator_chain_bound p
  omega

end PlanarDegrees.Frontier

namespace PlanarDegrees.Frontier

/-! ## Reachability after replacing states by table representatives

This argument applies to an arbitrary explicit successor generator. For the
face recurrence, equivalence means isomorphism on active names together with
equality of the global counts. The transport hypothesis below is the exact
property the face transitions must satisfy under such a renaming.
-/

namespace Table
variable {α : Type}
variable (same : α → α → Prop) [DecidableRel same]

def representative (table : List α) (s : α) : Option α :=
  table.find? (fun t => decide (same s t))

def covered (table : List α) (s : α) : Prop := ∃ t ∈ table, same s t

private theorem representative_spec {table : List α} {s t : α}
    (h : representative same table s = some t) : t ∈ table ∧ same s t :=
  ⟨List.mem_of_find?_eq_some h, of_decide_eq_true (List.find?_some (p := fun u => decide (same s u)) h)⟩

private theorem representative_exists {table : List α} {s : α}
    (h : covered same table s) : ∃ t, representative same table s = some t := by
  cases he : representative same table s with
  | some t => exact ⟨_,rfl⟩
  | none =>
    obtain ⟨t, ht, hst⟩ := h
    have hno := List.find?_eq_none.mp he t ht
    exact False.elim (hno (decide_eq_true hst))

variable [DecidableEq α]

/-- All results are taken from the fixed table, including on negative inputs. -/
def pack (table candidates : List α) : List α :=
  let names := candidates.filterMap (representative same table)
  table.filter (fun t => decide (t ∈ names))

theorem mem_pack {table candidates : List α} {t : α} :
    t ∈ pack same table candidates ↔ ∃ s ∈ candidates, representative same table s = some t := by
  constructor
  · intro h
    exact List.mem_filterMap.mp (of_decide_eq_true (List.mem_filter.mp h).2)
  · intro ⟨s, hs, ht⟩
    exact List.mem_filter.mpr ⟨(representative_spec same ht).1,
      decide_eq_true (List.mem_filterMap.mpr ⟨s, hs, ht⟩)⟩

def layer (table : List α) (next : α → List α) (seed : α) : Nat → List α
  | 0 => pack same table [seed]
  | k+1 => pack same table ((layer table next seed k).flatMap next)

/-- Concrete paths that stay inside the union of the represented classes. -/
inductive Path (table : List α) (next : α → List α) (seed : α) : Nat → α → Prop
  | start : covered same table seed → Path table next seed 0 seed
  | step {k : Nat} {s t : α} : Path table next seed k s → t ∈ next s →
      covered same table t → Path table next seed (k+1) t

theorem layer_bound (table : List α) (next : α → List α) (seed : α) (k : Nat) :
    (layer same table next seed k).length ≤ table.length := by
  cases k <;> apply List.length_filter_le

/-- Semantic soundness and completeness of first-match replacement, with no
assumption that the table entries are individually realizable. -/
theorem quotient_reachability (eqv : Equivalence same) (table : List α)
    (next : α → List α) (seed : α)
    (transport : ∀ {s u v}, same s u → v ∈ next s → ∃ w ∈ next u, same v w)
    (k : Nat) :
    (∀ t ∈ layer same table next seed k, ∃ s, Path same table next seed k s ∧ same s t) ∧
    (∀ s, Path same table next seed k s → ∃ t ∈ layer same table next seed k, same s t) := by
  induction k with
  | zero =>
    constructor
    · intro t ht
      obtain ⟨s, hs, hrep⟩ := (mem_pack same).mp ht
      simp at hs
      subst s
      obtain ⟨hin, hst⟩ := representative_spec same hrep
      exact ⟨seed, .start ⟨t,hin,hst⟩, hst⟩
    · intro s hs
      cases hs with
      | start h =>
        obtain ⟨t,ht⟩ := representative_exists same h
        exact ⟨t,(mem_pack same).mpr ⟨_, by simp, ht⟩, (representative_spec same ht).2⟩
  | succ k ih =>
    constructor
    · intro t ht
      obtain ⟨v,hv,hr⟩ := (mem_pack same).mp ht
      obtain ⟨u,hu,hvu⟩ := List.mem_flatMap.mp hv
      obtain ⟨s,hs,hsu⟩ := ih.1 _ hu
      obtain ⟨w,hw,hvw⟩ := transport (eqv.symm hsu) hvu
      obtain ⟨htin,hvt⟩ := representative_spec same hr
      have hwt := eqv.trans (eqv.symm hvw) hvt
      exact ⟨w, .step hs hw ⟨_, htin, hwt⟩, hwt⟩
    · intro s hpath
      cases hpath with
      | step hs hv hcov =>
        obtain ⟨u,hu,hxu⟩ := ih.2 _ hs
        obtain ⟨w,hw,hsw⟩ := transport hxu hv
        obtain ⟨r,hr,hsr⟩ := hcov
        obtain ⟨t,ht⟩ := representative_exists same ⟨r,hr,eqv.trans (eqv.symm hsw) hsr⟩
        exact ⟨t, (mem_pack same).mpr ⟨w, List.mem_flatMap.mpr ⟨u, hu, hw⟩, ht⟩,
          eqv.trans hsw (representative_spec same ht).2⟩

end Table

end PlanarDegrees.Frontier

namespace PlanarDegrees.Frontier

/-- Inventory lists have unique edge names. Each accepted visit contributes
exactly one to the pending count plus twice the sealed count. -/
theorem inventory_counts {p : List Event} {s : Inventory} (h : replay p = some s) :
    s.pending.Nodup ∧ s.sealed.Nodup ∧ s.pending.length + 2*s.sealed.length = p.length := by
  induction p generalizing s with
  | nil =>
    simp only [replay, Option.some.injEq] at h
    subst s
    simp [empty]
  | cons a p ih =>
    cases prev : replay p with
    | none => simp [replay,prev] at h
    | some t =>
      obtain ⟨op,cl,size⟩ := ih prev
      have hs : tick t a = some s := by simpa [replay,prev] using h
      by_cases sealed : a.edge ∈ t.sealed
      · simp [tick,sealed] at hs
      by_cases pending : a.edge ∈ t.pending
      · simp only [tick, ite_eq_right sealed, ite_eq_left pending, Option.some.injEq] at hs
        subst s
        rw [← op.erase_eq_filter, List.length_erase_of_mem pending]
        have hp := List.length_pos_of_mem pending
        exact ⟨op.erase _, List.nodup_cons.mpr ⟨sealed,cl⟩,by simp only [List.length_cons]; omega⟩
      · simp only [tick, ite_eq_right sealed, ite_eq_right pending, Option.some.injEq] at hs
        subst s
        exact ⟨List.nodup_cons.mpr ⟨pending,op⟩, cl,by simp only [List.length_cons]; omega⟩

end PlanarDegrees.Frontier

namespace PlanarDegrees.Frontier

/-! ## Size of the complete pool, including unreachable states -/

def words : Nat → List (List Bool)
  | 0 => [[]]
  | k+1 => [] :: ((words k).map (false :: ·) ++ (words k).map (true :: ·))

theorem words_spec (w : List Bool) (k : Nat) : w ∈ words k ↔ w.length ≤ k := by
  induction k generalizing w with
  | zero => simp [words]
  | succ k ih =>
    cases w with
    | nil => simp [words]
    | cons b w => cases b <;> simp [words,ih]

theorem word_count (k : Nat) : (words k).length + 1 = 2^(k+1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [words, List.length_cons, List.length_append, List.length_map, Nat.pow_succ] at *
    omega

def allowedTable {α : Type} (decode : List Bool → Option α) (budget : Nat) : List α :=
  (words budget).filterMap decode

/-- Each table record can occur together with either counter and any
coordinatewise subhistogram. This bounds the number of states before
semantics, deduplication, or rejection of false inputs. Here `h² ≥ 6n`;
one can take `h = floor(sqrt(6n))+1`. -/
theorem full_state_pool_bound {α : Type} (decode : List Bool → Option α)
    (C n h z : Nat) (ms : List Nat) (hp : 0 < h) (hsq : 6*n ≤ h*h)
    (hz : z ≤ n) (hm : mass 1 ms ≤ 6*n) :
    (allowedTable decode (C*h)).length * (residuals (z::ms)).length * (n+1) * (2*n+1)
      ≤ 2^((C+12)*h) := by
  have tableBound : (allowedTable decode (C*h)).length ≤ 2^(C*h+1) := by
    have hh := List.length_filterMap_le decode (words (C*h))
    have hw := word_count (C*h)
    change ((words (C*h)).filterMap decode).length ≤ _
    omega
  have two : h ≤ 2^h := Nat.le_of_lt Nat.lt_two_pow_self
  have powers := Nat.mul_le_mul two two
  have hi : h*h ≤ 2^(2*h) := by simpa [Nat.two_mul,Nat.pow_add] using powers
  have hn : n+1 ≤ 2^(2*h) := by
    have hpos := Nat.mul_pos hp hp
    omega
  have hz' := Nat.le_trans (Nat.add_le_add_right hz 1) hn
  have hn' : 2*n+1 ≤ 2^(2*h) := by
    have hpos := Nat.mul_pos hp hp
    omega
  have histBound : (residuals (z::ms)).length ≤ 2^(2*h)*2^(4*h) := by
    rw [residuals,countChoices,List.length_range]
    exact Nat.mul_le_mul hz' (Nat.le_trans (residuals_le_pow_slots 1 ms) <|
      Nat.pow_le_pow_right (by decide) (slots_length_le ms h hp (Nat.le_trans hm hsq)))
  have all := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul tableBound histBound) hn) hn'
  apply Nat.le_trans all
  rw [← Nat.pow_add,← Nat.pow_add,← Nat.pow_add,← Nat.pow_add]
  apply Nat.pow_le_pow_right (by decide)
  rw [Nat.add_mul]
  omega

end PlanarDegrees.Frontier

namespace PlanarDegrees.Frontier

/-! ## Ordering faces by the deepest separator containing a corner -/

def corners (a : Face) : List Nat := [a.x,a.y,a.z]
def assigned (home : Nat → Nat) (a : Face) : Nat := max (home a.x) (max (home a.y) (home a.z))

/-- `home v` is the preorder index of the separator that first contains
vertex v. Its descendants occupy the interval ending at `finish (home v)`.
In a triangle all three vertices belong to comparable recursion nodes. -/
def comparableCorners (home finish : Nat → Nat) (a : Face) : Prop :=
  ∀ x ∈ corners a, ∀ y ∈ corners a, home x ≤ home y → home y ≤ finish (home x)

private theorem corner_interval {home finish : Nat → Nat} {a : Face}
    (cmp : comparableCorners home finish a) {v : Nat} (hv : v ∈ corners a) :
    home v ≤ assigned home a ∧ assigned home a ≤ finish (home v) := by
  have hs := cmp v hv v hv (Nat.le_refl _)
  have hi (u) (hu : u ∈ corners a) : home u ≤ finish (home v) := by
    by_cases h : home v ≤ home u
    · exact cmp _ hv _ hu h
    · omega
  have hx := hi a.x (by simp [corners])
  have hy := hi a.y (by simp [corners])
  have hz := hi a.z (by simp [corners])
  simp [corners] at hv
  rcases hv with rfl|rfl|rfl <;> simp [assigned] <;> omega

/-- A live vertex lies on the current recursion path, even if the prefix
ends partway through the faces assigned to the current node. -/
theorem active_on_spine {home finish : Nat → Nat} {current v : Nat} {read next : List Face}
    (cmp : ∀ a ∈ read ++ next, comparableCorners home finish a)
    (earlier : ∀ a ∈ read, assigned home a ≤ current)
    (later : ∀ a ∈ next, current ≤ assigned home a)
    (was : ∃ a ∈ read, v ∈ corners a) (will : ∃ a ∈ next, v ∈ corners a) :
    home v ≤ current ∧ current ≤ finish (home v) := by
  obtain ⟨a,ha,hva⟩ := was
  obtain ⟨b,hb,hvb⟩ := will
  exact ⟨Nat.le_trans (corner_interval (cmp a (List.mem_append_left _ ha)) hva).1 (earlier a ha),
    Nat.le_trans (later b hb) (corner_interval (cmp b (List.mem_append_right _ hb)) hvb).2⟩

private theorem cost_mono {a b : Nat} (h : a ≤ b) : cost a ≤ cost b := by
  have ha := (Nat.le_log2 (n := a+1) (by omega)).mp (Nat.le_refl _)
  have h' := (Nat.le_log2 (n := b+1) (by omega)).mpr (Nat.le_trans ha (by omega))
  simp only [cost]
  omega

private theorem weighted_subset {xs ys : List Nat} (hu : xs.Nodup) (hv : ys.Nodup)
    (hs : xs ⊆ ys) (p q : Nat → Nat) (hle : ∀ x ∈ xs, p x ≤ q x) :
    (xs.map p).sum ≤ (ys.map q).sum := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨absent,nd⟩ := List.nodup_cons.mp hu
    have hmem := hs (List.mem_cons_self ..)
    have perm := (List.perm_cons_erase hmem).map q
    have smaller : xs ⊆ ys.erase x := by
      intro u h
      exact hv.mem_erase_iff.mpr ⟨fun eq => absent (eq ▸ h), hs (List.mem_cons_of_mem _ h)⟩
    have ht := ih nd (hv.erase _) smaller (fun u h => hle u (List.mem_cons_of_mem _ h))
    have hh := hle x (List.mem_cons_self ..)
    rw [perm.sum_nat]
    simpa using Nat.add_le_add hh ht

/-- Combine the path-containment lemma with a separator-chain budget. Here
`spine` is the concatenation of the disjoint bags on the current path. -/
theorem active_cost_bound {active spine ds : List Nat} {currentDegree finalDegree : Nat → Nat}
    (na : active.Nodup) (ns : spine.Nodup) (onPath : active ⊆ spine)
    (degree : ∀ v ∈ active, currentDegree v ≤ finalDegree v)
    {cs : List Nat} (spineCost : (spine.map (fun v => cost (finalDegree v))).sum = cs.sum)
    (total : ds.sum ≤ 6*ds.length) (p : SeparatorChain (squareMass ds) cs) :
    let used := (active.map (fun v => cost (currentDegree v))).sum
    used*used ≤ 220^2*ds.length := by
  have h := weighted_subset na ns onPath (fun x => cost (currentDegree x))
    (fun x => cost (finalDegree x)) (fun x hx => cost_mono (degree x hx))
  rw [spineCost] at h
  exact Nat.le_trans (Nat.mul_le_mul h h) (separator_cost_bound ds total p)

end PlanarDegrees.Frontier
