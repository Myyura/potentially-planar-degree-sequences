import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Basic.Real.Basic

/-! The ordered degree-balance rule, with names on the row to reconstruct
edges. New vertices are numbered in the order in which input terms are taken.
This file checks the combinatorial replay and exact degrees. -/

namespace Recognition.RowRule

structure State where
  n : Nat
  row : List Nat
  debt : Nat → Nat
  target : Nat → Nat
  neighbors : Nat → Finset Nat

def empty : State := ⟨0, [], fun _ => 0, fun _ => 0, fun _ => ∅⟩

/-- A paid interval can have zero, one or two designated ends. Each
strict interior has balance one. Either designation is allowed for a
singleton, so its residual balance may survive on either side. -/
structure Choice (s : State) (d : Nat) where
  left : List Nat
  first : List Nat
  middle : List Nat
  last : List Nat
  right : List Nat
  split : s.row = left ++ ((first ++ middle ++ last) ++ right)
  firstSize : first.length ≤ 1
  lastSize : last.length ≤ 1
  interior : ∀ v ∈ middle, s.debt v = 1
  affordable : (first ++ middle ++ last).length ≤ d

def Choice.segment {s d} (c : Choice s d) := c.first ++ c.middle ++ c.last

def Choice.newDebt {s d} (c : Choice s d) (v : Nat) : Nat :=
  if v = s.n then d - c.segment.length
  else if v ∈ c.segment then s.debt v - 1 else s.debt v

def step {s d} (c : Choice s d) : State where
  n := s.n + 1
  row := ((c.left ++ c.first ++ c.middle) ++ s.n :: (c.last ++ c.right)).filter
    (fun v => 0 < c.newDebt v)
  debt := c.newDebt
  target := fun v => if v = s.n then d else s.target v
  neighbors := fun v => if v = s.n then c.segment.toFinset
    else if v ∈ c.segment then insert s.n (s.neighbors v) else s.neighbors v

inductive Trace : List Nat → State → Prop where
  | start : Trace [] empty
  | advance {ds s d} : Trace ds s → (c : Choice s d) → Trace (ds ++ [d]) (step c)

/-- Membership in the row records exactly the vertices with outstanding
debt. At each vertex, paid incident edges and debt sum to its target. -/
structure Valid (s : State) : Prop where
  nodup : s.row.Nodup
  active : ∀ v, v ∈ s.row ↔ v < s.n ∧ 0 < s.debt v
  bounded : ∀ v < s.n, ∀ w ∈ s.neighbors v, w < s.n
  symm : ∀ v < s.n, ∀ w < s.n, w ∈ s.neighbors v ↔ v ∈ s.neighbors w
  loopless : ∀ v < s.n, v ∉ s.neighbors v
  balance : ∀ v < s.n, (s.neighbors v).card + s.debt v = s.target v

private theorem valid_empty : Valid empty := by
  constructor <;> simp [empty]

private theorem valid_step {s d} (g : Valid s) (c : Choice s d) : Valid (step c) := by
  have split : s.row = c.left ++ (c.segment ++ c.right) := c.split
  have onRow {v} (h : v ∈ c.segment) : v ∈ s.row := by simp [split, h]
  have isOld {v} (h : v ∈ c.segment) := (g.active v).1 (onRow h)
  have fresh : s.n ∉ s.row := fun h => (Nat.lt_irrefl _) ((g.active _).1 h).1
  have noNew {v} (hv : v < s.n) : s.n ∉ s.neighbors v :=
    fun h => (Nat.lt_irrefl _) (g.bounded _ hv _ h)
  have segNodup : c.segment.Nodup :=
    (List.sublist_append_left c.segment c.right).trans
      (List.sublist_append_right c.left (c.segment ++ c.right)) |>.nodup (split ▸ g.nodup)
  have rawPerm : ((c.left ++ c.first ++ c.middle) ++ s.n :: (c.last ++ c.right)).Perm
      (s.n :: s.row) := by
    simpa only [split, Choice.segment, List.append_assoc] using
      (List.perm_middle (a := s.n) (l₁ := c.left ++ c.first ++ c.middle)
        (l₂ := c.last ++ c.right))
  refine ⟨List.Nodup.filter _ (rawPerm.nodup_iff.2 (List.nodup_cons.2 ⟨fresh, g.nodup⟩)),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    change v ∈ List.filter _ _ ↔ v < s.n + 1 ∧ 0 < c.newDebt v
    simp only [List.mem_filter, decide_eq_true_eq, rawPerm.mem_iff, List.mem_cons]
    by_cases eq : v = s.n
    · simp [eq]
    by_cases paid : v ∈ c.segment
    · have hv := isOld paid
      simp [eq, onRow paid, Nat.lt_succ_of_lt hv.1]
    · rw [g.active]
      simp [Choice.newDebt, eq, paid]
      omega
  · intro v hv w hw
    change v < s.n + 1 at hv
    change w < s.n + 1
    by_cases eq : v = s.n
    · have paid : w ∈ c.segment := by simpa [step, eq] using hw
      exact Nat.lt_succ_of_lt (isOld paid).1
    have old : v < s.n := by omega
    by_cases paid : v ∈ c.segment
    · have h : w = s.n ∨ w ∈ s.neighbors v := by simpa [step, eq, paid] using hw
      rcases h with rfl | h
      · omega
      · exact Nat.lt_succ_of_lt (g.bounded _ old _ h)
    · have h : w ∈ s.neighbors v := by simpa [step, eq, paid] using hw
      exact Nat.lt_succ_of_lt (g.bounded _ old _ h)
  · intro v hv w hw
    change v < s.n + 1 at hv
    change w < s.n + 1 at hw
    by_cases ev : v = s.n <;> by_cases ew : w = s.n
    · simp [ev, ew]
    · have old : w < s.n := by omega
      by_cases pw : w ∈ c.segment <;> simp [step, ev, ew, pw, noNew old]
    · have old : v < s.n := by omega
      by_cases pv : v ∈ c.segment <;> simp [step, ev, ew, pv, noNew old]
    · have oldv : v < s.n := by omega
      have oldw : w < s.n := by omega
      by_cases pv : v ∈ c.segment <;> by_cases pw : w ∈ c.segment <;>
        simpa [step, ev, ew, pv, pw] using g.symm v oldv w oldw
  · intro v hv
    change v < s.n + 1 at hv
    by_cases eq : v = s.n
    · have unpaid : s.n ∉ c.segment := fun h => fresh (onRow h)
      simp [step, eq, unpaid]
    have old : v < s.n := by omega
    by_cases paid : v ∈ c.segment <;> simp [step, eq, paid, g.loopless v old]
  · intro v hv
    change v < s.n + 1 at hv
    by_cases eq : v = s.n
    · have affordable : c.segment.length ≤ d := c.affordable
      simpa [step, eq, Choice.newDebt, List.toFinset_card_of_nodup segNodup] using
        Nat.add_sub_of_le affordable
    have old : v < s.n := by omega
    by_cases paid : v ∈ c.segment
    · have pos := (isOld paid).2
      have oldBalance := g.balance v old
      simp [step, eq, Choice.newDebt, paid, Finset.card_insert_of_notMem (noNew old)]
      omega
    · simpa [step, eq, Choice.newDebt, paid] using g.balance v old

theorem Trace.valid {ds s} (h : Trace ds s) : Valid s := by
  induction h with
  | start => exact valid_empty
  | advance _ c ih => exact valid_step ih c

private theorem Trace.targets {ds s} (h : Trace ds s) :
    (List.ofFn fun v : Fin s.n => s.target v) = ds := by
  induction h with
  | start => rfl
  | @advance ds s d _ c ih =>
    change (List.ofFn fun v : Fin (s.n+1) => if v.val = s.n then d else s.target v) = ds ++ [d]
    rw [List.ofFn_succ']
    simp only [Fin.val_castSucc, Fin.val_last, ↓reduceIte, List.concat_eq_append]
    have old : (fun v : Fin s.n => if (v : Nat) = s.n then d else s.target v) =
        fun v : Fin s.n => s.target v := by
      funext v
      simp [Nat.ne_of_lt v.isLt]
    rw [old, ih]

/-- Every closed ordered trace, with the chosen order of the inputs,
reconstructs a finite simple graph having precisely those vertex degrees. -/
theorem closed_trace_graph {ds s} (h : Trace ds s) (closed : s.row = []) :
    ∃ G : SimpleGraph (Fin s.n), ∃ _ : DecidableRel G.Adj,
      (∀ v w : Fin s.n, G.Adj v w ↔ (w : Nat) ∈ s.neighbors v) ∧
      (List.ofFn fun v => G.degree v) = ds := by
  classical
  have g := h.valid
  let G : SimpleGraph (Fin s.n) := SimpleGraph.mk
    (fun (v w : Fin s.n) => w.val ∈ s.neighbors v)
    ⟨fun (v w : Fin s.n) => (g.symm v v.isLt w w.isLt).1⟩
    ⟨fun (v : Fin s.n) => g.loopless v v.isLt⟩
  refine ⟨G, inferInstance, fun _ _ => Iff.rfl, ?_⟩
  rw [← h.targets]
  congr 1
  funext v
  have mapNeighbors : (G.neighborFinset v).map Fin.valEmbedding = s.neighbors v := by
    ext w
    constructor
    · intro hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.1 hw
      exact (G.mem_neighborFinset v u).1 hu
    · intro hw
      let u : Fin s.n := ⟨w, g.bounded v v.isLt w hw⟩
      exact Finset.mem_map.2 ⟨u, (G.mem_neighborFinset v u).2 hw, rfl⟩
  have zero : s.debt v = 0 := by
    by_contra! pos
    have mem := (g.active v).2 ⟨v.isLt, Nat.pos_of_ne_zero pos⟩
    simp [closed] at mem
  rw [← G.card_neighborFinset_eq_degree, ← Finset.card_map Fin.valEmbedding, mapNeighbors]
  simpa [zero] using g.balance v v.isLt

theorem closed_trace_degrees {ds s} (h : Trace ds s) (closed : s.row = []) :
    ∃ G : SimpleGraph (Fin s.n), ∃ _ : DecidableRel G.Adj,
      (List.ofFn fun v => G.degree v) = ds := by
  obtain ⟨G, dec, _, degrees⟩ := closed_trace_graph h closed
  exact ⟨G, dec, degrees⟩

def State.balances (s : State) := s.row.map s.debt

/-- A move on integers alone. No vertex names or graph occur in this relation. -/
structure NumericalMove (row : List Nat) (d : Nat) where
  left : List Nat
  first : List Nat
  middle : List Nat
  last : List Nat
  right : List Nat
  split : row = left ++ ((first ++ middle ++ last) ++ right)
  firstSize : first.length ≤ 1
  lastSize : last.length ≤ 1
  interior : ∀ x ∈ middle, x = 1
  affordable : (first ++ middle ++ last).length ≤ d

def NumericalMove.next {row d} (m : NumericalMove row d) : List Nat :=
  (m.left ++ (m.first ++ m.middle).map (· - 1) ++
    (d - (m.first ++ m.middle ++ m.last).length) ::
      (m.last.map (· - 1) ++ m.right)).filter (fun x => 0 < x)

inductive NumericalTrace : List Nat → List Nat → Prop where
  | start : NumericalTrace [] []
  | advance {ds row d} : NumericalTrace ds row → (m : NumericalMove row d) →
      NumericalTrace (ds ++ [d]) m.next

def Choice.project {s d} (c : Choice s d) : NumericalMove s.balances d where
  left := c.left.map s.debt
  first := c.first.map s.debt
  middle := c.middle.map s.debt
  last := c.last.map s.debt
  right := c.right.map s.debt
  split := by simp [State.balances, c.split]
  firstSize := by simpa using c.firstSize
  lastSize := by simpa using c.lastSize
  interior := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    exact c.interior v hv
  affordable := by simpa using c.affordable

private theorem project_step {s d} (g : Valid s) (c : Choice s d) :
    (step c).balances = c.project.next := by
  have split : s.row = c.left ++ (c.segment ++ c.right) := c.split
  have outer := List.nodup_append.1 (split ▸ g.nodup)
  have inner := List.nodup_append.1 outer.2.1
  have old {v} (h : v ∈ s.row) : v ≠ s.n := Nat.ne_of_lt ((g.active v).1 h).1
  have clear (l : List Nat) (hrow : ∀ v ∈ l, v ∈ s.row)
      (hskip : ∀ v ∈ l, v ∉ c.segment) :
      l.map c.newDebt = l.map s.debt :=
    List.map_congr_left fun v hv => by simp [Choice.newDebt, old (hrow v hv), hskip v hv]
  have left := clear c.left (fun _ h => by simp [split, h])
    (fun v h hp => outer.2.2 v h v (by simp [hp]) rfl)
  have right := clear c.right (fun _ h => by simp [split, h])
    (fun v h hp => inner.2.2 v hp v h rfl)
  have charge (l : List Nat) (sub : ∀ v ∈ l, v ∈ c.segment) :
      l.map c.newDebt = (l.map s.debt).map (· - 1) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro v hv
    have paid := sub v hv
    have hr : v ∈ s.row := by simp [split, paid]
    simp [Choice.newDebt, old hr, paid]
  have front := charge (c.first ++ c.middle) (fun _ h => List.mem_append_left _ h)
  have last := charge c.last (fun _ h => List.mem_append_right _ h)
  have clean (l : List Nat) : (l.filter (fun v => 0 < c.newDebt v)).map c.newDebt =
      (l.map c.newDebt).filter (fun x => 0 < x) :=
    (List.filter_map (p := fun x : Nat => decide (0 < x)) (f := c.newDebt) (l := l)).symm
  change (List.map c.newDebt (List.filter _ _)) = _
  rw [clean]
  rw [show c.left ++ c.first ++ c.middle = c.left ++ (c.first ++ c.middle) from
    List.append_assoc .., List.map_append, List.map_append, left, front, List.map_cons,
    (List.map_append (f := c.newDebt) (l₁ := c.last) (l₂ := c.right)), right, last]
  simp [NumericalMove.next, Choice.project, Choice.newDebt, Choice.segment, List.append_assoc]

private theorem lift_move {s row d} (hr : s.balances = row) (m : NumericalMove row d) :
    ∃ c : Choice s d, c.project.next = m.next := by
  obtain ⟨l, tail, split, hl, ht⟩ := List.map_eq_append_iff.1 (hr.trans m.split)
  obtain ⟨seg, r, htail, hseg, hright⟩ := List.map_eq_append_iff.1 ht
  obtain ⟨fm, b, eqseg, hfm, hb⟩ := List.map_eq_append_iff.1 hseg
  obtain ⟨a, mid, eqfm, ha, hmid⟩ := List.map_eq_append_iff.1 hfm
  let c : Choice s d := {
    left := l, first := a, middle := mid, last := b, right := r
    split := by rw [split, htail, eqseg, eqfm]
    firstSize := by simpa [← ha] using m.firstSize
    lastSize := by simpa [← hb] using m.lastSize
    interior := fun v hv => m.interior _ (hmid ▸ List.mem_map_of_mem hv)
    affordable := by simpa [← ha, ← hmid, ← hb] using m.affordable }
  exact ⟨c, by simp [NumericalMove.next, Choice.project, c, hl, ha, hmid, hb, hright]⟩

/-- Forgetting names loses no run of the integer rule, even when balances
repeat. In a lifted run the old names follow the same positions throughout. -/
theorem numerical_trace_iff {ds row} :
    NumericalTrace ds row ↔ ∃ s, Trace ds s ∧ s.balances = row := by
  constructor
  · intro h
    induction h with
    | start => exact ⟨empty, .start, rfl⟩
    | advance _ m ih =>
      obtain ⟨s, tr, eq⟩ := ih
      obtain ⟨c, next⟩ := lift_move eq m
      exact ⟨step c, .advance tr c, (project_step tr.valid c).trans next⟩
  · rintro ⟨s, tr, rfl⟩
    induction tr with
    | start => exact .start
    | advance tr c ih =>
      rw [project_step tr.valid c]
      exact .advance ih c.project

private theorem on_input_vertices {ds : List Nat} {n : Nat} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (degs : (List.ofFn fun v => G.degree v) = ds) :
    ∃ H : SimpleGraph (Fin ds.length), ∃ _ : DecidableRel H.Adj,
      (List.ofFn fun v => H.degree v) = ds := by
  have size : n = ds.length := by simpa using congrArg List.length degs
  subst n
  exact ⟨G, inferInstance, degs⟩

/-- A successful run of the entirely numerical rule yields an ordinary
simple graph on exactly the input vertices, with this exact degree list. -/
theorem successful_numerical_trace_graph {ds : List Nat} (h : NumericalTrace ds []) :
    ∃ G : SimpleGraph (Fin ds.length), ∃ _ : DecidableRel G.Adj,
      (List.ofFn fun v => G.degree v) = ds := by
  obtain ⟨s, tr, finish⟩ := numerical_trace_iff.1 h
  obtain ⟨G, dec, degrees⟩ := closed_trace_degrees tr (List.map_eq_nil_iff.1 finish)
  let _ := dec
  exact on_input_vertices G degrees

private def activePart (l : List Nat) := l.filter (fun x => 0 < x)

private def paidEnd (x : Nat) (pay : Bool) : List Nat := if pay then [x] else []
private def unchargedEnd (x : Nat) (pay : Bool) : List Nat :=
  if pay then [] else activePart [x]

/-- The contour of a canonical sweep also contains vertices of balance zero.
Only two old ends survive a covered path. At each end the attaching edge may
be black. Every positive interior balance must pay its last edge now. -/
structure SweepMove (contour : List Nat) (d : Nat) where
  left : List Nat
  a : Nat
  middle : List Nat
  b : Nat
  right : List Nat
  split : contour = left ++ a :: (middle ++ b :: right)
  payA : Bool
  payB : Bool
  endA : payA = true → 0 < a
  endB : payB = true → 0 < b
  finalInterior : ∀ x ∈ middle, x ≤ 1
  affordable : (paidEnd a payA ++ activePart middle ++ paidEnd b payB).length ≤ d

private def SweepMove.cost {contour d} (m : SweepMove contour d) :=
  (paidEnd m.a m.payA ++ activePart m.middle ++ paidEnd m.b m.payB).length

def SweepMove.next {contour d} (m : SweepMove contour d) : List Nat :=
  m.left ++ [m.a - (if m.payA then 1 else 0), d - m.cost,
             m.b - (if m.payB then 1 else 0)] ++ m.right

private theorem SweepMove.project {contour d} (m : SweepMove contour d) :
    ∃ u : NumericalMove (activePart contour) d, u.next = activePart m.next := by
  have leftSplit : activePart [m.a] = unchargedEnd m.a m.payA ++ paidEnd m.a m.payA := by
    cases h : m.payA with
    | false => simp [unchargedEnd, paidEnd]
    | true => simp [unchargedEnd, paidEnd, activePart, m.endA h]
  have rightSplit : activePart [m.b] = paidEnd m.b m.payB ++ unchargedEnd m.b m.payB := by
    cases h : m.payB with
    | false => simp [unchargedEnd, paidEnd]
    | true => simp [unchargedEnd, paidEnd, activePart, m.endB h]
  have interior (x) (hx : x ∈ activePart m.middle) : x = 1 := by
    obtain ⟨mem, pos⟩ := List.mem_filter.1 hx
    have upper := m.finalInterior x mem
    simp at pos
    omega
  let u : NumericalMove (activePart contour) d := {
    left := activePart m.left ++ unchargedEnd m.a m.payA
    first := paidEnd m.a m.payA
    middle := activePart m.middle
    last := paidEnd m.b m.payB
    right := unchargedEnd m.b m.payB ++ activePart m.right
    split := by
      refine (congrArg activePart m.split).trans ?_
      rw [show m.a :: (m.middle ++ m.b :: m.right) =
        [m.a] ++ (m.middle ++ ([m.b] ++ m.right)) by rfl]
      simp only [activePart, List.filter_append]
      change _ ++ (activePart [m.a] ++ (_ ++ (activePart [m.b] ++ _))) = _
      rw [leftSplit, rightSplit]
      simp only [List.append_assoc]
    firstSize := by cases h : m.payA <;> simp [paidEnd]
    lastSize := by cases h : m.payB <;> simp [paidEnd]
    interior := interior
    affordable := m.affordable }
  have dead : ((activePart m.middle).map (· - 1)).filter (fun x => 0 < x) = [] := by
    apply List.filter_eq_nil_iff.2
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    simp [interior y hy]
  refine ⟨u, ?_⟩
  cases a : m.payA <;> cases b : m.payB <;>
    simp [u, NumericalMove.next, SweepMove.next, SweepMove.cost, paidEnd, unchargedEnd,
      a, b, List.filter_append, activePart, List.append_assoc,
      show ((m.middle.filter (fun x => 0 < x)).map (· - 1)).filter (fun x => 0 < x) = []
        from dead, List.filter_cons] <;> split_ifs <;> simp_all

/-- Two zero sentinels allow the first isolated point or base edge to be
started at either end. All subsequent sweeps use the same two-ended rule. -/
inductive SweepTrace : List Nat → List Nat → Prop where
  | start : SweepTrace [] [0, 0]
  | advance {ds contour d} : SweepTrace ds contour → (m : SweepMove contour d) →
      SweepTrace (ds ++ [d]) m.next

/-- Deleting exhausted contour vertices in any canonical sweep gives a
legal run of the integer rule, including moves with no red old neighbors. -/
theorem sweep_projects {ds contour} (h : SweepTrace ds contour) :
    NumericalTrace ds (contour.filter (fun x => 0 < x)) := by
  induction h with
  | start => exact .start
  | advance _ m ih =>
    obtain ⟨u, outcome⟩ := m.project
    rw [show m.next.filter (fun x => 0 < x) = u.next from outcome.symm]
    exact .advance ih u

/-- Ports below and above one fan. The new vertex occupies upper port
`left+1`; the two old ends may have surviving wires on its two sides. -/
inductive StripArc (left width : Nat) : Nat → Nat → Prop where
  | before {i} : i < left → StripArc left width i i
  | first : 0 < width → StripArc left width left left
  | paid {j} : j < width → StripArc left width (left+j) (left+1)
  | last : 0 < width → StripArc left width (left+width-1) (left+2)
  | after (j) : StripArc left width (left+width+j) (left+3+j)

private theorem strip_monotone {l w i j k m : Nat} (a : StripArc l w i j)
    (b : StripArc l w k m) (h : i < k) : j ≤ m := by
  cases a <;> cases b <;> omega

/-- Actual x-coordinate at height t of the segment with endpoints
(i,0) and (j,1), in the real plane. -/
def stripX (i j : Nat) (t : ℝ) : ℝ := (1 - t) * i + t * j

private theorem strip_strict {l w i j k m} (a : StripArc l w i j)
    (b : StripArc l w k m) (h : i < k) {t : ℝ} (ht : 0 < t) (h1 : t < 1) :
    stripX i j t < stripX k m t := by
  have lbase : (i : ℝ) < k := by exact_mod_cast h
  have ltip : (j : ℝ) ≤ m := by exact_mod_cast strip_monotone a b h
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left lbase (sub_pos.2 h1))
    (mul_le_mul_of_nonneg_left ltip ht.le)

/-- Straight segments permitted by a fan can meet in its open horizontal
strip only when the two segments have identical endpoints. -/
theorem fan_segments_disjoint {l w i j k m} (a : StripArc l w i j)
    (b : StripArc l w k m) {t : ℝ} (ht : 0 < t) (h1 : t < 1)
    (meet : stripX i j t = stripX k m t) : i = k ∧ j = m := by
  have eq : i = k := by
    rcases lt_trichotomy i k with h | h | h
    · exact False.elim ((strip_strict a b h ht h1).ne meet)
    · exact h
    · exact False.elim ((strip_strict b a h ht h1).ne meet.symm)
  subst k
  refine ⟨rfl, ?_⟩
  have prod : t * (j : ℝ) = t * m := add_left_cancel (show
    (1-t) * (i : ℝ) + t * j = (1-t) * (i : ℝ) + t * m from meet)
  have cast : (j : ℝ) = m := mul_left_cancel₀ ht.ne' prod
  exact_mod_cast cast

/-- A labelled segment is either an edge from a paid vertex to the new
vertex, or the continuation of a named old vertex across the strip. -/
inductive Stroke {s d} (c : Choice s d) : Nat → Nat → Nat → Nat → Prop where
  | before {v} : v ∈ c.left → Stroke c (c.left.idxOf v) (c.left.idxOf v) v v
  | first {v} : v ∈ c.first → Stroke c c.left.length c.left.length v v
  | paid {v} : v ∈ c.segment →
      Stroke c (c.left.length + c.segment.idxOf v) (c.left.length + 1) v s.n
  | last {v} : v ∈ c.last →
      Stroke c (c.left.length + c.segment.length - 1) (c.left.length + 2) v v
  | after {v} : v ∈ c.right →
      Stroke c (c.left.length + c.segment.length + c.right.idxOf v)
        (c.left.length + 3 + c.right.idxOf v) v v

theorem Stroke.arc {s d} {c : Choice s d} {i j v u} (e : Stroke c i j v u) :
    StripArc c.left.length c.segment.length i j := by
  cases e with
  | before h => exact .before (List.idxOf_lt_length_iff.2 h)
  | first h => exact .first (List.length_pos_of_mem (List.mem_append_left _
      (List.mem_append_left _ h) : _ ∈ c.segment))
  | paid h => exact .paid (List.idxOf_lt_length_iff.2 h)
  | last h => exact .last (List.length_pos_of_mem (List.mem_append_right _ h : _ ∈ c.segment))
  | after => exact .after _

/-- These segments include each newly reconstructed edge, and a vertical
or slanted continuation for every old vertex still on the open contour. -/
theorem fan_strip_covers_step {s d} (c : Choice s d) :
    (∀ v ∈ c.segment, ∃ i j, Stroke c i j v s.n) ∧
    ∀ v ∈ (step c).row, v ≠ s.n → ∃ i j, Stroke c i j v v := by
  refine ⟨fun _ h => ⟨_, _, .paid h⟩, ?_⟩
  intro v hv old
  obtain ⟨raw, owes⟩ := List.mem_filter.1 hv
  simp only [List.mem_append, List.mem_cons] at raw
  rcases raw with ((left | first) | mid) | (fresh | last | right)
  · exact ⟨_, _, .before left⟩
  · exact ⟨_, _, .first first⟩
  · have paid : v ∈ c.segment := List.mem_append_left _ (List.mem_append_right _ mid)
    have debt := c.interior v mid
    simp [Choice.newDebt, old, paid, debt] at owes
  · exact (old fresh).elim
  · exact ⟨_, _, .last last⟩
  · exact ⟨_, _, .after right⟩

/-- Empty upper slots distinguish missing endpoints; the middle slot always
names the new vertex, including when its balance is already exhausted. -/
def Choice.upper {s d} (c : Choice s d) : List (Option Nat) :=
  c.left.map some ++ ([c.first.head?, some s.n, c.last.head?] ++ c.right.map some)

private theorem at_offset {α : Type} (a b : List α) (i : Nat) :
    (a ++ b)[a.length+i]? = b[i]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

private theorem short_of_mem {l : List Nat} {v : Nat} (hl : l.length ≤ 1) (hv : v ∈ l) :
    l = [v] := by
  cases l with
  | nil => simp at hv
  | cons a r =>
    cases r with
    | nil => simp at hv; simp [hv]
    | cons => simp at hl

/-- Both ends of each segment are attached to the named vertex at their
port. A shared endpoint of two segments therefore has one vertex name. -/
theorem Stroke.ports {s d} {c : Choice s d} {i j v u} (e : Stroke c i j v u) :
    s.row[i]? = some v ∧ (c.upper[j]?).join = some u := by
  have split : s.row = c.left ++ (c.segment ++ c.right) := c.split
  have cap : ∀ k, c.upper[c.left.length+k]? =
      ([c.first.head?, some s.n, c.last.head?] ++ c.right.map some)[k]? := by
    intro k
    simpa [Choice.upper] using
      at_offset (c.left.map some) ([c.first.head?, some s.n, c.last.head?] ++ c.right.map some) k
  cases e with
  | before h =>
    have range := List.idxOf_lt_length_iff.2 h
    constructor
    · rw [split, List.getElem?_append_left range, List.getElem?_idxOf h]
    · simp [Choice.upper, List.getElem?_append_left (by simpa using range :
        c.left.idxOf _ < (c.left.map some).length), List.getElem?_idxOf h]
  | @first v h =>
    have one := short_of_mem c.firstSize h
    constructor
    · rw [split]
      simp [Choice.segment, one, List.append_assoc]
    · simpa [one] using congrArg Option.join (cap 0)
  | paid h =>
    have inSeg := List.idxOf_lt_length_iff.2 h
    constructor
    · rw [split, at_offset, List.getElem?_append_left inSeg, List.getElem?_idxOf h]
    · simpa using congrArg Option.join (cap 1)
  | @last v h =>
    have one := short_of_mem c.lastSize h
    let fm := c.first ++ c.middle
    have size : c.segment.length = fm.length+1 := by simp [Choice.segment, fm, one, Nat.add_assoc]
    have which : (c.segment ++ c.right)[fm.length]? = some v := by
      simp [Choice.segment, fm, one, List.append_assoc]
    constructor
    · rw [split, size, show c.left.length+(fm.length+1)-1 = c.left.length+fm.length by omega,
        at_offset, which]
    · simpa [one] using congrArg Option.join (cap 2)
  | @after v h =>
    constructor
    · rw [split, Nat.add_assoc, at_offset, at_offset, List.getElem?_idxOf h]
    · rw [Nat.add_assoc, cap]
      simp [Nat.add_comm 3, List.getElem?_idxOf h]

private theorem head_toList {l : List Nat} (len : l.length ≤ 1) : l.head?.toList = l := by
  cases l with
  | nil => rfl
  | cons a r => cases r with
    | nil => rfl
    | cons => simp at len

/-- Reading the upper ports from left to right, and removing exhausted
vertices and empty ports, recovers the next row with its vertex order. -/
theorem upper_ports_row {s d} (g : Valid s) (c : Choice s d) :
    ((c.upper.filterMap id).filter (fun v => 0 < c.newDebt v)) = (step c).row := by
  have unpack (x : Option Nat) (l : List (Option Nat)) :
      (x :: l).filterMap id = x.toList ++ l.filterMap id := by cases x <;> simp
  have dead : c.middle.filter (fun v => 0 < c.newDebt v) = [] := by
    apply List.filter_eq_nil_iff.2
    intro v hv
    have paid : v ∈ c.segment := List.mem_append_left _ (List.mem_append_right _ hv)
    by_cases fresh : v = s.n
    · subst v
      have inRow : s.n ∈ s.row := by simp [c.split, hv]
      exact ((Nat.lt_irrefl _) ((g.active _).1 inRow).1).elim
    · simp [Choice.newDebt, fresh, paid, c.interior v hv]
  have up : c.upper.filterMap id =
      c.left ++ (c.first ++ s.n :: (c.last ++ c.right)) := by
    unfold Choice.upper
    rw [List.filterMap_append]
    change _ ++ (c.first.head? :: some s.n :: c.last.head? :: c.right.map some).filterMap id = _
    rw [unpack, unpack, unpack, head_toList c.firstSize, head_toList c.lastSize]
    simp
  rw [up]
  simp [step, dead, List.append_assoc]

/-- A second, empty strip closes up unused ports. The kth nonempty
source port goes to the kth position of the next dense row. -/
inductive Repack : List (Option Nat) → Nat → Nat → Nat → Prop where
  | head {xs v} : Repack (some v :: xs) 0 0 v
  | gap {xs i j v} : Repack xs i j v → Repack (none :: xs) (i+1) j v
  | keep {xs i j v w} : Repack xs i j v → Repack (some w :: xs) (i+1) (j+1) v

theorem Repack.ports {xs i j v} (e : Repack xs i j v) :
    xs[i]? = some (some v) ∧ (xs.filterMap id)[j]? = some v := by
  induction e with
  | head => simp
  | gap _ ih => simpa using ih
  | keep _ ih => simpa using ih

theorem Repack.from_source {xs : List (Option Nat)} {i v}
    (live : xs[i]? = some (some v)) : ∃ j, Repack xs i j v := by
  induction xs generalizing i with
  | nil => simp at live
  | cons h xs ih =>
    cases i with
    | zero =>
      have eq : h = some v := by simpa using live
      subst h
      exact ⟨0, .head⟩
    | succ i =>
      obtain ⟨j, e⟩ := ih (i := i) (by simpa using live)
      cases h with
      | none => exact ⟨j, .gap e⟩
      | some => exact ⟨j+1, .keep e⟩

theorem Repack.to_target {xs : List (Option Nat)} {j v}
    (live : (xs.filterMap id)[j]? = some v) : ∃ i, Repack xs i j v := by
  induction xs generalizing j with
  | nil => simp at live
  | cons h xs ih =>
    cases h with
    | none =>
      obtain ⟨i, e⟩ := ih (by simpa using live)
      exact ⟨i+1, .gap e⟩
    | some w =>
      cases j with
      | zero =>
        have eq : w = v := by simpa using live
        subst w
        exact ⟨0, .head⟩
      | succ j =>
        obtain ⟨i, e⟩ := ih (j := j) (by simpa using live)
        exact ⟨i+1, .keep e⟩

theorem Repack.ordered {xs i j v} (e : Repack xs i j v) {k m u}
    (f : Repack xs k m u) (lt : i < k) : j < m := by
  induction e generalizing k m u with
  | head => cases f <;> omega
  | gap _ ih =>
    cases f with
    | gap f => exact ih f (by omega)
  | keep _ ih =>
    cases f with
    | head => omega
    | keep f => exact Nat.succ_lt_succ (ih f (by omega))

theorem repack_segments_disjoint {xs i j k m v u}
    (a : Repack xs i j v) (b : Repack xs k m u) {t : ℝ} (ht : 0 < t) (h1 : t < 1)
    (meet : stripX i j t = stripX k m t) : i = k ∧ j = m ∧ v = u := by
  have strict {i j k m v u} (a : Repack xs i j v) (b : Repack xs k m u) (lt : i < k) :
      stripX i j t < stripX k m t := by
    have hx : (i : ℝ) < k := by exact_mod_cast lt
    have hy : (j : ℝ) < m := by exact_mod_cast a.ordered b lt
    exact add_lt_add (mul_lt_mul_of_pos_left hx (sub_pos.2 h1)) (mul_lt_mul_of_pos_left hy ht)
  have eq : i = k := by
    rcases lt_trichotomy i k with lt | eq | gt
    · exact ((strict a b lt).ne meet).elim
    · exact eq
    · exact ((strict b a gt).ne meet.symm).elim
  subst k
  have prod : t * (j : ℝ) = t * m := add_left_cancel (show
    (1-t) * (i : ℝ) + t * j = (1-t) * (i : ℝ) + t * m from meet)
  have cast : (j : ℝ) = m := mul_left_cancel₀ ht.ne' prod
  exact ⟨rfl, by exact_mod_cast cast, Option.some.inj (Option.some.inj (a.ports.1.symm.trans b.ports.1))⟩

def Choice.livePorts {s d} (c : Choice s d) := c.upper.map
  (fun v => v.bind (fun u => if 0 < c.newDebt u then some u else none))

theorem repack_rows {s d} (g : Valid s) (c : Choice s d) :
    c.livePorts.filterMap id = (step c).row := by
  rw [← upper_ports_row g c]
  unfold Choice.livePorts
  generalize c.upper = slots
  induction slots with
  | nil => rfl
  | cons h slots ih =>
    cases h with
    | none => simpa using ih
    | some w =>
      by_cases owing : 0 < c.newDebt w <;> simp_all

/-- Every surviving name has a straight continuation to its exact position
on the next contour. The connecting strip keeps the order proved above. -/
theorem next_port_connected {s d} (g : Valid s) (c : Choice s d) {j v}
    (next : (step c).row[j]? = some v) :
    ∃ i, Repack c.livePorts i j v ∧ c.upper[i]? = some (some v) := by
  obtain ⟨i, e⟩ := Repack.to_target ((repack_rows g c) ▸ next)
  refine ⟨i, e, ?_⟩
  have src := e.ports.1
  simp only [Choice.livePorts, List.getElem?_map] at src
  cases q : c.upper[i]? with
  | none => simp [q] at src
  | some h =>
    cases h with
    | none => simp [q] at src
    | some w =>
      by_cases owing : 0 < c.newDebt w <;> simp_all

/-- The two strips of one step, with the same coordinate at each named
common port. Equal heights in distinct open strips never occur after the
strips are translated to successive unit height intervals. -/
structure DrawnStep {s d} (c : Choice s d) : Prop where
  edges : ∀ v ∈ c.segment, ∃ i j, Stroke c i j v s.n
  continuing : ∀ v ∈ (step c).row, v ≠ s.n → ∃ i j, Stroke c i j v v
  fanMeeting : ∀ {i j k m v u x y} (_ : Stroke c i j v u) (_ : Stroke c k m x y)
    {t : ℝ}, 0 < t → t < 1 → stripX i j t = stripX k m t →
    i = k ∧ j = m ∧ v = x ∧ u = y
  nextContour : ∀ {j v}, (step c).row[j]? = some v →
    ∃ i, Repack c.livePorts i j v ∧ c.upper[i]? = some (some v)
  repackMeeting : ∀ {i j k m v u}, Repack c.livePorts i j v → Repack c.livePorts k m u →
    ∀ {t : ℝ}, 0 < t → t < 1 → stripX i j t = stripX k m t →
      i = k ∧ j = m ∧ v = u

theorem drawn_step {s d} (g : Valid s) (c : Choice s d) : DrawnStep c := by
  refine ⟨(fan_strip_covers_step c).1, (fan_strip_covers_step c).2, ?_,
    fun h => next_port_connected g c h, repack_segments_disjoint⟩
  intro i j k m v u x y a b t ht h1 meet
  obtain ⟨rfl, rfl⟩ := fan_segments_disjoint a.arc b.arc ht h1 meet
  exact ⟨rfl, rfl, Option.some.inj (a.ports.1.symm.trans b.ports.1),
    Option.some.inj (a.ports.2.symm.trans b.ports.2)⟩

/-- Each step has its geometric strips; at each interface the common named
row is identical and in the same order. -/
inductive DrawnTrace : List Nat → State → Prop where
  | start : DrawnTrace [] empty
  | advance {ds s d} : DrawnTrace ds s → (c : Choice s d) → DrawnStep c →
      DrawnTrace (ds ++ [d]) (step c)

theorem Trace.drawn {ds s} (h : Trace ds s) : DrawnTrace ds s := by
  induction h with
  | start => exact .start
  | advance prev c ih => exact .advance ih c (drawn_step prev.valid c)

/-- The graph and the geometric strip history are on the very same vertex
names. The outer-face-to-rotation and canonical-order bridges are separate
topological statements. -/
theorem successful_trace_drawn_replay {ds : List Nat} (h : NumericalTrace ds []) :
    ∃ s, DrawnTrace ds s ∧ s.row = [] ∧
      ∃ G : SimpleGraph (Fin s.n), ∃ _ : DecidableRel G.Adj,
        (∀ v w : Fin s.n, G.Adj v w ↔ (w : Nat) ∈ s.neighbors v) ∧
        (List.ofFn fun v => G.degree v) = ds := by
  obtain ⟨s, tr, done⟩ := numerical_trace_iff.1 h
  have closed := List.map_eq_nil_iff.1 done
  obtain ⟨G, dec, adj, degrees⟩ := closed_trace_graph tr closed
  exact ⟨s, tr.drawn, closed, G, dec, adj, degrees⟩

end Recognition.RowRule
