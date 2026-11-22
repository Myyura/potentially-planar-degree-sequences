import RowResult
import GraphCounts
import MaximalPlane

/-! Projecting a canonical shelling of a host graph onto arbitrary red
edges. The certificate uses vertex names and host adjacency only. All
balances are computed by counting neighbors later in that very order. -/
namespace Recognition.CanonicalRow
open RowRule SimpleGraph

/-- Two extra end slots initialize the first vertex and the base edge.
The contour stores a simple path of real exposed vertices. -/
structure Cover {V : Type*} (T : SimpleGraph V) (seen : List V)
    (contour : List (Option V)) (v : V) (future : List V) where
  left : List (Option V)
  a : Option V
  middle : List (Option V)
  b : Option V
  right : List (Option V)
  split : contour = left ++ a :: (middle ++ b :: right)
  simplePath : (contour.filterMap id).Nodup
  previouslySeen : ∀ w, some w ∈ contour → w ∈ seen
  oldNeighbors : ∀ w, w ∈ seen ∧ T.Adj w v ↔ some w ∈ a :: (middle ++ [b])
  retired : ∀ w, some w ∈ middle → ∀ z ∈ future, ¬ T.Adj w z

def Cover.next {V T seen contour v future} (c : @Cover V T seen contour v future) :=
  c.left ++ [c.a, some v, c.b] ++ c.right

/-- A shelling of the host, in chronological vertex order. No degrees or
red-edge data occur in its definition. -/
inductive Sweep {V : Type*} (T : SimpleGraph V) :
    List V → List (Option V) → List V → Prop where
  | done {seen contour} : Sweep T seen contour []
  | step {seen contour v future} : (c : Cover T seen contour v future) →
      Sweep T (seen ++ [v]) c.next future → Sweep T seen contour (v :: future)

structure CanonicalOrder {V : Type*} (T : SimpleGraph V) where
  vertices : List V
  distinct : vertices.Nodup
  complete : ∀ v, v ∈ vertices
  sweep : Sweep T [] [none, none] vertices

/-- The choice of outer face and its opposite base edge fixes the last
vertex of a host canonical order. -/
def EndsAt {V} {T : SimpleGraph V} (C : CanonicalOrder T) (v : V) :=
  C.vertices.getLast? = some v

private theorem mem_real {V : Type*} (l : List (Option V)) (v : V) :
    v ∈ l.filterMap id ↔ some v ∈ l := by
  simp [List.mem_filterMap]

private def Cover.block {V T seen contour v future} (c : @Cover V T seen contour v future) :=
  c.a :: (c.middle ++ [c.b])

private theorem block_shape {V T seen contour v future} (c : @Cover V T seen contour v future) :
    contour = c.left ++ (c.block ++ c.right) := by
  simp [c.split,Cover.block,List.append_assoc]

private theorem cover_parts {V T seen contour v future} (c : @Cover V T seen contour v future) :
    (c.block.filterMap id).Nodup ∧
    ∀ w, some w ∈ c.left ++ c.right → ¬T.Adj w v := by
  have nd := c.simplePath
  rw [block_shape c,List.filterMap_append,List.filterMap_append] at nd
  obtain ⟨_,tail,separate⟩ := List.nodup_append.1 nd
  obtain ⟨single,_,right⟩ := List.nodup_append.1 tail
  refine ⟨single, ?_⟩
  intro w hw adj
  have inPath : some w ∈ contour := by
    rw [block_shape c]
    simpa only [List.mem_append] using
      (List.mem_append.1 hw).elim (fun a => Or.inl a) (fun b => Or.inr (Or.inr b))
  have inBlock := (mem_real c.block w).2 ((c.oldNeighbors w).1 ⟨c.previouslySeen _ inPath,adj⟩)
  rcases List.mem_append.1 hw with h|h
  · exact separate w ((mem_real _ _).2 h) w (List.mem_append_left _ inBlock) rfl
  · exact right w inBlock w ((mem_real _ _).2 h) rfl

section Projection
variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

private def red (p : Option V) (w : V) : Bool := p.elim false (fun u => decide (G.Adj u w))

private def due (future : List V) (p : Option V) := future.countP (red G p)

private def weight (all : List V) (v : V) := all.countP (fun w => decide (G.Adj v w))

private theorem redCount (l : List (Option V)) (v : V) :
    (l.filterMap id).countP (fun w => decide (G.Adj w v)) =
      l.countP (fun p => red G p v) := by
  induction l with
  | nil => rfl
  | cons h l ih =>
    cases h <;> simp [red,List.countP_cons] at * <;> rw [ih]

private theorem noLater (future : List V) (p : Option V)
    (closed : ∀ w ∈ future, red G p w = false) : due G future p = 0 := by
  induction future with
  | nil => rfl
  | cons w ws ih =>
    have stop := closed w (.head _)
    have tail := ih (fun z hz => closed _ (.tail _ hz))
    simpa [due,List.countP_cons,stop] using tail

private theorem old_count {T : SimpleGraph V} (sub : G ≤ T) {seen contour v future}
    (ds : seen.Nodup) (c : Cover T seen contour v future) :
    seen.countP (fun w => decide (G.Adj v w)) = c.block.countP (fun p => red G p v) := by
  classical
  rw [← redCount]
  have p : (seen.filter fun w => decide (G.Adj v w)).Perm
      ((c.block.filterMap id).filter fun w => decide (G.Adj w v)) := by
    apply (List.perm_ext_iff_of_nodup (ds.filter _) ((cover_parts c).1.filter _)).2
    intro w
    simp only [List.mem_filter,decide_eq_true_eq,mem_real]
    constructor
    · rintro ⟨old,adj⟩
      exact ⟨(c.oldNeighbors w).1 ⟨old,sub adj.symm⟩,adj.symm⟩
    · rintro ⟨here,adj⟩
      exact ⟨((c.oldNeighbors w).2 here).1,adj.symm⟩
  simpa [List.countP_eq_length_filter] using p.length_eq

private theorem project_cover {T : SimpleGraph V} (sub : G ≤ T) {seen contour v future}
    (ds : seen.Nodup) (c : Cover T seen contour v future) :
    ∃ m : SweepMove (contour.map (due G (v :: future))) (weight G (seen ++ v :: future) v),
      m.next = c.next.map (due G future) := by
  let old := due G (v :: future)
  let new := due G future
  let tick := fun p => red G p v
  have update (p) : old p = new p + (if tick p then 1 else 0) := by
    exact List.countP_cons
  have finished {p} (hp : p ∈ c.middle) : new p = 0 := by
    apply noLater
    intro z hz
    cases p with
    | none => rfl
    | some w =>
      have notRed : ¬G.Adj w z := fun h => c.retired w hp _ hz (sub h)
      simp [red,notRed]
  have clear {p} (hp : p ∈ c.left ++ c.right) : old p = new p := by
    rw [update]
    cases p with
    | none => simp [tick,red]
    | some w =>
      have notRed : ¬G.Adj w v := fun h => (cover_parts c).2 w hp (sub h)
      simp [tick,red,notRed]
  have left : c.left.map old = c.left.map new :=
    List.map_congr_left fun _ h => clear (List.mem_append_left _ h)
  have right : c.right.map old = c.right.map new :=
    List.map_congr_left fun _ h => clear (List.mem_append_right _ h)
  have midCount : ((c.middle.map old).filter (fun x => 0 < x)).length = c.middle.countP tick := by
    rw [List.filter_map,List.length_map,List.countP_eq_length_filter]
    apply congrArg List.length
    apply List.filter_congr
    intro p hp
    simp [update,finished hp]
    cases h : tick p <;> rfl
  let charged := fun (b : Bool) (z : Nat) => if b then [z] else []
  let cells := charged (tick c.a) (old c.a) ++
    (c.middle.map old).filter (fun x => 0 < x) ++ charged (tick c.b) (old c.b)
  have amount : cells.length = c.block.countP tick := by
    simp only [cells,List.length_append,midCount,Cover.block,List.countP_cons,List.countP_append,
      List.countP_nil]
    cases tick c.a <;> cases tick c.b <;> simp [charged] <;> omega
  have allDegree : weight G (seen ++ v :: future) v = cells.length + new (some v) := by
    rw [amount]
    simp [weight]
    rw [old_count G sub ds c]
    rfl
  let m : SweepMove (contour.map old) (weight G (seen ++ v :: future) v) := {
    left := c.left.map old, a := old c.a, middle := c.middle.map old,
    b := old c.b, right := c.right.map old
    split := by simp [c.split]
    payA := tick c.a, payB := tick c.b
    endA := fun h => by rw [update,h]; simp
    endB := fun h => by rw [update,h]; simp
    finalInterior := by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := List.mem_map.1 hx
      rw [update,finished hp]
      cases tick p <;> decide
    affordable := by
      change cells.length ≤ _
      omega }
  refine ⟨m,?_⟩
  change (c.left.map old ++ [old c.a - (if tick c.a then 1 else 0),
      weight G (seen ++ v :: future) v - cells.length,
      old c.b - (if tick c.b then 1 else 0)] ++ c.right.map old) = _
  simp [Cover.next,left,right,allDegree,update,new]


private theorem sweep_run {T : SimpleGraph V} (sub : G ≤ T)
    {seen contour future} (sweep : Sweep T seen contour future) (all : List V)
    (order : seen ++ future = all) (nd : all.Nodup)
    (prior : SweepTrace (seen.map (weight G all)) (contour.map (due G future))) :
    ∃ out, SweepTrace (all.map (weight G all)) out ∧ ∀ x ∈ out, x = 0 := by
  induction sweep with
  | done =>
    simp only [List.append_nil] at order
    subst all
    exact ⟨_,prior,fun x hx => by
      obtain ⟨p,_,rfl⟩ := List.mem_map.1 hx
      rfl⟩
  | @step seen contour v remaining c _ ih =>
    have distinct : seen.Nodup := (List.nodup_append.1 (order ▸ nd)).1
    obtain ⟨m,hrow⟩ := project_cover G sub distinct c
    apply ih (by simpa [List.append_assoc] using order)
    rw [List.map_append, List.map_singleton]
    rw [← order, ← hrow] at *
    exact .advance prior m

private theorem weight_degree [Fintype V] {T : SimpleGraph V} (C : CanonicalOrder T) (v : V) :
    weight G C.vertices v = Nat.card {w // G.Adj v w} := by
  classical
  have same : (C.vertices.filter (fun w => decide (G.Adj v w))).toFinset = G.neighborFinset v := by
    ext w
    simp [C.complete, G.mem_neighborFinset]
  change C.vertices.countP _ = _
  rw [List.countP_eq_length_filter,← List.toFinset_card_of_nodup (C.distinct.filter _),same,
    G.card_neighborFinset_eq_degree,← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
  rfl

/-- The degree list is taken directly from the given graph. The construction
counts later red neighbors at each prefix; it assumes no balance history. -/
theorem order_trace [Fintype V] {T : SimpleGraph V} (sub : G ≤ T) (C : CanonicalOrder T) :
    NumericalTrace (C.vertices.map fun v => Nat.card {w // G.Adj v w}) [] := by
  have init : SweepTrace (([] : List V).map (weight G C.vertices))
      ([none,none].map (due G C.vertices)) := by
    have z : due G C.vertices none = 0 := noLater _ _ _ (fun _ _ => rfl)
    simp [z, SweepTrace.start]
  obtain ⟨out, run, zero⟩ := sweep_run G sub C.sweep C.vertices rfl C.distinct init
  have close : out.filter (fun x => 0 < x) = [] := by
    apply List.filter_eq_nil_iff.2
    intro x hx
    simp [zero _ hx]
  have answer := sweep_projects run
  rw [close] at answer
  have eq : weight G C.vertices = (fun v => Nat.card {w // G.Adj v w}) :=
    funext (weight_degree G C)
  rwa [eq] at answer

end Projection

/-- This is the sole canonical-order input: the usual theorem for a
triangulated host with a chosen final vertex, stated for an edge-maximal
planar graph on at least three labelled vertices. -/
def CanonicalOrderingInput : Prop :=
  ∀ (n : Nat), 3 ≤ n → ∀ T : SimpleGraph (Fin n),
    Maximal LeanPool.K5MinorFreeChoosability.IsPlanar T →
    ∀ z : Fin n, ∃ C : CanonicalOrder T, EndsAt C z

private theorem erase_zero {ds row} (h : NumericalTrace ds row) :
    NumericalTrace (ds.filter (fun x => 0 < x)) row := by
  have pos {xs r} (tr : NumericalTrace xs r) : ∀ x ∈ r, 0 < x := by
    cases tr with
    | start => simp
    | advance _ m => intro x hx; simpa using (List.mem_filter.1 hx).2
  induction h with
  | start => exact .start
  | @advance ds row d tr m ih =>
    by_cases z : d=0
    · subst d
      have len := m.affordable
      have empty : m.first=[] ∧ m.middle=[] ∧ m.last=[] := by simpa using len
      obtain ⟨a,b,c⟩ := empty
      have parts : row = m.left ++ m.right := by simpa [a,b,c] using m.split
      have next : m.next = row := by
        have stays : row.filter (fun x => 0 < x) = row :=
          List.filter_eq_self.2 (fun x hx => by simpa using pos tr x hx)
        rw [parts,List.filter_append] at stays
        simpa [NumericalMove.next,a,b,c,List.filter_append] using stays.trans parts.symm
      simpa [next] using ih
    · have positive := Nat.pos_of_ne_zero z
      simpa [positive] using (NumericalTrace.advance ih m)

private def firstStep {V : Type*} (T : SimpleGraph V) (x : V) (future : List V) :
    Cover T [] [none,none] x future where
  left := []; a := none; middle := []; b := none; right := []
  split := rfl
  simplePath := by simp
  previouslySeen := by simp
  oldNeighbors := by simp
  retired := by simp

private def secondStep {V : Type*} [DecidableEq V] (x y : V) (ne : x ≠ y) :
    Cover (⊤ : SimpleGraph V) [x] [none,some x,none] y [] where
  left := [none]; a := some x; middle := []; b := none; right := []
  split := rfl
  simplePath := by simp
  previouslySeen := by simp
  oldNeighbors := by
    intro w
    simp only [SimpleGraph.top_adj,List.nil_append,List.mem_cons,
      Option.some.injEq,Option.some_ne_none,List.not_mem_nil,or_false]
    exact ⟨And.left, fun h => ⟨h,h ▸ ne⟩⟩
  retired := by simp

private theorem small_order {n : Nat} (small : n < 3) (z : Fin n) :
    ∃ C : CanonicalOrder (⊤ : SimpleGraph (Fin n)), EndsAt C z := by
  rcases n with _|n
  · exact Fin.elim0 z
  rcases n with _|n
  · let C : CanonicalOrder (⊤ : SimpleGraph (Fin 1)) := {
      vertices := [z], distinct := by simp
      complete := fun v => by simpa using Subsingleton.elim v z
      sweep := .step (firstStep _ z []) .done }
    exact ⟨C,rfl⟩
  have eq : n = 0 := by omega
  subst n
  let x : Fin 2 := ⟨1-z.val,by omega⟩
  have ne : x ≠ z := by
    intro eq
    have := congrArg Fin.val eq
    change 1-z.val = z.val at this
    omega
  let C : CanonicalOrder (⊤ : SimpleGraph (Fin 2)) := {
    vertices := [x,z], distinct := by simp [ne]
    complete := by
      intro v
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      by_cases e : v=z
      · exact .inr e
      · exact .inl (Fin.ext (show v.val=1-z.val by
          have h : v.val ≠ z.val := fun q => e (Fin.ext q)
          omega))
    sweep := .step (firstStep _ x [z]) (.step (secondStep x z ne) .done) }
  exact ⟨C,rfl⟩

/-- A successful ordered certificate on the positive part, including the
prescribed last input position. The returned order permutes vertex *names*,
so repetitions in the degree list cause no ambiguity. -/
theorem planaric_trace_of_ordering (ord : CanonicalOrderingInput) {ds : List Nat}
    (planar : SparseBoundary.Planaric ds) (z : Fin ds.length) :
    ∃ vs : List (Fin ds.length), vs.Perm (List.finRange ds.length) ∧
      vs.getLast? = some z ∧
      NumericalTrace ((vs.map (fun i => ds[i.val])).filter (fun x => 0 < x)) [] := by
  classical
  obtain ⟨G,deg,p⟩ := planar
  have host : ∃ T : SimpleGraph (Fin ds.length), Wagner.toSimple G ≤ T ∧
      ∃ C : CanonicalOrder T, EndsAt C z := by
    by_cases size : 3 ≤ ds.length
    · obtain ⟨T,sub,maximal⟩ := Augment.exists_maximal (Wagner.toSimple G)
        ((Wagner.planar_iff_rotation G).1 p)
      exact ⟨T,sub,ord _ size T maximal z⟩
    · exact ⟨⊤,le_top,small_order (by omega) z⟩
  obtain ⟨T,sub,C,reserved⟩ := host
  have eq (i : Fin ds.length) : Nat.card {j // (Wagner.toSimple G).Adj i j} = ds[i.val] :=
    (Wagner.neighbor_count G i).trans (deg i)
  refine ⟨C.vertices,(List.perm_ext_iff_of_nodup C.distinct (List.nodup_finRange _)).2
    (fun v => by simp [C.complete]),reserved,?_⟩
  simpa only [eq] using erase_zero (order_trace (Wagner.toSimple G) sub C)

/-- In the numerical certificate itself, every positive term is used once
and the requested positive input occurrence is used last. -/
theorem prescribed_last_degree (ord : CanonicalOrderingInput) {ds : List Nat}
    (planar : SparseBoundary.Planaric ds) (z : Fin ds.length) (positive : 0 < ds[z.val]) :
    ∃ xs : List Nat, xs.Perm (ds.filter (fun x => 0 < x)) ∧
      xs.getLast? = some ds[z.val] ∧ NumericalTrace xs [] := by
  obtain ⟨vs,perm,last,tr⟩ := planaric_trace_of_ordering ord planar z
  refine ⟨_,?_,?_,tr⟩
  · have eq : (List.finRange ds.length).map (fun i => ds[i.val]) = ds := by
      apply List.ext_getElem <;> simp
    have permuted := (perm.map (fun i => ds[i.val])).filter (fun x => decide (0<x))
    exact permuted.trans (List.Perm.of_eq (congrArg (List.filter (fun x : Nat => decide (0<x))) eq))
  · obtain ⟨ys,rfl⟩ := List.getLast?_eq_some_iff.1 last
    simp [positive]

/-- The empty support is covered as well; no choice of last vertex is
required to recover a successful run. -/
theorem planaric_has_trace (ord : CanonicalOrderingInput) {ds : List Nat}
    (planar : SparseBoundary.Planaric ds) :
    ∃ xs : List Nat, xs.Perm (ds.filter (fun x => 0 < x)) ∧ NumericalTrace xs [] := by
  by_cases pos : ∃ z : Fin ds.length, 0 < ds[z.val]
  · obtain ⟨z,p⟩ := pos
    obtain ⟨xs,h,_,run⟩ := prescribed_last_degree ord planar z p
    exact ⟨xs,h,run⟩
  · have zero : ds.filter (fun x => 0 < x) = [] := by
      apply List.filter_eq_nil_iff.2
      intro x hx
      obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hx
      have no : ¬0<x := fun h => pos ⟨⟨i,hi⟩,eq ▸ h⟩
      simp [no]
    exact ⟨[],zero ▸ List.Perm.rfl, .start⟩

end Recognition.CanonicalRow
