import RowPortMinor

/-! The port wires of one vertex form a connected branch set. Distinct
names never share a port, and each paid stroke links the two corresponding
branch sets. The argument works for any choice of width that fits all layers. -/
namespace Recognition.RowRouting
open RowRule RowPlane RowPortMinor LeanPool.K5MinorFreeChoosability

abbrev Coord := Nat × Nat

def ForwardArc (ls : List Layer) (p q : Coord) :=
  ∃ a, ls[p.1]? = some a ∧ q.1 = p.1+1 ∧ a.arc p.2 q.2

def grid (ls : List Layer) : SimpleGraph Coord where
  Adj p q := ForwardArc ls p q ∨ ForwardArc ls q p
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := by
    constructor
    rintro p (⟨_,_,eq,_⟩|⟨_,_,eq,_⟩) <;> omega

private theorem extendGrid (ls rest : List Layer) : grid ls ≤ grid (ls++rest) := by
  have lift {p q} (h : ForwardArc ls p q) : ForwardArc (ls++rest) p q := by
    obtain ⟨a,ha,levels,arc⟩ := h
    have bound := (List.getElem?_eq_some_iff.1 ha).choose
    exact ⟨a,(List.getElem?_append_left bound).trans ha,levels,arc⟩
  intro p q edge
  exact Or.imp lift lift edge

structure Packing (ls : List Layer) (s : State) (w : Nat) where
  bag : Nat → Finset Coord
  bounds : ∀ v < s.n, ∀ p ∈ bag v, p.1 ≤ ls.length ∧ p.2 < w
  connected : ∀ v < s.n, ConnSet (grid ls) (bag v : Set Coord)
  disjoint : ∀ v < s.n, ∀ u < s.n, ∀ p ∈ bag v, p ∈ bag u → v=u
  adjacent : ∀ v < s.n, ∀ u < s.n, u ∈ s.neighbors v →
    ∃ p ∈ bag v, ∃ q ∈ bag u, (grid ls).Adj p q
  active : ∀ i v, s.row[i]? = some v → (ls.length,i) ∈ bag v

private theorem index_at {xs : List Nat} (nd : xs.Nodup) {i v} (h : xs[i]?=some v) :
    xs.idxOf v = i := by
  have mem := List.mem_of_getElem? h
  obtain ⟨hi,eq⟩ := List.getElem?_eq_some_iff.1 h
  have small := List.idxOf_lt_length_iff.2 mem
  exact nd.getElem_inj_iff.1 ((List.getElem_idxOf small).trans eq.symm)

private theorem from_fan {ls s d} (c : Choice s d) {i k v u} (arc : Stroke c i k v u) :
    (grid (ls++[fan c,repack c])).Adj (ls.length,i) (ls.length+1,k) := by
  apply Or.inl
  refine ⟨fan c, ?_, rfl, v,u,arc⟩
  simp

private theorem from_repack {ls s d} (c : Choice s d) {k j v} (arc : Repack c.livePorts k j v) :
    (grid (ls++[fan c,repack c])).Adj (ls.length+1,k) (ls.length+2,j) := by
  apply Or.inl
  refine ⟨repack c, ?_, rfl, v,arc⟩
  simp

private def upperSlot {s d} (c : Choice s d) (v : Nat) := c.upper.idxOf (some v)
private def nextSlot {s d} (c : Choice s d) (v : Nat) := (step c).row.idxOf v

private theorem upper_at {s d} (g : Valid s) (c : Choice s d) {k v}
    (h : c.upper[k]? = some (some v)) : upperSlot c v = k :=
  option_index (upper_unique g c) (List.getElem?_idxOf (List.mem_of_getElem? h)) h

private theorem at_upper {s d} (g : Valid s) (c : Choice s d) {v}
    (h : v=s.n ∨ v∈(step c).row) : c.upper[upperSlot c v]? = some (some v) := by
  rcases h with eq|alive
  · rw [eq,upper_at g c (birth_port c)]
    exact birth_port c
  · obtain ⟨_,_,hit⟩ := next_port_connected g c (List.getElem?_idxOf alive)
    exact List.getElem?_idxOf (List.mem_of_getElem? hit)

private theorem birth_slot {s d} (g : Valid s) (c : Choice s d) :
    upperSlot c s.n = c.left.length+1 := upper_at g c (birth_port c)

private def middleBag {s d} (c : Choice s d) (t : Nat) (old : Nat → Finset Coord) (v : Nat) :=
  if v=s.n then {(t+1,upperSlot c v)}
  else if v∈(step c).row then insert (t+1,upperSlot c v) (old v) else old v

private def nextBag {s d} (c : Choice s d) (t : Nat) (old : Nat → Finset Coord) (v : Nat) :=
  if v∈(step c).row then insert (t+2,nextSlot c v) (middleBag c t old v)
  else middleBag c t old v

private theorem keepOld {s d} (c : Choice s d) (t : Nat) (old : Nat → Finset Coord)
    {v : Nat} (h : v≠s.n) {p : Coord} (hp : p∈old v) : p∈nextBag c t old v := by
  by_cases alive : v∈(step c).row <;> simp [nextBag,middleBag,h,alive,hp]

private theorem middle_mem {s d} (c : Choice s d) (t : Nat) (old : Nat → Finset Coord)
    {v} (need : v=s.n ∨ v∈(step c).row) :
    (t+1,upperSlot c v) ∈ middleBag c t old v := by
  rcases need with rfl|h
  · simp [middleBag]
  · by_cases e : v=s.n <;> simp [middleBag,e,h]

private theorem birth_mem {s d} (c : Choice s d) (t : Nat) (old : Nat → Finset Coord) :
    (t+1,upperSlot c s.n) ∈ nextBag c t old s.n := by
  by_cases alive : s.n∈(step c).row <;> simp [nextBag,middleBag,alive]

private theorem describe {s d} (c : Choice s d) (t : Nat) (old : Nat → Finset Coord)
    {v p} (h : p∈nextBag c t old v) :
    (v≠s.n ∧ p∈old v) ∨
    ((v=s.n ∨ v∈(step c).row) ∧ p=(t+1,upperSlot c v)) ∨
    (v∈(step c).row ∧ p=(t+2,nextSlot c v)) := by
  by_cases e : v=s.n
  · subst v
    by_cases a : s.n∈(step c).row <;> simp [nextBag,middleBag,a] at h ⊢ <;> tauto
  · by_cases a : v∈(step c).row <;> simp [nextBag,middleBag,e,a] at h ⊢ <;> tauto

private theorem mid_conn {s d w ls} (p : Packing ls s w) (g : Valid s) (c : Choice s d)
    {v} (hv : v < s.n+1) :
    ConnSet (grid (ls++[fan c,repack c])) (middleBag c ls.length p.bag v : Set Coord) := by
  by_cases fresh : v=s.n
  · simpa [middleBag,fresh] using connSet_singleton (grid (ls++[fan c,repack c]))
      (ls.length+1,upperSlot c s.n)
  have prev := (p.connected v (by omega)).mono (extendGrid ls [fan c,repack c])
  by_cases alive : v∈(step c).row
  · obtain ⟨i,k,st,rep⟩ := through_old g c (List.getElem?_idxOf alive) fresh
    have top := upper_at g c (Option.join_eq_some_iff.1 st.ports.2)
    have past := p.active i v st.ports.1
    have linked := (from_fan (ls := ls) c st).symm
    rw [← top] at linked
    simpa [middleBag,fresh,alive] using prev.insert_adj past linked
  · simpa [middleBag,fresh,alive] using prev

private theorem new_conn {s d w ls} (p : Packing ls s w) (g : Valid s) (c : Choice s d)
    {v} (hv : v < s.n+1) :
    ConnSet (grid (ls++[fan c,repack c])) (nextBag c ls.length p.bag v : Set Coord) := by
  have mid := mid_conn p g c hv
  by_cases alive : v∈(step c).row
  · obtain ⟨k,rep,hit⟩ := next_port_connected g c (List.getElem?_idxOf alive)
    have eq := upper_at g c hit
    have linked := (from_repack (ls := ls) c rep).symm
    rw [← eq] at linked
    have midMem := middle_mem c ls.length p.bag (.inr alive)
    simpa [nextBag,alive,nextSlot] using mid.insert_adj midMem linked
  · simpa [nextBag,alive] using mid

private theorem decoder {ls s w d} (A : Packing ls s w) (g : Valid s) (c : Choice s d)
    {v p} (hv : v < s.n+1) (hp : p ∈ nextBag c ls.length A.bag v) :
    if p.1 ≤ ls.length then v≠s.n ∧ p∈A.bag v
    else if p.1=ls.length+1 then c.upper[p.2]?=some (some v)
    else (step c).row[p.2]?=some v := by
  rcases describe c ls.length A.bag hp with ⟨old,mem⟩ | ⟨need, rfl⟩ | ⟨alive,rfl⟩
  · simp [(A.bounds v (by omega) p mem).1,old,mem]
  · simpa using at_upper g c need
  · simpa [nextSlot] using List.getElem?_idxOf alive

private theorem new_disjoint {ls s w d} (A : Packing ls s w) (g : Valid s) (c : Choice s d)
    {v u p} (hv : v<s.n+1) (hu : u<s.n+1)
    (pv : p∈nextBag c ls.length A.bag v) (pu : p∈nextBag c ls.length A.bag u) : v=u := by
  have vdata := decoder A g c hv pv
  have udata := decoder A g c hu pu
  by_cases before : p.1≤ls.length
  · simp only [before,↓reduceIte] at vdata udata
    exact A.disjoint v (by have := vdata.1; omega) u (by have := udata.1; omega)
      p vdata.2 udata.2
  · by_cases upper : p.1=ls.length+1
    · simp [upper] at vdata udata
      exact Option.some.inj (Option.some.inj (vdata.symm.trans udata))
    · simp [before,upper] at vdata udata
      exact Option.some.inj (vdata.symm.trans udata)

private theorem new_bounds {ls s w d} (A : Packing ls s w) (g : Valid s) (c : Choice s d)
    (hf : (fan c).width ≤ w) (hr : (repack c).width ≤ w) {v p} (hv : v<s.n+1)
    (mem : p∈nextBag c ls.length A.bag v) : p.1 ≤ (ls++[fan c,repack c]).length ∧ p.2 < w := by
  rcases describe c ls.length A.bag mem with ⟨old,mem⟩ | ⟨need,rfl⟩ | ⟨alive,rfl⟩
  · have b := A.bounds v (by omega) p mem
    exact ⟨by simp; omega,b.2⟩
  · have available := (List.getElem?_eq_some_iff.1 (at_upper g c need)).choose
    exact ⟨by simp,available.trans_le ((Nat.le_max_right ..).trans hf)⟩
  · have room : (step c).row.length ≤ w := by
      rw [← repack_rows g c]
      exact (Nat.le_max_right ..).trans hr
    exact ⟨by simp,(List.idxOf_lt_length_iff.2 alive).trans_le room⟩

private theorem paid_edge {ls s w d} (A : Packing ls s w) (g : Valid s) (c : Choice s d)
    {v : Nat} (pay : v ∈ c.segment) :
    ∃ p ∈ nextBag c ls.length A.bag v, ∃ q ∈ nextBag c ls.length A.bag s.n,
      (grid (ls++[fan c,repack c])).Adj p q := by
  have arc := Stroke.paid (c := c) pay
  have atOld := arc.ports.1
  have name := (g.active _).1 (List.mem_of_getElem? atOld)
  have tip := birth_mem c ls.length A.bag
  rw [birth_slot g c] at tip
  exact ⟨_,keepOld c _ A.bag (Nat.ne_of_lt name.1) (A.active _ _ atOld), _,tip,from_fan c arc⟩

private theorem new_adjacent {ls s w d} (A : Packing ls s w) (g : Valid s) (c : Choice s d)
    {v u} (hv : v<s.n+1) (hu : u<s.n+1) (edge : u ∈ (step c).neighbors v) :
    ∃ p ∈ nextBag c ls.length A.bag v, ∃ q ∈ nextBag c ls.length A.bag u,
      (grid (ls++[fan c,repack c])).Adj p q := by
  by_cases vf : v=s.n
  · subst v
    have pay : u∈c.segment := by simpa [step] using edge
    obtain ⟨q,qm,p,pm,adj⟩ := paid_edge A g c pay
    exact ⟨p,pm,q,qm,adj.symm⟩
  have oldv : v<s.n := by omega
  have absent : s.n∉s.neighbors v := fun hp => (Nat.lt_irrefl _) (g.bounded _ oldv _ hp)
  by_cases uf : u=s.n
  · subst u
    by_cases pay : v∈c.segment
    · exact paid_edge A g c pay
    · simp [step,vf,pay,absent] at edge
  have oldu : u<s.n := by omega
  have oldAdj : u∈s.neighbors v := by
    by_cases pay : v∈c.segment <;> simpa [step,vf,uf,pay] using edge
  obtain ⟨p,pm,q,qm,adj⟩ := A.adjacent v oldv u oldu oldAdj
  exact ⟨p,keepOld c _ _ vf pm,q,keepOld c _ _ uf qm,extendGrid ls _ adj⟩

theorem history_trace {ds s ls} (h : History ds s ls) : Trace ds s := by
  induction h with
  | start => exact .start
  | step _ c ih => exact .advance ih c

/-- All used coordinates belong to the finite rectangle of this replay,
even though the auxiliary grid is defined on pairs of natural numbers. -/
theorem history_packing {ds s ls w} (h : History ds s ls)
    (width : ∀ a∈ls, a.width≤w) : Nonempty (Packing ls s w) := by
  induction h with
  | start =>
    refine ⟨⟨fun _ => ∅, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [empty]
    · simp [empty]
    · simp [empty]
    · simp [empty]
    · simp [empty]
  | @step ds s d ls hist c ih =>
    obtain ⟨A⟩ := ih (fun a good => width a (List.mem_append_left _ good))
    have g := (history_trace hist).valid
    have g' := (Trace.advance (history_trace hist) c).valid
    refine ⟨{ bag := nextBag c ls.length A.bag
              bounds := fun _ hv _ hp => new_bounds A g c (width _ (by simp)) (width _ (by simp)) hv hp
              connected := fun _ hv => new_conn A g c hv
              disjoint := fun _ hv _ hu _ hp hq => new_disjoint A g c hv hu hp hq
              adjacent := fun _ hv _ hu edge => new_adjacent A g c hv hu edge
              active := ?_ }⟩
    intro i v atNew
    have alive := List.mem_of_getElem? atNew
    have j := index_at g'.nodup atNew
    simp [nextBag,alive,nextSlot,j]

def stateGraph (s : State) (g : Valid s) : SimpleGraph (Fin s.n) where
  Adj v u := (u : Nat) ∈ s.neighbors v
  symm := ⟨fun v u => (g.symm v v.isLt u u.isLt).1⟩
  loopless := ⟨fun v => g.loopless v v.isLt⟩

def Packing.model {ls s w} (A : Packing ls s w) (g : Valid s) :
    MinorModel (grid ls) (stateGraph s g) where
  branch v := A.bag v
  branch_nonempty v := (A.connected v v.isLt).1
  branch_connected v := (connSet_iff_induce_connected ..).1 (A.connected v v.isLt)
  branch_disjoint v u ne := Finset.disjoint_left.2 fun p hp hq =>
    ne (Fin.ext (A.disjoint _ v.isLt _ u.isLt p hp hq))
  branch_adjacent v u edge := A.adjacent v v.isLt u u.isLt edge

/-- In a terminal history the model's degree list is the input, in the
same chronological naming used for every branch set. -/
theorem stateGraph_degrees {ds s ls} (h : History ds s ls) (closed : s.row=[]) :
    (List.ofFn fun v => Nat.card {u // (stateGraph s (history_trace h).valid).Adj v u}) = ds := by
  classical
  obtain ⟨G,dec,adj,degrees⟩ := closed_trace_graph (history_trace h) closed
  have eq : G = stateGraph s (history_trace h).valid := by
    ext v u
    exact adj v u
  subst G
  refine Eq.trans ?_ degrees
  congr 1
  funext v
  rw [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
  rfl

end Recognition.RowRouting
