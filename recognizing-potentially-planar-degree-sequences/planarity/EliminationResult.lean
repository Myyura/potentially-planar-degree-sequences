import EmbeddingBridge
import ReverseTrace
import Triangulation.Forward

/-! # Eliminating a coloured list of prescribed edges

The input consists of a simple list of prescribed pairs, oriented increasingly,
together with a proper edge colouring. No packing instance or packing geometry
is used. The numerical encoder uses left-endpoint bits as addresses, including
empty groups, so that the schedule has the same length for every colour.
The map statements quantify over arbitrary input and output realizations.
-/
namespace Recognition.EliminationResult
open Reduction Layers Rigidity Stacking

structure Prescription where
  degrees : List Nat
  edges : List Edge
  colours : Nat
  increasing : ∀ e ∈ edges, e.left < e.right ∧ e.right < degrees.length ∧ e.color < colours
  unique : edges.Nodup
  sameColour : ∀ a ∈ edges, ∀ b ∈ edges, a.left = b.left → a.right = b.right → a.color = b.color
  proper : ∀ a ∈ edges, ∀ b ∈ edges, a.color = b.color →
    ((a.left = b.left ∨ a.right = b.right) → a = b) ∧ a.left ≠ b.right

open Prescription

/-- Euler-tight rows of order at least five are the domain of the peeling library. -/
def BaseValid (I : Prescription) : Prop := TableValid I.degrees ∧ I.edges.length ≤ 3*I.degrees.length-6

private theorem base_valid (I : Prescription) (h : BaseValid I) : TableValid I.degrees := h.1
private abbrev edge_bounds (I : Prescription) := I.increasing
private theorem marker_capacity (I : Prescription) (v : BaseValid I) :
    I.edges.length ≤ 2*fullOrder I.degrees.length-4 := by
  have := v.2
  unfold fullOrder
  omega

def markers (I : Prescription) : List Mark :=
  (edges I).zipIdx.map fun (e,j) => Mark.mk e (fullOrder (degrees I).length+j)

def matchingClass (I : Prescription) (c : Nat) := (markers I).filter (·.edge.color == c)

def tests (I : Prescription) : List Test :=
  (List.range I.colours).flatMap fun c => classTests (bitWidth (degrees I).length) (matchingClass I c)

def allLayers (I : Prescription) := [full, full, full] ++ tests I

def output (I : Prescription) : List Nat :=
  ((allLayers I).foldl layer ⟨I.degrees,0⟩).degrees

theorem marker_bounds (I : Prescription) {a : Mark} (ha : a ∈ markers I) :
    a.edge ∈ edges I ∧ fullOrder (degrees I).length ≤ a.marker ∧
    a.marker < fullOrder (degrees I).length+(edges I).length := by
  obtain ⟨⟨e,j⟩,hj,rfl⟩ := List.mem_map.mp ha
  exact ⟨List.fst_mem_of_mem_zipIdx hj,Nat.le_add_right _ _, by
    have := List.snd_lt_of_mem_zipIdx hj; simp at *; omega⟩

private theorem mark_ident (I : Prescription) (a b : Mark) (ha : a ∈ markers I) (hb : b ∈ markers I)
    (he : a.edge = b.edge) : a = b := by
  obtain ⟨⟨e,i⟩,hi,rfl⟩ := List.mem_map.mp ha
  obtain ⟨⟨f,j⟩,hj,rfl⟩ := List.mem_map.mp hb
  have ei := List.mem_zipIdx' hi
  have ej := List.mem_zipIdx' hj
  have hij := I.unique.eq_of_getElem_eq ei.1 ej.1 (ei.2.symm.trans (he.trans ej.2))
  dsimp at he hij
  subst_vars
  rfl

theorem in_class (I : Prescription) {c : Nat} {a : Mark} (h : a ∈ matchingClass I c) :
    a ∈ markers I ∧ a.edge.color = c := by simpa [matchingClass] using h

theorem endpoints_match (I : Prescription) (c : Nat) (side : Bool) (a b : Mark)
    (ha : a ∈ matchingClass I c) (hb : b ∈ matchingClass I c) :
    (endpoint side a = endpoint side b → a = b) ∧ endpoint side a ≠ endpoint (!side) b := by
  obtain ⟨ham,hac⟩ := in_class I ha
  obtain ⟨hbm,hbc⟩ := in_class I hb
  have he := hac.trans hbc.symm
  have hae := (marker_bounds I ham).1
  have hbe := (marker_bounds I hbm).1
  have f := I.proper _ hae _ hbe he
  have g := I.proper _ hbe _ hae he.symm
  cases side
  · exact ⟨fun h => mark_ident I _ _ ham hbm (f.1 (.inl h)),f.2⟩
  · exact ⟨fun h => mark_ident I _ _ ham hbm (f.1 (.inr h)),Ne.symm g.2⟩

theorem schedule_forces (I : Prescription) (adj : Nat → Nat → Prop)
    (two : ∀ a ∈ markers I, ∀ x y z, adj a.marker x → adj a.marker y → adj a.marker z →
      x = y ∨ x = z ∨ y = z)
    (ok : ∀ q ∈ tests I, Passes adj q) :
    ∀ e ∈ edges I, ∃ a ∈ markers I, a.edge = e ∧ adj a.marker e.left ∧ adj a.marker e.right := by
  intro e he
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp he
  let a := (markers I)[j]'(by simpa [markers] using hj)
  have ha : a ∈ markers I := List.getElem_mem ..
  have heqa : a.edge = (edges I)[j] := by simp [a, markers, List.getElem_zipIdx]
  have hc := (edge_bounds I _ he).2.2
  let c := a.edge.color
  have hcls : a ∈ matchingClass I c := by simp [matchingClass, ha, c]
  have pass := matching_forces (degrees I).length (matchingClass I c) adj
    (fun x hx => by
      have := edge_bounds I _ (marker_bounds I (in_class I hx).1).1
      omega)
    (fun side x hx y hy => (endpoints_match I c side x y hx hy).1)
    (fun side x hx y hy => (endpoints_match I c side x y hx hy).2)
    (fun x hx => two x (in_class I hx).1)
    (fun t ht => ok _ (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr (by simpa [c, heqa] using hc),ht⟩))
  exact ⟨a,ha,heqa,heqa ▸ pass a hcls false,heqa ▸ pass a hcls true⟩

private theorem markers_distinct (I : Prescription) : ((markers I).map Mark.marker).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj eq
  simpa [markers,List.getElem_zipIdx] using eq

private structure Ready (I : Prescription) (T : Table) : Prop where
  valid : TableValid T.degrees
  generation : fullOrder (degrees I).length+(edges I).length ≤ T.fresh
  room : T.fresh+(degrees I).length ≤ T.degrees.length

private theorem test_labels (I : Prescription) (T : Table) (q : Test) (hr : Ready I T)
    (hq : q ∈ tests I) :
    (selectedLabels T q).Nodup ∧ (∀ v ∈ selectedLabels T q, v < T.degrees.length) ∧
      q.group.length ≤ (degrees I).length := by
  obtain ⟨c,_,hc⟩ := List.mem_flatMap.mp hq
  have subc : q.group.Sublist (matchingClass I c) := class_sublist hc
  have subm : q.group.Sublist (markers I) := subc.trans List.filter_sublist
  have ndm : (q.group.map Mark.marker).Nodup :=
    List.Pairwise.sublist (subm.map _) (markers_distinct I)
  have nde : (q.group.map (endpoint q.side)).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (p := List.pairwise_map.mp ndm)
    intro a b ha hb ne eq
    have H := (endpoints_match I c q.side a b (subc.subset ha) (subc.subset hb)).1 eq
    apply ne
    rw [H]
  let s := (degrees I).length
  have boundEnd {v : Nat} (h : v ∈ q.group.map (endpoint q.side)) : v < s := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    have ⟨hl,hr,_⟩ := edge_bounds I a.edge (marker_bounds I (subm.subset ha)).1
    unfold endpoint
    split
    · exact hr
    · exact Nat.lt_trans hl hr
  have boundMark {v : Nat} (h : v ∈ q.group.map Mark.marker) :
      fullOrder s ≤ v ∧ v < T.fresh := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    have H := (marker_bounds I (subm.subset ha)).2
    exact ⟨H.1,Nat.lt_of_lt_of_le H.2 hr.generation⟩
  have sz : q.group.length ≤ s := by
    have := nde.length_le_of_subset (l₂ := List.range s) (fun _ h => List.mem_range.mpr (boundEnd h))
    simpa using this
  have fresh {v : Nat} (h : v ∈ List.range' T.fresh q.group.length) :
      T.fresh ≤ v ∧ v < T.fresh+q.group.length := by
    obtain ⟨j,hj,rfl⟩ := List.mem_range'.mp h
    simp; omega
  have hsf : s ≤ fullOrder s := Nat.le_add_right .. 
  have hg := hr.generation
  have hrm := hr.room
  change fullOrder s + _ ≤ _ at hg
  change T.fresh+s ≤ _ at hrm
  refine ⟨?_,?_,sz⟩
  · apply List.nodup_append.mpr
    refine ⟨List.nodup_append.mpr ⟨ndm,nde,?_⟩, List.nodup_range' 1,?_⟩
    · intro a ha b hb; have := boundMark ha; have := boundEnd hb; omega
    · intro a ha b hb
      have := fresh hb
      rcases List.mem_append.mp ha with h|h
      · have := boundMark h; omega
      · have := boundEnd h; omega
  · intro v hv
    rcases List.mem_append.mp hv with old|new
    · rcases List.mem_append.mp old with mark|e
      · have := boundMark mark; omega
      · have := boundEnd e; omega
    · have := fresh new; omega

/-- The same degree and Euler promises hold for every prefix of successful
numerical compilation, independently of whether a partition exists. -/
private theorem ready_step (I : Prescription) (T : Table) (q : Test) (hr : Ready I T)
    (hq : q ∈ tests I) : Ready I (layer T q) := by
  obtain ⟨nd,hb,hs⟩ := test_labels I T q hr hq
  refine ⟨valid_layer T q hr.valid nd hb, ?_, ?_⟩
  · exact Nat.le_trans hr.generation (Nat.le_trans (Nat.le_add_right ..) hr.room)
  · change T.degrees.length+_ ≤ _
    rw [layer_order]
    have hsf : (degrees I).length ≤ fullOrder (degrees I).length := Nat.le_add_right ..
    have hg := hr.generation
    have hm := hr.room
    have hn := hr.valid.1
    omega

private theorem valid_full (T : Table) (hv : TableValid T.degrees) : TableValid (layer T full).degrees :=
  valid_layer T full hv (by simp [selectedLabels,full]) (by simp [selectedLabels,full])

private def prepared (I : Prescription) :=
  layer (layer (layer ⟨degrees I,0⟩ full) full) full

private theorem ready_prepared (I : Prescription) (hv : BaseValid I) : Ready I (prepared I) := by
  have hs := base_valid I hv
  refine ⟨valid_full _ (valid_full _ (valid_full _ hs)), ?_, ?_⟩
  · have := marker_capacity I hv
    change _ ≤ (layer (layer ⟨degrees I,0⟩ full) full).degrees.length
    simp only [layer_order, full,List.length_nil, Nat.sub_zero]
    unfold fullOrder at *
    omega
  · change (layer (layer ⟨degrees I,0⟩ full) full).degrees.length + _ ≤ _
    simp only [prepared, layer_order, full,List.length_nil, Nat.sub_zero]
    have := hs.1; omega

private theorem ready_fold (I : Prescription) (qs : List Test) (T : Table) (hr : Ready I T)
    (sub : qs ⊆ tests I) : Ready I (qs.foldl layer T) := by
  induction qs generalizing T with
  | nil => exact hr
  | cons q qs ih => exact ih _ (ready_step I T q hr (sub (by simp))) (fun _ h => sub (by simp [h]))

theorem output_valid (I : Prescription) (hv : BaseValid I) : TableValid (output I) := by
  have h := ready_fold I (tests I) (prepared I) (ready_prepared I hv) (fun _ h => h)
  simpa only [output,allLayers,List.foldl_append,List.foldl_cons,List.foldl_nil,prepared] using h.valid

theorem compilation_run (I : Prescription) (hv : BaseValid I) :
    Run ⟨degrees I,0⟩ (allLayers I) ((allLayers I).foldl layer ⟨degrees I,0⟩) := by
  have loop (qs : List Test) (sub : qs ⊆ tests I) (T : Table) (r : Ready I T) :
      Run T qs (qs.foldl layer T) := by
    induction qs generalizing T with
    | nil => exact .nil _
    | cons q qs ih =>
      have hq := sub (List.mem_cons_self (a:=q) (l:=qs))
      have ⟨nd,bound,_⟩ := test_labels I T q r hq
      exact .cons r.valid nd bound
        (ih (fun _ h => sub (List.mem_cons_of_mem _ h)) _ (ready_step I T q r hq))
  have f {T : Table} {qs R} (v : TableValid T.degrees) (h : Run (layer T full) qs R) :
      Run T (full :: qs) R := .cons v (by simp [selectedLabels,full]) (by simp [selectedLabels,full]) h
  have v := base_valid I hv
  let T : Table := ⟨degrees I,0⟩
  let A := layer T full
  let B := layer A full
  have pre := loop (tests I) (fun _ h => h) (prepared I) (ready_prepared I hv)
  have hB := f (T := B) (valid_full A (valid_full T v)) pre
  have hA := f (T := A) (valid_full T v) hB
  simpa only [T,A,B,prepared,allLayers,List.foldl_append,List.foldl_cons,List.foldl_nil,List.cons_append,List.nil_append] using f (T := T) v hA

private theorem face_edges {xs : List Nat} (A : Model xs) {i j k} (f : A.triangle i j k) :
    A.edge i j ∧ A.edge i k ∧ A.edge j k := by
  obtain ⟨a,b,c,ha,hb,hc,g⟩ := f
  exact ⟨⟨a,b,ha,hb,c,g⟩, ⟨a,c,ha,hc,b,A.map.flip (A.map.rot (A.map.rot g))⟩,
    ⟨b,c,hb,hc,a,A.map.rot g⟩⟩

theorem test_group (I : Prescription) {t : Test} (h : t ∈ tests I) (a : Mark) (ha : a ∈ t.group) :
    a ∈ markers I := by
  obtain ⟨c,_,ht⟩ := List.mem_flatMap.mp h
  exact (in_class I ((class_sublist ht).subset ha)).1

private def limit (I : Prescription) := fullOrder (degrees I).length+(edges I).length

private theorem original_bound (I : Prescription) : (degrees I).length ≤ limit I := by
  simp only [limit,fullOrder]
  omega

theorem end_bound (I : Prescription) {a : Mark} (ha : a ∈ markers I) (b : Bool) :
    endpoint b a < (degrees I).length := by
  have := edge_bounds I a.edge (marker_bounds I ha).1
  cases b <;> simp [endpoint] <;> omega

/-- The selected triangle of each marker gives a selected endpoint. The other
two available kinds of corner are each an independent set. -/
private theorem passes_step (I : Prescription) {A : Table} {t : Test} {R : Model (layer A t).degrees}
    (s : Step A t R) (ht : t ∈ tests I)
    (markers : ∀ a ∈ markers I, ∀ b ∈ markers I, ¬ s.base.edge a.marker b.marker)
    (aux : ∀ i j, A.fresh ≤ i → A.fresh ≤ j → ¬ s.base.edge i j) :
    Passes s.base.edge t := by
  intro a ha
  have ma : a.marker ∈ selectedLabels A t := List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩))
  obtain ⟨j,hj,k,hk,f⟩ := s.vacancy _ ma
  obtain ⟨aj,ak,jk⟩ := face_edges R f
  have back {u v} (hu : u ∈ selectedLabels A t) (hv : v ∈ selectedLabels A t) :=
    (s.edges _ _ (s.selectedBound _ hu) (s.selectedBound _ hv)).mpr
  have inspect (v : Nat) (hv : v ∈ selectedLabels A t) (edge : R.edge a.marker v) :
      (∃ b ∈ t.group, v = endpoint t.side b) ∨ A.fresh ≤ v := by
    rcases List.mem_append.mp hv with h | h
    · rcases List.mem_append.mp h with m | e
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp m
        exact False.elim (markers a (test_group I ht a ha) b (test_group I ht b hb) (back ma hv edge))
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp e
        exact Or.inl ⟨b,hb,rfl⟩
    · obtain ⟨i,_,rfl⟩ := List.mem_range'.mp h
      exact Or.inr (Nat.le_add_right ..)
  rcases inspect j hj aj with ⟨b,hb,rfl⟩ | h
  · exact ⟨b,hb,back ma hj aj⟩
  rcases inspect k hk ak with ⟨b,hb,rfl⟩ | g
  · exact ⟨b,hb,back ma hk ak⟩
  · exact False.elim (aux _ _ h g (back hj hk jk))

private theorem schedule_passes (I : Prescription) (fixed : Nat → Nat → Prop)
    {A R qs Z S} (h : Trail A R qs Z S) (sub : qs ⊆ tests I)
    (room : limit I ≤ A.fresh ∧ A.fresh ≤ A.degrees.length)
    (preserve : ∀ i j, i < limit I → j < limit I → (R.edge i j ↔ fixed i j))
    (markers : ∀ a ∈ markers I, ∀ b ∈ markers I, ¬ fixed a.marker b.marker)
    (aux : ∀ i j, A.fresh ≤ i → A.fresh ≤ j → ¬ R.edge i j) :
    ∀ t ∈ qs, Passes fixed t := by
  induction h with
  | nil => simp
  | @cons A t qs Z R S s _ ih =>
    have ht : t ∈ tests I := sub (List.mem_cons_self ..)
    have pin {i j} (hi : i < limit I) (hj : j < limit I) : R.edge i j ↔ fixed i j :=
      (s.edges i j (by omega) (by omega)).symm.trans (preserve _ _ hi hj)
    have keep := ih (fun _ h => sub (List.mem_cons_of_mem _ h)) (by
      change limit I ≤ A.degrees.length ∧ A.degrees.length ≤ (layer A t).degrees.length
      rw [layer_order]; omega) (fun _ _ a b => pin a b) s.independent
    intro q hq
    rcases List.mem_cons.mp hq with rfl | h'
    · have localPass := passes_step I s ht (fun a ha b hb e => markers a ha b hb
          ((preserve _ _ (marker_bounds I ha).2.2 (marker_bounds I hb).2.2).mp e)) aux
      intro a ha
      obtain ⟨b,hb,e⟩ := localPass a ha
      have endLt := Nat.lt_of_lt_of_le (end_bound I (test_group I ht b hb) q.side) (original_bound I)
      exact ⟨b,hb,(preserve _ _ (marker_bounds I (test_group I ht a ha)).2.2 endLt).mp e⟩
    · exact keep q h'


private theorem edge_symm {xs : List Nat} (A : Model xs) {i j} : A.edge i j → A.edge j i := by
  rintro ⟨a,b,ha,hb,c,f⟩
  exact ⟨b,a,hb,ha,c,A.map.flip f⟩

private theorem edge_of_corners {xs : List Nat} (A : Model xs) {a b c i j : Nat}
    (f : A.triangle a b c) (h : i = a ∨ i = b ∨ i = c) (k : j = a ∨ j = b ∨ j = c)
    (ij : i ≠ j) : A.edge i j := by
  obtain ⟨ab,ac,bc⟩ := face_edges A f
  have ba := edge_symm A ab
  have ca := edge_symm A ac
  have cb := edge_symm A bc
  grind

private theorem force_from_trail (I : Prescription) (valid : BaseValid I) {Z R S}
    (trail : Trail ⟨degrees I,0⟩ S (full :: full :: full :: tests I) Z R) :
    ∀ e ∈ edges I, S.edge e.left e.right := by
  cases trail with
  | @cons _ _ _ _ _ _ s1 tr1 =>
    cases tr1 with
    | @cons _ _ _ _ _ _ s2 tr2 =>
      cases tr2 with
      | @cons A _ _ Z M3 R s3 rest =>
        let T0 : Table := ⟨degrees I,0⟩
        let n := (degrees I).length
        let n1 := fullOrder n
        let n2 := fullOrder n1
        have l1 : (layer T0 full).degrees.length = n1 := full_length T0
        have l2 : (layer (layer T0 full) full).degrees.length = n2 := (full_length _).trans (congrArg fullOrder l1)
        have protect : limit I ≤ n2 := by
          have room := marker_capacity I valid
          change n1+(edges I).length ≤ n1+(2*n1-4)
          exact Nat.add_le_add_left room _
        have baseSmall : n ≤ n1 := Nat.le_add_right .. 
        have inputSmall := original_bound I
        have markerInd : ∀ a ∈ markers I, ∀ b ∈ markers I, ¬ M3.edge a.marker b.marker := by
          intro a ha b hb adj
          have pa := (marker_bounds I ha).2
          have pb := (marker_bounds I hb).2
          have oa : a.marker < n2 := Nat.lt_of_lt_of_le pa.2 protect
          have ob : b.marker < n2 := Nat.lt_of_lt_of_le pb.2 protect
          have low := (s3.edges _ _ (l2 ▸ oa) (l2 ▸ ob)).mpr adj
          exact s2.independent _ _ (l1 ▸ pa.1) (l1 ▸ pb.1) low
        have ok := schedule_passes I M3.edge rest (fun _ h => h) (by
          constructor
          · change limit I ≤ (layer (layer T0 full) full).degrees.length
            exact l2 ▸ protect
          · change (layer (layer T0 full) full).degrees.length ≤ (layer (layer (layer T0 full) full) full).degrees.length
            exact layer_ge (layer (layer T0 full) full) full) (fun _ _ _ _ => Iff.rfl) markerInd s3.independent
        let adj := fun m v => v < n ∧ M3.edge m v
        have pass : ∀ q ∈ tests I, Passes adj q := by
          intro q hq a ha
          obtain ⟨b,hb,e⟩ := ok q hq a ha
          exact ⟨b,hb,end_bound I (test_group I hq b hb) q.side,e⟩
        have triangle (m : Mark) (hm : m ∈ markers I) :
            ∃ a b c, s2.base.triangle a b c ∧
              ¬ (a < n ∧ b < n ∧ c < n) ∧
              ∀ j, adj m.marker j → j = a ∨ j = b ∨ j = c := by
          have p := (marker_bounds I hm).2
          have hi : m.marker < n2 := Nat.lt_of_lt_of_le p.2 protect
          obtain ⟨a,b,c,_,_,_,f,neighbors⟩ := s2.star m.marker (l1 ▸ p.1) (l2 ▸ hi)
          refine ⟨a,b,c,f,?_,?_⟩
          · rintro ⟨a₀,b₀,c₀⟩
            have := s1.allOld a b c a₀ b₀ c₀ f
            simp [selectedLabels,full] at this
          · intro j h
            have hj : j < n2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h.1 inputSmall) protect
            exact (neighbors j).mp ((s3.edges _ _ (l2 ▸ hi) (l2 ▸ hj)).mpr h.2)
        have two (m : Mark) (hm : m ∈ markers I) (x y z : Nat)
            (hx : adj m.marker x) (hy : adj m.marker y) (hz : adj m.marker z) :
            x = y ∨ x = z ∨ y = z := by
          obtain ⟨a,b,c,_,non,only⟩ := triangle m hm
          have := only x hx
          have := only y hy
          have := only z hz
          have := hx.1
          have := hy.1
          have := hz.1
          grind
        intro e he
        obtain ⟨m,hm,_,left,right⟩ := schedule_forces I adj two pass e he
        obtain ⟨a,b,c,f,_,only⟩ := triangle m hm
        have edge := edge_of_corners s2.base f (only _ left) (only _ right)
          (Nat.ne_of_lt (edge_bounds I e he).1)
        exact (s1.edges _ _ left.1 right.1).mpr edge

/-- Every realization of the output recovers the prescribed pairs on one and
 the same induced base map. All labels of surviving vertices are preserved. -/
theorem decode_induced (I : Prescription) (v : BaseValid I) (R : Model (output I)) :
    ∃ S : Model I.degrees, (∀ e ∈ I.edges, S.edge e.left e.right) ∧
      ∀ i j, i < I.degrees.length → j < I.degrees.length → (S.edge i j ↔ R.edge i j) := by
  obtain ⟨S,h⟩ := reverse_run (compilation_run I v) R
  exact ⟨S, force_from_trail I v h, h.induced⟩

open Forward (Omission Cover allFaces extend extend_edges extend_names separate ofFn_unique)
variable {T : Table} {q : Test} (R : Model T.degrees)

def Marked (I : Prescription) (R : Model T.degrees) :=
  ∀ a ∈ markers I, R.edge a.marker a.edge.left ∧ R.edge a.marker a.edge.right

private theorem keep_marked {I : Prescription} (h : Marked I R) {O : Omission R q}
    (xs : List (Star R.map O.fill)) (nd : xs.Nodup) (v : TableValid T.degrees)
    (labels : (selectedLabels T q).Nodup) (bounded : ∀ i ∈ selectedLabels T q, i < T.degrees.length) :
    Marked I (extend R (O := O) xs nd v labels bounded) := by
  intro a ha
  exact ⟨extend_edges R xs nd v labels bounded (h a ha).1,
    extend_edges R xs nd v labels bounded (h a ha).2⟩

/-- Choose the newly introduced vertices for the next test before numbering
this fresh generation. This keeps every earlier marker and endpoint fixed. -/
private theorem lookahead (P : {V : Type} → Map V → Prop)
    (lift : ∀ {V : Type} (M : Map V) (fill : Choice V), P M → P (stack M fill))
    (previous : P R.map) (I : Prescription) {O : Omission R q}
    (v : TableValid T.degrees) (labels : (selectedLabels T q).Nodup)
    (bounded : ∀ i ∈ selectedLabels T q, i < T.degrees.length)
    (h : Marked I R) (r : Test) (hr : r ∈ tests I)
    (nextND : (selectedLabels (layer T q) r).Nodup) :
    ∃ N : Model (layer T q).degrees, P N.map ∧ Marked I N ∧ Nonempty (Cover N r) := by
  classical
  let m (i : Fin r.group.length) := r.group[i.val]
  have req (i : Fin r.group.length) : R.edge (m i).marker (endpoint r.side (m i)) := by
    have e := h (m i) (test_group I hr _ (List.getElem_mem i.isLt))
    cases r.side <;> simp [endpoint] <;> first | exact e.1 | exact e.2
  let x i := (req i).choose
  let y i := (req i).choose_spec.choose
  have nameX i : R.label (x i) = (m i).marker := (req i).choose_spec.choose_spec.1
  have nameY i : R.label (y i) = endpoint r.side (m i) := (req i).choose_spec.choose_spec.2.1
  have pair i : R.map.adj (x i) (y i) := (req i).choose_spec.choose_spec.2.2
  have sep (i j : Fin r.group.length) (ne : i ≠ j) :
      x i ≠ x j ∧ x i ≠ y j ∧ y i ≠ x j ∧ y i ≠ y j := by
    have S := separate r nextND i j ne
    change (m i).marker ≠ (m j).marker ∧ (m i).marker ≠ endpoint r.side (m j) ∧
      endpoint r.side (m i) ≠ (m j).marker ∧ endpoint r.side (m i) ≠ endpoint r.side (m j) at S
    have := nameX i; have := nameX j; have := nameY i; have := nameY j
    grind
  obtain ⟨f,faces,inj⟩ := FaceTests.matching_faces R.map O.fill O.disjoint x y pair sep
  have nd := ofFn_unique f inj
  let N := extend R (O := O) (List.ofFn f) nd v labels bounded
  refine ⟨N,lift R.map O.fill previous,keep_marked R h (List.ofFn f) nd v labels bounded,⟨?_⟩⟩
  exact {
    x := fun i => .inl (x i)
    y := fun i => .inl (y i)
    z := fun i => .inr (f i)
    labX := nameX
    labY := nameY
    labZ := extend_names R f nd v labels bounded
    face := faces
  }


private theorem finish (P : {V : Type} → Map V → Prop)
    (lift : ∀ {V : Type} (M : Map V) (fill : Choice V), P M → P (stack M fill))
    (I : Prescription) {T : Table} {q qs Z} (R : Model T.degrees)
    (previous : P R.map) (O : Omission R q) (marksReady : Marked I R) (run : Run T (q::qs) Z)
    (sub : qs ⊆ tests I) : ∃ N : Model Z.degrees, P N.map := by
  induction qs generalizing T q with
  | nil =>
    cases run with
    | cons v nd bound tail =>
      cases tail
      exact ⟨extend R (O := O) [] (by simp) v nd bound,lift R.map O.fill previous⟩
  | cons r rs ih =>
    cases run with
    | cons v nd bound tail =>
      have nextND : (selectedLabels (layer T q) r).Nodup := by cases tail; assumption
      obtain ⟨N,hp,hm,⟨C⟩⟩ := lookahead R P lift previous I (O := O) v nd bound marksReady r
        (sub (List.mem_cons_self ..)) nextND
      exact ih N hp (C.omission nextND) hm tail (fun _ h => sub (List.mem_cons_of_mem _ h))

private theorem full_labels (A : Table) : (selectedLabels A full).Nodup ∧
    ∀ v ∈ selectedLabels A full, v < A.degrees.length := by simp [selectedLabels,full]

private theorem name_markers (P : {V : Type} → Map V → Prop)
    (lift : ∀ {V : Type} (M : Map V) (fill : Choice V), P M → P (stack M fill))
    (I : Prescription) (A : Table) (eq : A.degrees = degrees I)
    (R : Model A.degrees) (previous : P R.map) (v : TableValid A.degrees)
    (pres : ∀ e ∈ edges I, R.edge e.left e.right) :
    ∃ N : Model (layer (layer A full) full).degrees, P N.map ∧ Marked I N := by
  classical
  let T1 := layer A full
  let all := allFaces R
  let U := extend R (O := all) [] (by simp) v (full_labels A).1 (full_labels A).2
  let V1 := valid_layer A full v (full_labels A).1 (full_labels A).2
  let all' := allFaces U
  let edges := edges I
  let e (i : Fin edges.length) := edges[i.val]
  have em (i : Fin edges.length) : e i ∈ I.edges := List.getElem_mem i.isLt
  have edge i := pres _ (em i)
  let x i := (edge i).choose
  let y i := (edge i).choose_spec.choose
  have lx i : R.label (x i) = (e i).left := (edge i).choose_spec.choose_spec.1
  have ly i : R.label (y i) = (e i).right := (edge i).choose_spec.choose_spec.2.1
  have non (i : Fin edges.length) := (edge_bounds I _ (em i)).1
  have same (i j : Fin edges.length) (p : (x i=x j ∧ y i=y j) ∨ (x i=y j ∧ y i=x j)) :
      i = j := by
    have l₁ := lx i; have l₂ := lx j; have r₁ := ly i; have r₂ := ly j
    have lo := non i; have hi := non j
    have al : (e i).left = (e j).left := by grind
    have ar : (e i).right = (e j).right := by grind
    have ac : (e i).color = (e j).color := by
      exact I.sameColour _ (em i) _ (em j) al ar
    have ext {a b : Edge} : a.left=b.left → a.right=b.right → a.color=b.color → a=b := by cases a; cases b; grind
    have ee : e i = e j := ext al ar ac
    exact Fin.ext (List.nodup_iff_eq_of_getElem_eq.mp I.unique _ _ i.isLt j.isLt ee)
  obtain ⟨marker,injective,neighbors⟩ := FaceTests.prepare_markers R.map x y (fun i => (edge i).choose_spec.choose_spec.2.2) same
  have nd := ofFn_unique marker injective
  let N := extend (T := T1) U (O := all') (List.ofFn marker) nd V1 (full_labels T1).1 (full_labels T1).2
  have tag (i : Fin edges.length) :
      N.label (.inr (marker i)) = fullOrder (degrees I).length + i.val := by
    have h := extend_names (T := T1) U (O := all') marker nd V1 (full_labels T1).1 (full_labels T1).2 i
    change N.label (.inr (marker i)) = T1.degrees.length + i.val at h
    rw [show T1.degrees.length = fullOrder (degrees I).length from (full_length A).trans (congrArg (fun xs : List Nat => fullOrder xs.length) eq)] at h
    exact h
  refine ⟨N,lift U.map all'.fill (lift R.map all.fill previous),?_⟩
  intro m hm
  obtain ⟨k,hk,hmk⟩ := List.mem_iff_getElem.mp hm
  have hk' : k < edges.length := by simpa [markers,edges] using hk
  let i : Fin edges.length := ⟨k,hk'⟩
  have idEdge : m.edge = e i := by simpa [markers,e,edges,i,List.getElem_zipIdx] using congrArg Mark.edge hmk.symm
  have idMark : m.marker = fullOrder (degrees I).length + i.val := by
    simpa [markers,i,List.getElem_zipIdx] using congrArg Mark.marker hmk.symm
  have key : N.label (.inr (marker i)) = m.marker := (tag i).trans idMark.symm
  constructor
  · exact ⟨.inr (marker i),.inl (.inl (x i)),key,(lx i).trans (congrArg Edge.left idEdge.symm),
      (neighbors i (x i)).mpr (Or.inl rfl)⟩
  · exact ⟨.inr (marker i),.inl (.inl (y i)),key,(ly i).trans (congrArg Edge.right idEdge.symm),
      (neighbors i (y i)).mpr (Or.inr rfl)⟩

theorem encode_preserving (P : {V : Type} → Map V → Prop)
    (lift : ∀ {V : Type} (M : Map V) (fill : Choice V), P M → P (stack M fill))
    (I : Prescription) (valid : BaseValid I) (R : Model (degrees I))
    (previous : P R.map) (pres : ∀ e ∈ edges I, R.edge e.left e.right) :
    ∃ N : Model (output I), P N.map := by
  let T0 : Table := ⟨degrees I,0⟩
  let T2 := layer (layer T0 full) full
  obtain ⟨M,hp,h⟩ := name_markers P lift I T0 rfl R previous (base_valid I valid) pres
  let Z := (allLayers I).foldl layer T0
  have program := compilation_run I valid
  change Run T0 (full :: full :: full :: tests I) Z at program
  have cut {A : Table} {t ts Z} (run : Run A (t::ts) Z) : Run (layer A t) ts Z := by cases run; assumption
  have remaining : Run T2 (full :: tests I) Z := cut (cut program)
  exact finish P lift I M hp (allFaces M) h remaining (fun _ h => h)

theorem encode_prescribed (I : Prescription) (valid : BaseValid I) (R : Model (degrees I))
    (pres : ∀ e ∈ edges I, R.edge e.left e.right) : Nonempty (Model (output I)) := by
  obtain ⟨N,_⟩ := encode_preserving (fun _ => True) (fun _ _ _ => trivial) I valid R trivial pres
  exact ⟨N⟩

theorem encode_stacked (I : Prescription) (valid : BaseValid I) (R : Model (degrees I))
    (previous : StackedMap R.map) (pres : ∀ e ∈ edges I, R.edge e.left e.right) :
    ∃ N : Model (output I), StackedMap N.map :=
  encode_preserving StackedMap (fun _ fill prev => .subdivide prev fill) I valid R previous pres

/-- Exact realizability, with the geometric input a triangular map. -/
theorem elimination_iff (I : Prescription) (v : BaseValid I) :
    Nonempty (Model (output I)) ↔ ∃ R : Model I.degrees, ∀ e ∈ I.edges, R.edge e.left e.right := by
  constructor
  · rintro ⟨M⟩
    obtain ⟨R,edges,_⟩ := decode_induced I v M
    exact ⟨R,edges⟩
  · rintro ⟨R,edges⟩
    exact encode_prescribed I v R edges

/-- For an ordinary planar output graph, the recovered adjacencies are exactly
those of its induced subgraph on the original labels. -/
theorem recover_planar_output (I : Prescription) (v : BaseValid I)
    (G : SparseBoundary.Graph (output I).length) (realizes : G.Realizes (output I)) (planar : G.Planar) :
    ∃ S : Model I.degrees, (∀ e ∈ I.edges, S.edge e.left e.right) ∧
      ∀ (i j : Fin (output I).length), i.val < I.degrees.length → j.val < I.degrees.length →
        (S.edge i.val j.val ↔ G.adj i j = true) := by
  obtain ⟨M,adj⟩ := Wagner.tight_embedding _ G (output_valid I v) realizes planar
  obtain ⟨S,edges,induced⟩ := decode_induced I v M
  exact ⟨S,edges,fun i j hi hj => (induced _ _ hi hj).trans (adj i j)⟩

/-! ## The greedy colouring of an ordinary prescription -/

private def occupied (v : Nat) (p : Nat × Nat) := p.1 == v || p.2 == v

/-- The degree in the input is counted directly from the uncoloured edge list. -/
def incidence (rows : List (Nat × Nat)) (v : Nat) := (rows.filter (occupied v)).length

private def ends (e : Edge) := (e.left, e.right)

private def freeColour (used : List Nat) : Nat :=
  ((List.range (used.length + 1)).find? (fun k => !(used.contains k))).getD 0

private theorem free_spec (used : List Nat) : freeColour used ≤ used.length ∧ freeColour used ∉ used := by
  let scan := List.range (used.length+1)
  cases h : scan.find? (fun k => !(used.contains k)) with
  | none =>
    have sub : scan ⊆ used := by
      intro k hk
      have := List.find?_eq_none.mp h k hk
      simpa using this
    have := (List.nodup_range : scan.Nodup).length_le_of_subset sub
    simp at this
  | some k =>
    have picked : freeColour used = k := by
      change (scan.find? (fun k => !(used.contains k))).getD 0 = k
      rw [h]; rfl
    rw [picked]
    have inside := List.mem_range.mp (List.mem_of_find?_eq_some h)
    have fresh := List.find?_some h
    exact ⟨by omega,by simpa using fresh⟩

private def usedAt (es : List Edge) (v : Nat) := es.filter (fun e => occupied v (ends e))

private def blockedColours (es : List Edge) (p : Nat × Nat) :=
  (usedAt es p.1 ++ usedAt es p.2).map Edge.color

/-- Greedy first-fit in reverse list order. The choice uses only colours
already assigned to edges incident with either endpoint. -/
def paint : List (Nat × Nat) → List Edge
  | [] => []
  | p :: tail =>
    let rest := paint tail
    ⟨p.1,p.2,freeColour (blockedColours rest p)⟩ :: rest

@[simp] private theorem paint_ends (rows : List (Nat × Nat)) : (paint rows).map ends = rows := by
  induction rows with
  | nil => rfl
  | cons p ps ih => simp [paint,ends,ih]

private theorem paint_at (rows : List (Nat × Nat)) (v : Nat) :
    (usedAt (paint rows) v).length = incidence rows v := by
  induction rows with
  | nil => simp [paint,usedAt,incidence]
  | cons p ps ih =>
    by_cases h : occupied v p <;> simpa [paint,usedAt,incidence,List.filter_cons,h,ends] using ih

private theorem paint_bounds (rows : List (Nat × Nat)) (c : Nat)
    (deg : ∀ v, incidence rows v ≤ c) : ∀ e ∈ paint rows, e.color < 2*c-1 := by
  induction rows with
  | nil => simp [paint]
  | cons p ps ih =>
    have recur : ∀ v, incidence ps v ≤ c := by
      intro v
      have := deg v
      by_cases h : occupied v p <;> simp [incidence,List.filter_cons,h] at * <;> omega
    intro e he
    rcases List.mem_cons.mp he with rfl | old
    · have l := deg p.1
      have r := deg p.2
      have hl : incidence ps p.1 + 1 ≤ c := by simpa [incidence,List.filter_cons,occupied] using l
      have hr : incidence ps p.2 + 1 ≤ c := by simpa [incidence,List.filter_cons,occupied] using r
      have pick := (free_spec (blockedColours (paint ps) p)).1
      simp only [blockedColours,List.length_map,List.length_append,paint_at] at pick
      change freeColour _ ≤ incidence ps p.1 + incidence ps p.2 at pick
      exact Nat.lt_of_le_of_lt pick (by omega)
    · exact ih recur e old

private theorem paint_proper (rows : List (Nat × Nat)) (strict : ∀ p ∈ rows, p.1 < p.2) :
    ∀ a ∈ paint rows, ∀ b ∈ paint rows, a.color = b.color →
      ((a.left = b.left ∨ a.right = b.right) → a = b) ∧ a.left ≠ b.right := by
  induction rows with
  | nil => simp [paint]
  | cons p ps ih =>
    have rest := ih (fun x hx => strict x (List.mem_cons_of_mem _ hx))
    let e : Edge := ⟨p.1,p.2,freeColour (blockedColours (paint ps) p)⟩
    have different (b : Edge) (hb : b ∈ paint ps) (eq : e.color = b.color) :
        p.1 ≠ b.left ∧ p.1 ≠ b.right ∧ p.2 ≠ b.left ∧ p.2 ≠ b.right := by
      have unused := (free_spec (blockedColours (paint ps) p)).2
      change e.color ∉ _ at unused
      rw [eq] at unused
      have no (h : occupied p.1 (ends b) ∨ occupied p.2 (ends b)) : False := by
        apply unused
        apply List.mem_map.mpr
        refine ⟨b, List.mem_append.mpr (?_),rfl⟩
        exact h.imp (fun t => List.mem_filter.mpr ⟨hb,t⟩) (fun t => List.mem_filter.mpr ⟨hb,t⟩)
      simp only [occupied,ends,Bool.or_eq_true,beq_iff_eq] at no
      grind
    intro a ha b hb eq
    change a ∈ e :: paint ps at ha
    change b ∈ e :: paint ps at hb
    rcases List.mem_cons.mp ha with rfl | ha <;> rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨fun _ => rfl,Nat.ne_of_lt (strict p (List.mem_cons_self ..))⟩
    · have d := different b hb eq
      change ((_ = _ ∨ _ = _) → _) ∧ p.1 ≠ b.right
      exact ⟨fun h => h.elim (fun h => (d.1 h).elim) (fun h => (d.2.2.2 h).elim),d.2.1⟩
    · have d := different a ha eq.symm
      exact ⟨fun h => h.elim (fun h => (d.1 h.symm).elim) (fun h => (d.2.2.2 h.symm).elim),Ne.symm d.2.2.1⟩
    · exact rest a ha b hb eq

/-- Ordinary pairs in arbitrary order are coloured with at most `2*c-1`
colours. All fields of the geometric compiler's input are established here. -/
def ofPairs (ds : List Nat) (rows : List (Nat × Nat)) (c : Nat)
    (ordered : ∀ p ∈ rows, p.1 < p.2 ∧ p.2 < ds.length) (nd : rows.Nodup)
    (deg : ∀ v, incidence rows v ≤ c) : Prescription where
  degrees := ds
  edges := paint rows
  colours := 2*c-1
  increasing := by
    intro e he
    have mem : ends e ∈ rows := paint_ends rows ▸ List.mem_map.mpr ⟨e,he,rfl⟩
    exact ⟨(ordered _ mem).1,(ordered _ mem).2,paint_bounds rows c deg e he⟩
  unique := List.Nodup.of_map ends (by simpa using nd)
  sameColour := by
    intro a ha b hb l r
    have hn : ((paint rows).map ends).Nodup := by simpa using nd
    have same := List.inj_on_of_nodup_map hn ha hb (Prod.ext l r)
    exact congrArg Edge.color same
  proper := paint_proper rows (fun p h => (ordered p h).1)

/-! ## Returning to the ordinary graph language -/

private noncomputable def labelEquiv {ds : List Nat} (R : Model ds) : R.V ≃ Fin ds.length :=
  Equiv.ofBijective (fun v => (⟨R.label v,bound R v⟩ : Fin ds.length))
    ⟨fun a b h => R.inj a b (congrArg Fin.val h),fun j => by
      obtain ⟨a,h⟩ := (R.hits _).mp j.isLt
      exact ⟨a,Fin.ext h⟩⟩

private def relabelTriangle (f : V → W) (t : Triangle V) : Triangle W := ⟨f t.a,f t.b,f t.c⟩

private theorem relabelWalk {F : V → V → V → Prop} {H : W → W → W → Prop} (f : V → W)
    (pres : ∀ a b c, F a b c → H (f a) (f b) (f c)) {s t} (w : Rigidity.Walk F s t) :
    Rigidity.Walk H (relabelTriangle f s) (relabelTriangle f t) := by
  induction w with
  | nil => exact .nil
  | rot _ ih => exact .rot ih
  | flip _ ih => exact .flip ih
  | cross _ h ih => exact .cross ih (pres _ _ _ h)

private noncomputable def namedMap {ds : List Nat} (R : Model ds) : Rigidity.Map (Fin ds.length) := by
  let e := labelEquiv R
  let H := fun x y z => R.map.face (e.symm x) (e.symm y) (e.symm z)
  refine {
    face := H
    rot := fun h => R.map.rot h
    flip := fun h => R.map.flip h
    distinct := fun h same => R.map.distinct h (congrArg e.symm same)
    twoSides := ?_
    incident := ?_
    connected := ?_
  }
  · intro a b c f
    obtain ⟨d,ne,g,only⟩ := R.map.twoSides f
    refine ⟨e d,fun eq => ne ((e.symm_apply_eq).mpr eq.symm).symm,?_,?_⟩
    · simpa [H] using g
    · intro z h
      rcases only _ h with one | two
      · exact Or.inl (e.symm.injective one)
      · exact Or.inr ((e.symm_apply_eq).mp two)
  · intro a
    obtain ⟨b,c,f⟩ := R.map.incident (e.symm a)
    exact ⟨e b,e c,by simpa [H] using f⟩
  · intro a b c x y z f g
    have w := relabelWalk (H := H) e (fun i j k h => by simpa [H] using h) (R.map.connected f g)
    simpa [relabelTriangle] using w

private theorem named_adj {ds : List Nat} (R : Model ds) (x y : Fin ds.length) :
    (namedMap R).adj x y ↔ R.edge x.val y.val := by
  let e := labelEquiv R
  have tag (i : Fin ds.length) : R.label (e.symm i) = i.val := congrArg Fin.val (e.apply_symm_apply i)
  constructor
  · rintro ⟨z,h⟩
    exact ⟨e.symm x,e.symm y,tag x,tag y,e.symm z,h⟩
  · rintro ⟨a,b,ax,bx,c,h⟩
    obtain rfl : a=e.symm x := R.inj _ _ (ax.trans (tag x).symm)
    obtain rfl : b=e.symm y := R.inj _ _ (bx.trans (tag y).symm)
    refine ⟨e c,?_⟩
    change R.map.face (e.symm x) (e.symm y) (e.symm (e c))
    simpa using h

/-- The graph of every Euler-tight abstract model is planar. The numerical
Euler equality forces coherent orientations through the closed-trace theorem. -/
theorem model_planar {ds : List Nat} (R : Model ds) (valid : TableValid ds) : (Transfer.graph R).Planar := by
  cases ds with
  | nil => have h := valid.1; contradiction
  | cons x xs =>
    let G := Transfer.graph R
    have tight := (Wagner.order_counts G valid (Transfer.graph_realizes R)).2
    exact ReverseTrace.planar_of_tight_map G (namedMap R)
      (fun i j => (named_adj R i j).trans (Transfer.same_edges R i j)) (by simpa using tight)

/-- The graph problem on the left uses the standard forbidden-minor
semantics. The right-hand graph retains each prescribed positional adjacency. -/
theorem planaric_iff (I : Prescription) (valid : BaseValid I) :
    SparseBoundary.Planaric (output I) ↔ ∃ K : SparseBoundary.Graph I.degrees.length,
      K.Realizes I.degrees ∧ K.Planar ∧ ∀ e ∈ I.edges, SourceConverse.natAdj K e.left e.right = true := by
  constructor
  · rintro ⟨G,degs,hp⟩
    obtain ⟨R,required,_⟩ := recover_planar_output I valid G degs hp
    refine ⟨Transfer.graph R,Transfer.graph_realizes R,model_planar R valid.1,?_⟩
    intro e he
    obtain ⟨lt,hr,_⟩ := I.increasing e he
    let i : Fin I.degrees.length := ⟨e.left,lt.trans hr⟩
    let j : Fin I.degrees.length := ⟨e.right,hr⟩
    exact (SourceConverse.natAdj_fin (Transfer.graph R) i j).symm ▸ (Transfer.same_edges R i j).mp (required _ he)
  · rintro ⟨K,degs,planar,required⟩
    obtain ⟨R,same⟩ := Wagner.tight_embedding _ K valid.1 degs planar
    obtain ⟨N⟩ := encode_prescribed I valid R (fun e he => by
      have hr := I.increasing e he
      let i : Fin I.degrees.length := ⟨e.left,hr.1.trans hr.2.1⟩
      let j : Fin I.degrees.length := ⟨e.right,hr.2.1⟩
      exact (same i j).mpr ((SourceConverse.natAdj_fin K i j) ▸ required e he))
    exact ⟨Transfer.graph N,Transfer.graph_realizes N,model_planar N (output_valid I valid)⟩

/-! ## Explicit list size and the boundary cases -/

private theorem order_bound (qs : List Test) (T : Table) :
    (qs.foldl layer T).degrees.length ≤ T.degrees.length * 3^qs.length := by
  induction qs generalizing T with
  | nil => simp
  | cons q qs ih =>
    have h : (layer T q).degrees.length ≤ T.degrees.length*3 := by rw [layer_order]; omega
    apply (ih (layer T q)).trans
    simpa [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm 3] using Nat.mul_le_mul_right (3^qs.length) h

/-- The exponent depends only on the number of colours. -/
theorem output_polynomial (I : Prescription) (pos : 0 < I.degrees.length) :
    (output I).length ≤ 3^(3+6*I.colours) * I.degrees.length^(8*I.colours+1) := by
  let s := I.degrees.length
  let k := I.colours
  have schedules : (allLayers I).length = 3+k*(2+4*bitWidth s) := by
    have each (xs : List Nat) : (xs.flatMap (fun c => classTests (bitWidth s) (matchingClass I c))).length =
        xs.length*(2+4*bitWidth s) := by
      induction xs with
      | nil => simp
      | cons c cs ih => simp [ih,classTests_length,Nat.succ_mul,Nat.add_comm]
    rw [allLayers,List.length_append]
    change 3+(tests I).length = _
    apply congrArg (3+·)
    simpa only [tests,k,s,List.length_range] using each (List.range k)
  have bound := order_bound (allLayers I) ⟨I.degrees,0⟩
  change (output I).length ≤ s * 3^(allLayers I).length at bound
  have hlog : 2^s.log2 ≤ s := (Nat.le_log2 (Nat.ne_of_gt pos)).mp (Nat.le_refl _)
  have exp : 3+k*(2+4*bitWidth s) = (3+6*k)+(4*k)*s.log2 := by unfold bitWidth; ring
  have growth : 3^((4*k)*s.log2) ≤ s^(8*k) := calc
    _ ≤ (2^2)^((4*k)*s.log2) := Nat.pow_le_pow_left (by decide) _
    _ = (2^s.log2)^(8*k) := by rw [←Nat.pow_mul,←Nat.pow_mul]; congr 1; ring
    _ ≤ s^(8*k) := Nat.pow_le_pow_left hlog _
  rw [schedules,exp,Nat.pow_add] at bound
  exact bound.trans (by
    calc
      _ ≤ s*(3^(3+6*k)*s^(8*k)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ growth)
      _ = _ := by change _ = 3^(3+6*k)*s^(8*k+1); rw [Nat.pow_succ]; ring)

open SparseBoundary Wagner

/-- This version directly handles order four and the impossible edge count.
A local demand exceeding the target degree is already rejected by the
ordinary case of `planaric_iff`. -/
def compile (I : Prescription) : List Nat :=
  if I.degrees.length = 4 ∨ I.edges = [] then I.degrees
  else if I.edges.length ≤ 3*I.degrees.length-6 then output I else malformedOutput

private def Required (I : Prescription) (K : Graph I.degrees.length) :=
  ∀ e ∈ I.edges, SourceConverse.natAdj K e.left e.right = true

private theorem required_count (I : Prescription) (K : Graph I.degrees.length) (req : Required I K) :
    I.edges.length ≤ Nat.card (toSimple K).edgeSet := by
  classical
  let E := {e // e ∈ I.edges.toFinset}
  have inside (e : E) : e.val ∈ I.edges := List.mem_toFinset.mp e.property
  let l (e : E) : Fin I.degrees.length := ⟨e.val.left,(I.increasing _ (inside e)).1.trans (I.increasing _ (inside e)).2.1⟩
  let r (e : E) : Fin I.degrees.length := ⟨e.val.right,(I.increasing _ (inside e)).2.1⟩
  let f (e : E) : (toSimple K).edgeSet := ⟨s(l e,r e), by
    change K.adj (l e) (r e) = true
    rw [← SourceConverse.natAdj_fin]; exact req _ (inside e)⟩
  have injective : Function.Injective f := by
    intro a b same
    have pair := Sym2.eq_iff.mp (congrArg Subtype.val same)
    change l a=l b ∧ r a=r b ∨ l a=r b ∧ r a=l b at pair
    have orderA := (I.increasing _ (inside a)).1
    have orderB := (I.increasing _ (inside b)).1
    simp only [l,r,Fin.mk.injEq] at pair
    have L : a.val.left=b.val.left := by omega
    have R : a.val.right=b.val.right := by omega
    have col := I.sameColour _ (inside a) _ (inside b) L R
    apply Subtype.ext
    have ext {x y : Edge} : x.left=y.left → x.right=y.right → x.color=y.color → x=y := by
      cases x; cases y; grind
    exact ext L R col
  have card : Nat.card E = I.edges.length := by
    rw [Nat.card_eq_fintype_card]
    exact (Fintype.card_coe I.edges.toFinset).trans (List.toFinset_card_of_nodup I.unique)
  exact card ▸ Nat.card_le_card_of_injective f injective

/-- Exactness of the total ordinary graph compiler on every admissible
Euler-tight row of order at least four. -/
theorem compile_iff (I : Prescription) (size : 4 ≤ I.degrees.length)
    (total : I.degrees.sum+12 = 6*I.degrees.length)
    (range : ∀ d ∈ I.degrees, 3 ≤ d ∧ d < I.degrees.length) :
    Planaric (compile I) ↔ ∃ K : Graph I.degrees.length, K.Realizes I.degrees ∧ K.Planar ∧
      ∀ e ∈ I.edges, SourceConverse.natAdj K e.left e.right = true := by
  classical
  by_cases id : I.degrees.length=4 ∨ I.edges=[]
  · rw [compile,ite_eq_left id]
    constructor
    · rintro ⟨K,ds,planar⟩
      refine ⟨K,ds,planar,?_⟩
      intro e he
      rcases id with four | empty
      · obtain ⟨ab,bn,_⟩ := I.increasing e he
        let a : Fin I.degrees.length := ⟨e.left,ab.trans bn⟩
        let b : Fin I.degrees.length := ⟨e.right,bn⟩
        have high := range _ (List.getElem_mem a.isLt)
        have near : (toSimple K).degree a = Fintype.card (Fin I.degrees.length)-1 := by
          rw [←SimpleGraph.card_neighborSet_eq_degree,←Nat.card_eq_fintype_card]
          change Nat.card {b // (toSimple K).Adj a b} = _
          rw [neighbor_count,ds a]
          rw [Fintype.card_fin]
          change I.degrees[a.val] = I.degrees.length-1
          omega
        have uni := ((toSimple K).degree_eq_card_sub_one a).mp near
        exact (SourceConverse.natAdj_fin K a b).symm ▸ (uni (by exact Fin.ne_of_lt ab : a ≠ b))
      · simp [empty] at he
    · rintro ⟨K,ds,planar,_⟩; exact ⟨K,ds,planar⟩
  · have valid : TableValid I.degrees := ⟨by omega,total,range⟩
    rw [compile,ite_eq_right id]
    split
    next few => exact planaric_iff I ⟨valid,few⟩
    next many =>
      constructor
      · exact fun h => (Promise.malformed_no h).elim
      · rintro ⟨K,degs,_,required⟩
        have count := (order_counts K valid degs).2
        rw [Nat.card_fin] at count
        have bound := required_count I K required
        omega

/-- Uncoloured, simply listed prescriptions enter the compiler directly by
first-fit edge colouring. -/
theorem uncoloured_iff (ds : List Nat) (rows : List (Nat × Nat)) (c : Nat)
    (ordered : ∀ p ∈ rows, p.1 < p.2 ∧ p.2 < ds.length) (nd : rows.Nodup)
    (deg : ∀ v, incidence rows v ≤ c) (size : 4 ≤ ds.length)
    (total : ds.sum+12=6*ds.length) (range : ∀ d ∈ ds, 3≤d ∧ d<ds.length) :
    Planaric (compile (ofPairs ds rows c ordered nd deg)) ↔
      ∃ K : Graph ds.length, K.Realizes ds ∧ K.Planar ∧ ∀ p ∈ rows, SourceConverse.natAdj K p.1 p.2 = true := by
  rw [compile_iff _ size total range]
  apply exists_congr
  intro K
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  change (∀ e ∈ paint rows, SourceConverse.natAdj K (ends e).1 (ends e).2 = true) ↔ _
  constructor
  · intro h p hp
    have member : p ∈ (paint rows).map ends := by simpa only [paint_ends] using hp
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp member
    exact h e he
  · intro h e he
    exact h (ends e) (paint_ends rows ▸ List.mem_map.mpr ⟨e,he,rfl⟩)

/-- An actual sequence of face subdivisions starting at the indicated map. -/
inductive Extension {V : Type} (base : Rigidity.Map V) : {W : Type} → Rigidity.Map W → Prop where
  | refl : Extension base base
  | subdivide {W : Type} {M : Rigidity.Map W} (prior : Extension base M) (fill : Choice W) :
      Extension base (stack M fill)

/-- The successful output can extend the very input realization supplied. -/
theorem encode_extends (I : Prescription) (v : BaseValid I) (R : Model I.degrees)
    (req : ∀ e ∈ I.edges, R.edge e.left e.right) : ∃ N : Model (output I), Extension R.map N.map :=
  encode_preserving (Extension R.map) (fun _ fill prior => .subdivide prior fill) I v R .refl req

/-- Uniform size estimate for every branch, including the fixed negative output. -/
theorem compile_polynomial (I : Prescription) (size : 4 ≤ I.degrees.length) :
    (compile I).length ≤ 3^(3+6*I.colours) * I.degrees.length^(8*I.colours+1) := by
  have coeff : 27 ≤ 3^(3+6*I.colours)  := Nat.pow_le_pow_right (by decide : 0 < 3) (Nat.le_add_right 3 _)
  have power : I.degrees.length ≤ I.degrees.length^(8*I.colours+1) := by
    simpa only [Nat.pow_one] using Nat.pow_le_pow_right (by omega : 0 < I.degrees.length)
      (show 1 ≤ 8*I.colours+1 by omega)
  have lo := Nat.mul_le_mul coeff power
  unfold compile
  split
  · omega
  · split
    · exact output_polynomial I (by omega)
    · change 6 ≤ _; omega

end Recognition.EliminationResult
