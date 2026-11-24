import Triangulation.Cover
import Triangulation.FaceTests
import Triangulation.Provenance

namespace Recognition.Forward
open Recognition.Rigidity Recognition.Reduction Recognition.Layers Recognition.Stacking

variable {T : Table} {q : Test} (R : Model T.degrees)

private noncomputable def atLabel (i : Nat) (h : i < T.degrees.length) : R.V :=
  Classical.choose ((R.hits _).mp h)

private theorem at_label (i : Nat) (h : i < T.degrees.length) : R.label (atLabel R i h) = i :=
  Classical.choose_spec ((R.hits _).mp h)

private theorem lift_edge {i j : Nat} (h : R.edge i j) (a b : R.V)
    (ha : R.label a = i) (hb : R.label b = j) : R.map.adj a b := by
  obtain ⟨x,y,hx,hy,e⟩ := h
  exact R.inj x a (hx.trans ha.symm) ▸ R.inj y b (hy.trans hb.symm) ▸ e

private theorem four_vertices (h : 4 ≤ T.degrees.length) (x y z : R.V) :
    ∃ w, w ≠ x ∧ w ≠ y ∧ w ≠ z := by
  obtain ⟨i,hi,a,b,c⟩ := choose_old T.degrees.length (R.label x) (R.label y) (R.label z) h
  refine ⟨atLabel R i hi,?_⟩
  have := at_label R i hi
  grind

/-- The ordering of a fresh generation is free. The given distinct prefix is
followed by all remaining stars in their enumeration order. -/
private noncomputable def prioritize {U : Type} (E : Enumeration U) (prefixes : List U) : List U := by
  classical
  exact prefixes ++ E.vertices.filter fun x => decide (x ∉ prefixes)

private theorem priority_mem {U : Type} (E : Enumeration U) (xs : List U) (v : U) :
    v ∈ prioritize E xs := by
  classical
  by_cases h : v ∈ xs <;> simp [prioritize,h,E.complete]

private theorem priority_unique {U : Type} (E : Enumeration U) (xs : List U) (h : xs.Nodup) :
    (prioritize E xs).Nodup := by
  classical
  refine List.nodup_append.mpr ⟨h,List.filter_sublist.nodup E.unique,?_⟩
  intro a ha b hb eq
  obtain rfl := eq
  exact (of_decide_eq_true (List.mem_filter.mp hb).2) ha

private theorem priority_length {U : Type} (E : Enumeration U) (xs : List U) (h : xs.Nodup) :
    (prioritize E xs).length = E.vertices.length := by
  classical
  apply List.Perm.length_eq
  apply List.perm_iff_count.mpr
  intro a
  rw [(priority_unique E xs h).count,E.unique.count]
  simp [priority_mem,E.complete]

private noncomputable def number {O : Omission R q} (xs : List (Star R.map O.fill)) :
    Vertex R.map O.fill → Nat := by
  classical
  let order := prioritize (starEnumeration R.map O.fill R.vertices) xs
  exact Sum.elim R.label (fun s => T.degrees.length + order.idxOf s)

noncomputable def extend {O : Omission R q} (xs : List (Star R.map O.fill)) (nd : xs.Nodup)
    (v : TableValid T.degrees) (labels : (selectedLabels T q).Nodup)
    (bounded : ∀ i ∈ selectedLabels T q, i < T.degrees.length) : Model (layer T q).degrees := by
  classical
  let M := R.map
  let E := R.vertices
  let S := starEnumeration M O.fill E
  let n := T.degrees.length
  let order := prioritize S xs
  have four := four_vertices R (by have := v.1; omega)
  let marked := fun a : R.V => (selectedLabels T q).contains (R.label a)
  have hit (a : R.V) : marked a = true ↔ ∃ b c, vacant M O.fill a b c := by
    simpa [marked,List.contains_iff_mem] using O.hits a
  have euler : mass E.vertices (degree (M := M) E) + 12 = 6*E.vertices.length := by
    have size := (label_perm R).length_eq
    simp at size
    have e : mass E.vertices (degree (M := M) E) = T.degrees.sum := by
      unfold mass
      rw [List.map_congr_left (fun a _ => R.value a)]
      change mass R.vertices.vertices (fun a => T.degrees[R.label a]?.getD 0) = T.degrees.sum
      rw [label_sum R (fun i => T.degrees[i]?.getD 0)]
      exact mass_get _ 0
    rw [e]; exact size ▸ v.2.1
  have bits : mass E.vertices (fun a => if marked a then 1 else 0) = 3*q.group.length := by
    have eq (a : R.V) : (if marked a then 1 else 0) = (marked a).toNat := by cases marked a <;> rfl
    unfold mass
    rw [List.map_congr_left (fun a _ => eq a)]
    change mass R.vertices.vertices (fun a => ((selectedLabels T q).contains (R.label a)).toNat) = _
    rw [label_sum R (fun i => ((selectedLabels T q).contains i).toNat), selected_mass _ labels _ bounded,label_count]
  have len := forward_length M O.fill four E marked hit O.disjoint q.group.length bits euler
  have eq : order.length = 2*n-4-q.group.length := by
    have el := (label_perm R).length_eq
    simp at el
    change S.vertices.length + _ + _ = 2 * R.vertices.vertices.length at len
    have ord := priority_length S xs nd
    change (prioritize S xs).length = 2*T.degrees.length-4-q.group.length
    omega
  have lenTotal : (layer T q).degrees.length = n+order.length := by rw [layer_order,eq]
  have small (s : Star M O.fill) : order.idxOf s < order.length :=
    List.idxOf_lt_length_of_mem (priority_mem S xs s)
  let lab := number R (O := O) xs
  refine {
    V := Vertex M O.fill
    map := stack M O.fill
    vertices := enumeration M O.fill E
    label := lab
    inj := ?_
    hits := ?_
    value := ?_
  }
  · intro x y e
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (R.inj _ _ e)
      | inr b =>
        change R.label a = n+order.idxOf b at e
        have h : R.label a < n := bound R a
        omega
    | inr a =>
      cases y with
      | inl b =>
        change n+order.idxOf a = R.label b at e
        have h : R.label b < n := bound R b
        omega
      | inr b =>
        change n+order.idxOf a = n+order.idxOf b at e
        have same := Nat.add_left_cancel e
        have h₁ := List.getElem_idxOf (xs := order) (x := a) (small a)
        have h₂ := List.getElem_idxOf (xs := order) (x := b) (small b)
        exact congrArg Sum.inr (by grind)
  · intro i
    constructor
    · intro hi
      by_cases h : i < n
      · obtain ⟨a,ha⟩ := (R.hits _).mp h
        exact ⟨.inl a,ha⟩
      · have b : i-n < order.length := by omega
        let s := order[i-n]
        have iz := (priority_unique S xs nd).idxOf_getElem (i := i-n) b
        change order.idxOf order[i-n] = i-n at iz
        exact ⟨.inr s,by change n+order.idxOf order[i-n] = i; omega⟩
    · rintro ⟨x,e⟩
      cases x with
      | inl x =>
        have h : R.label x < n := bound R x
        change R.label x = i at e
        omega
      | inr s =>
        change n+order.idxOf s = i at e
        have := small s; omega
  · intro x
    cases x with
    | inl a =>
      have h := forward_layer M O.fill four E marked hit O.disjoint a
      have old : degree (M := M) E a = _ := R.value a
      have hmark : (if marked a then 1 else 0) = ((selectedLabels T q).contains (R.label a)).toNat := by
        change (if marked a then 1 else 0) = (marked a).toNat
        cases marked a <;> rfl
      rw [hmark] at h
      change degree (M := stack M O.fill) _ _ = (layer T q).degrees[R.label a]?.getD 0
      rw [old_value _ _ (bound R a)]
      omega
    | inr s =>
      rw [new_degree]
      apply Eq.symm
      apply new_value
      · exact Nat.le_add_right ..
      · change n+order.idxOf s < _
        have := small s; omega


theorem ofFn_unique {m : Nat} {U : Type} (f : Fin m → U) (inj : ∀ i j, f i = f j → i = j) :
    (List.ofFn f).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj e
  simp only [List.getElem_ofFn] at e
  exact congrArg Fin.val (inj _ _ e)

private theorem first_names {O : Omission R q} {k : Nat} (f : Fin k → Star R.map O.fill)
    (nd : (List.ofFn f).Nodup) (i : Fin k) :
    number R (O := O) (List.ofFn f) (.inr (f i)) = T.degrees.length+i.val := by
  classical
  let xs := List.ofFn f
  change T.degrees.length + (prioritize _ xs).idxOf (f i) = _
  have hi : i.val < xs.length := by simp [xs]
  have e : xs[i.val] = f i := by simp [xs]
  have member : f i ∈ xs := e ▸ List.getElem_mem hi
  have pos := nd.idxOf_getElem (i := i.val) hi
  simp only [List.getElem_ofFn] at pos
  change xs.idxOf (f i) = i.val at pos
  simp [prioritize,List.idxOf_append,member,pos]

/-- Priority names in a fresh generation, as read from the extended model. -/
theorem extend_names {O : Omission R q} {k : Nat} (f : Fin k → Star R.map O.fill)
    (nd : (List.ofFn f).Nodup) (v : TableValid T.degrees)
    (labels : (selectedLabels T q).Nodup)
    (bounded : ∀ i ∈ selectedLabels T q, i < T.degrees.length) (i : Fin k) :
    (extend R (O := O) (List.ofFn f) nd v labels bounded).label (.inr (f i)) =
      T.degrees.length + i.val :=
  first_names R f nd i

theorem extend_edges {O : Omission R q} (xs : List (Star R.map O.fill)) (nd : xs.Nodup)
    (v : TableValid T.degrees) (labels : (selectedLabels T q).Nodup)
    (bounded : ∀ i ∈ selectedLabels T q, i < T.degrees.length) {i j} (h : R.edge i j) :
    (extend R (O := O) xs nd v labels bounded).edge i j := by
  obtain ⟨x,y,hx,hy,e⟩ := h
  exact ⟨.inl x,.inl y,hx,hy,(old_edges R.map O.fill x y).mpr e⟩

def Marked (I : Instance) (R : Model T.degrees) :=
  ∀ a ∈ marks I, R.edge a.marker a.edge.left ∧ R.edge a.marker a.edge.right

private theorem keep_marked {I : Instance} (h : Marked I R) {O : Omission R q}
    (xs : List (Star R.map O.fill)) (nd : xs.Nodup) (v : TableValid T.degrees)
    (labels : (selectedLabels T q).Nodup) (bounded : ∀ i ∈ selectedLabels T q, i < T.degrees.length) :
    Marked I (extend R (O := O) xs nd v labels bounded) := by
  intro a ha
  exact ⟨extend_edges R xs nd v labels bounded (h a ha).1,
    extend_edges R xs nd v labels bounded (h a ha).2⟩

theorem separate {U : Table} (r : Test) (nd : (selectedLabels U r).Nodup)
    (i j : Fin r.group.length) (ne : i ≠ j) :
    r.group[i.val].marker ≠ r.group[j.val].marker ∧
    r.group[i.val].marker ≠ endpoint r.side r.group[j.val] ∧
    endpoint r.side r.group[i.val] ≠ r.group[j.val].marker ∧
    endpoint r.side r.group[i.val] ≠ endpoint r.side r.group[j.val] := by
  obtain ⟨both,_,_⟩ := List.nodup_append.mp nd
  obtain ⟨m,e,cross⟩ := List.nodup_append.mp both
  have M (k : Fin r.group.length) : r.group[k.val].marker ∈ r.group.map Mark.marker :=
    List.mem_map.mpr ⟨_,List.getElem_mem k.isLt,rfl⟩
  have E (k : Fin r.group.length) : endpoint r.side r.group[k.val] ∈ r.group.map (endpoint r.side) :=
    List.mem_map.mpr ⟨_,List.getElem_mem k.isLt,rfl⟩
  refine ⟨?_,cross _ (M i) _ (E j),Ne.symm (cross _ (M j) _ (E i)),?_⟩
  · intro same
    apply ne
    exact Fin.ext (List.nodup_iff_eq_of_getElem_eq.mp m _ _ (by simp) (by simp) (by simpa using same))
  · intro same
    apply ne
    exact Fin.ext (List.nodup_iff_eq_of_getElem_eq.mp e _ _ (by simp) (by simp) (by simpa using same))

/-- Choose the newly introduced vertices for the next test before numbering
this fresh generation. This keeps every earlier marker and endpoint fixed. -/
private theorem lookahead (P : {V : Type} → Map V → Prop)
    (lift : ∀ {V : Type} (M : Map V) (fill : Choice V), P M → P (stack M fill))
    (previous : P R.map) (I : Instance) {O : Omission R q}
    (v : TableValid T.degrees) (labels : (selectedLabels T q).Nodup)
    (bounded : ∀ i ∈ selectedLabels T q, i < T.degrees.length)
    (h : Marked I R) (r : Test) (hr : r ∈ schedule I)
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
    labZ := first_names R f nd
    face := faces
  }


private theorem finish (P : {V : Type} → Map V → Prop)
    (lift : ∀ {V : Type} (M : Map V) (fill : Choice V), P M → P (stack M fill))
    (I : Instance) {T : Table} {q qs Z} (R : Model T.degrees)
    (previous : P R.map) (O : Omission R q) (marksReady : Marked I R) (run : Run T (q::qs) Z)
    (sub : qs ⊆ schedule I) : ∃ N : Model Z.degrees, P N.map := by
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
    (I : Instance) (A : Table) (eq : A.degrees = sourceTable I)
    (R : Model A.degrees) (previous : P R.map) (v : TableValid A.degrees)
    (pres : ∀ e ∈ prescribed I, R.edge e.left e.right) :
    ∃ N : Model (layer (layer A full) full).degrees, P N.map ∧ Marked I N := by
  classical
  let T1 := layer A full
  let all := allFaces R
  let U := extend R (O := all) [] (by simp) v (full_labels A).1 (full_labels A).2
  let V1 := valid_layer A full v (full_labels A).1 (full_labels A).2
  let all' := allFaces U
  let edges := prescribed I
  let e (i : Fin edges.length) := edges[i.val]
  have em (i : Fin edges.length) : e i ∈ prescribed I := List.getElem_mem i.isLt
  have edge i := pres _ (em i)
  let x i := (edge i).choose
  let y i := (edge i).choose_spec.choose
  have lx i : R.label (x i) = (e i).left := (edge i).choose_spec.choose_spec.1
  have ly i : R.label (y i) = (e i).right := (edge i).choose_spec.choose_spec.2.1
  have non (i : Fin edges.length) := (edges_bounds I _ (em i)).1
  have same (i j : Fin edges.length) (p : (x i=x j ∧ y i=y j) ∨ (x i=y j ∧ y i=x j)) :
      i = j := by
    have l₁ := lx i; have l₂ := lx j; have r₁ := ly i; have r₂ := ly j
    have lo := non i; have hi := non j
    have al : (e i).left = (e j).left := by grind
    have ar : (e i).right = (e j).right := by grind
    have ac : (e i).color = (e j).color := by
      rw [prescribed_color I _ (em i),prescribed_color I _ (em j),al,ar]
    have ext {a b : Edge} : a.left=b.left → a.right=b.right → a.color=b.color → a=b := by cases a; cases b; grind
    have ee : e i = e j := ext al ar ac
    exact Fin.ext (List.nodup_iff_eq_of_getElem_eq.mp (prescribed_nd I) _ _ i.isLt j.isLt ee)
  obtain ⟨marker,injective,neighbors⟩ := FaceTests.prepare_markers R.map x y (fun i => (edge i).choose_spec.choose_spec.2.2) same
  have nd := ofFn_unique marker injective
  let N := extend (T := T1) U (O := all') (List.ofFn marker) nd V1 (full_labels T1).1 (full_labels T1).2
  have tag (i : Fin edges.length) :
      N.label (.inr (marker i)) = fullOrder (sourceTable I).length + i.val := by
    have h := first_names (T := T1) U (O := all') marker nd i
    change N.label (.inr (marker i)) = T1.degrees.length + i.val at h
    rw [show T1.degrees.length = fullOrder (sourceTable I).length from (full_length A).trans (congrArg (fun xs : List Nat => fullOrder xs.length) eq)] at h
    exact h
  refine ⟨N,lift U.map all'.fill (lift R.map all.fill previous),?_⟩
  intro m hm
  obtain ⟨k,hk,hmk⟩ := List.mem_iff_getElem.mp hm
  have hk' : k < edges.length := by simpa [marks,edges] using hk
  let i : Fin edges.length := ⟨k,hk'⟩
  have idEdge : m.edge = e i := by simpa [marks,e,edges,i,List.getElem_zipIdx] using congrArg Mark.edge hmk.symm
  have idMark : m.marker = fullOrder (sourceTable I).length + i.val := by
    simpa [marks,i,List.getElem_zipIdx] using congrArg Mark.marker hmk.symm
  have key : N.label (.inr (marker i)) = m.marker := (tag i).trans idMark.symm
  constructor
  · exact ⟨.inr (marker i),.inl (.inl (x i)),key,(lx i).trans (congrArg Edge.left idEdge.symm),
      (neighbors i (x i)).mpr (Or.inl rfl)⟩
  · exact ⟨.inr (marker i),.inl (.inl (y i)),key,(ly i).trans (congrArg Edge.right idEdge.symm),
      (neighbors i (y i)).mpr (Or.inr rfl)⟩

theorem encode_preserving (P : {V : Type} → Map V → Prop)
    (lift : ∀ {V : Type} (M : Map V) (fill : Choice V), P M → P (stack M fill))
    (I : Instance) (valid : Valid I) (R : Model (sourceTable I))
    (previous : P R.map) (pres : ∀ e ∈ prescribed I, R.edge e.left e.right) :
    ∃ N : Model (encode I), P N.map := by
  let T0 : Table := ⟨sourceTable I,0⟩
  let T2 := layer (layer T0 full) full
  obtain ⟨M,hp,h⟩ := name_markers P lift I T0 rfl R previous (source_valid I valid) pres
  let Z := (allTests I).foldl layer T0
  have program := compilation_run I valid
  change Run T0 (full :: full :: full :: schedule I) Z at program
  have cut {A : Table} {t ts Z} (run : Run A (t::ts) Z) : Run (layer A t) ts Z := by cases run; assumption
  have remaining : Run T2 (full :: schedule I) Z := cut (cut program)
  exact finish P lift I M hp (allFaces M) h remaining (fun _ h => h)

theorem encode_prescribed (I : Instance) (valid : Valid I) (R : Model (sourceTable I))
    (pres : ∀ e ∈ prescribed I, R.edge e.left e.right) : Nonempty (Model (encode I)) := by
  obtain ⟨N,_⟩ := encode_preserving (fun _ => True) (fun _ _ _ => trivial) I valid R trivial pres
  exact ⟨N⟩

theorem encode_stacked (I : Instance) (valid : Valid I) (R : Model (sourceTable I))
    (previous : StackedMap R.map) (pres : ∀ e ∈ prescribed I, R.edge e.left e.right) :
    ∃ N : Model (encode I), StackedMap N.map :=
  encode_preserving StackedMap (fun _ fill prev => .subdivide prev fill) I valid R previous pres

theorem compiler_iff (I : Instance) (valid : Valid I) :
    Nonempty (Model (encode I)) ↔ ∃ R : Model (sourceTable I), ∀ e ∈ prescribed I, R.edge e.left e.right :=
  ⟨fun ⟨R⟩ => decode_prescribed I valid R,fun ⟨R,h⟩ => encode_prescribed I valid R h⟩

#print axioms encode_stacked
#print axioms encode_prescribed
#print axioms compiler_iff

end Recognition.Forward
