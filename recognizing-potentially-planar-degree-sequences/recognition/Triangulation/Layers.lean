import Triangulation.Rigidity
import Reduction

namespace Recognition.Layers
open Recognition.Rigidity Recognition.Reduction

/-- Labels survive every peeling. The enumeration itself may have arbitrary order. -/
structure Model (ds : List Nat) where
  V : Type
  map : Map V
  vertices : Enumeration V
  label : V → Nat
  inj : ∀ x y, label x = label y → x = y
  hits : ∀ i, i < ds.length ↔ ∃ x, label x = i
  value : ∀ x, degree (M := map) vertices x = ds[label x]?.getD 0

variable {ds : List Nat} (R : Model ds)

def Model.edge (i j : Nat) := ∃ x y, R.label x = i ∧ R.label y = j ∧ R.map.adj x y
def Model.triangle (i j k : Nat) :=
  ∃ x y z, R.label x = i ∧ R.label y = j ∧ R.label z = k ∧ R.map.face x y z

theorem bound (x : R.V) : R.label x < ds.length := (R.hits _).mpr ⟨x,rfl⟩

private theorem perm_of_mem {U : Type} (xs ys : List U) (a : xs.Nodup) (b : ys.Nodup)
    (h : ∀ x, x ∈ xs ↔ x ∈ ys) : xs.Perm ys := by
  classical
  apply List.perm_iff_count.mpr
  intro x
  simp only [a.count,b.count,h]

theorem label_perm : (R.vertices.vertices.map R.label).Perm (List.range ds.length) := by
  apply perm_of_mem
  · exact List.pairwise_map.mpr (R.vertices.unique.imp fun {x y} ne e => ne (R.inj x y e))
  · exact List.nodup_range
  · intro i
    simp only [List.mem_map,List.mem_range]
    rw [R.hits]
    constructor
    · rintro ⟨x,_,h⟩
      exact ⟨x,h⟩
    · rintro ⟨x,h⟩
      exact ⟨x,R.vertices.complete _,h⟩

theorem label_sum (f : Nat → Nat) :
    mass R.vertices.vertices (fun x => f (R.label x)) = mass (List.range ds.length) f := by
  simpa [mass,List.map_map,Function.comp_def] using ((label_perm R).map f).sum_nat

private theorem const_mass {U : Type} (xs : List U) (k : Nat) : mass xs (fun _ => k) = xs.length*k := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih => simpa [mass,Nat.succ_mul,Nat.add_comm] using congrArg (fun n => k+n) ih

theorem mass_get (xs : List Nat) (k : Nat) :
    mass (List.range (xs.length+k)) (fun i => xs[i]?.getD 0) = xs.sum := by
  have eq : (List.range xs.length).map (fun i => xs[i]?.getD 0) = xs := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp [List.getElem?_eq_getElem hi']
  have tail : (List.range k).map (fun i => xs[xs.length+i]?.getD 0) = (List.range k).map (fun _ => 0) := by
    apply List.map_congr_left
    intro i _
    simp
  unfold mass
  rw [List.range_add,List.map_append,List.map_map,List.sum_append,eq]
  simp only [Function.comp_def]
  rw [tail,show ((List.range k).map (fun _ => 0)).sum = 0 by simpa [mass] using const_mass (List.range k) 0,Nat.add_zero]

theorem selected_mass (labels : List Nat) (nd : labels.Nodup) (N : Nat)
    (small : ∀ x ∈ labels, x < N) :
    mass (List.range N) (fun x => (labels.contains x).toNat) = labels.length := by
  let p := fun x => labels.contains x
  have sum (xs : List Nat) : mass xs (fun x => (p x).toNat) = (xs.filter p).length := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      cases e : p a <;> simpa [mass,e,List.filter_cons,Nat.add_comm] using ih
  rw [sum]
  exact (perm_of_mem _ _ (List.filter_sublist.nodup List.nodup_range) nd (by
    intro x
    simp only [List.mem_filter,List.mem_range,p,List.contains_iff_mem]
    exact ⟨And.right,fun h => ⟨small _ h,h⟩⟩)).length_eq

private theorem range_tail (n k : Nat) :
    mass (List.range (n+k)) (fun i => mark (n ≤ i)) = k := by
  unfold mass
  rw [List.range_add,List.map_append,List.map_map,List.sum_append]
  have z := List.map_congr_left (l := List.range n) (f := fun i => mark (n ≤ i)) (g := fun _ => 0)
    (fun i h => by have := List.mem_range.mp h; simp [mark,show ¬n ≤ i by omega])
  have o := List.map_congr_left (l := List.range k) (f := fun i => mark (n ≤ n+i)) (g := fun _ => 1)
    (fun i _ => by simp [mark])
  simp only [Function.comp_def]
  rw [z,o]
  change mass (List.range n) (fun _ => 0) + mass (List.range k) (fun _ => 1) = k
  simp [const_mass]

variable (T : Table) (q : Test)

private def K := 2*T.degrees.length-4-q.group.length

theorem new_value {i : Nat} (h : T.degrees.length ≤ i) (b : i < (layer T q).degrees.length) :
    (layer T q).degrees[i]?.getD 0 = 3 := by
  rw [List.getElem?_eq_getElem b]
  simp only [Option.getD_some]
  unfold layer at *
  exact (List.getElem_append_right (by simpa [raised] using h)).trans (List.getElem_replicate _)

theorem old_value {i : Nat} (h : i < T.degrees.length) :
    (layer T q).degrees[i]?.getD 0 =
      2*(T.degrees[i]?.getD 0) - ((selectedLabels T q).contains i).toNat := by
  have b : i < (layer T q).degrees.length := by rw [layer_order]; omega
  simp only [List.getElem?_eq_getElem b,List.getElem?_eq_getElem h,Option.getD_some]
  unfold layer at *
  simp only [List.getElem_append_left (by simpa [raised] using h : i < (raised T.degrees (selectedLabels T q)).length)]
  simp [raised,List.getElem_zipIdx]

theorem choose_old (n x y z : Nat) (h : 4 ≤ n) : ∃ w, w < n ∧ w ≠ x ∧ w ≠ y ∧ w ≠ z := by
  by_cases h₀ : 0 ≠ x ∧ 0 ≠ y ∧ 0 ≠ z
  · exact ⟨0,by omega⟩
  by_cases h₁ : 1 ≠ x ∧ 1 ≠ y ∧ 1 ≠ z
  · exact ⟨1,by omega⟩
  by_cases h₂ : 2 ≠ x ∧ 2 ≠ y ∧ 2 ≠ z
  · exact ⟨2,by omega⟩
  exact ⟨3,by omega⟩

private def peeling (R : Model (layer T q).degrees) (h : TableValid T.degrees) : Peeling R.map where
  fresh v := T.degrees.length ≤ R.label v
  cubic v hv := (cubic_iff_degree R.vertices v).mpr ((R.value v).trans (new_value T q hv (bound R v)))
  fourOld x y z := by
    have := h.1
    obtain ⟨i,hi,hx,hy,hz⟩ := choose_old T.degrees.length (R.label x) (R.label y) (R.label z) (by omega)
    have hh : i < (layer T q).degrees.length := by rw [layer_order]; omega
    obtain ⟨w,hw⟩ := (R.hits i).mp hh
    exact ⟨w,by grind⟩


structure Step (R : Model (layer T q).degrees) where
  base : Model T.degrees
  selectedBound : ∀ i ∈ selectedLabels T q, i < T.degrees.length
  edges : ∀ i j, i < T.degrees.length → j < T.degrees.length → (base.edge i j ↔ R.edge i j)
  vacancy : ∀ i ∈ selectedLabels T q, ∃ j ∈ selectedLabels T q, ∃ k ∈ selectedLabels T q,
    R.triangle i j k
  allOld : ∀ i j k, i < T.degrees.length → j < T.degrees.length → k < T.degrees.length →
    R.triangle i j k → i ∈ selectedLabels T q
  independent : ∀ i j, T.degrees.length ≤ i → T.degrees.length ≤ j → ¬ R.edge i j
  star : ∀ i, T.degrees.length ≤ i → i < (layer T q).degrees.length →
    ∃ a b c, a < T.degrees.length ∧ b < T.degrees.length ∧ c < T.degrees.length ∧
      base.triangle a b c ∧ ∀ j, R.edge i j ↔ j = a ∨ j = b ∨ j = c

theorem reverse_step (R : Model (layer T q).degrees) (valid : TableValid T.degrees)
    (nodup : (selectedLabels T q).Nodup)
    (bounded : ∀ i ∈ selectedLabels T q, i < T.degrees.length) :
    Nonempty (Step T q R) := by
  let P := peeling T q R valid
  let n := T.degrees.length
  let L := selectedLabels T q
  let target := fun x : R.V => T.degrees[R.label x]?.getD 0
  let bit := fun x : R.V => (L.contains (R.label x)).toNat
  have F (x : R.V) : P.fresh x ↔ n ≤ R.label x := Iff.rfl
  have nh : 5 ≤ n := valid.1
  have NB : ∀ i ∈ L, i < n := bounded
  have deg (a : P.Old) : degree (M := R.map) R.vertices a.val + bit a.val = 2 * target a.val := by
    have h : R.label a.val < n := Nat.lt_of_not_ge a.property
    have positive := (valid.2.2 _ (List.getElem_mem (l := T.degrees) h)).1
    have val := (R.value a.val).trans (old_value T q h)
    simp only [List.getElem?_eq_getElem h,Option.getD_some] at val
    simp only [target,List.getElem?_eq_getElem h,Option.getD_some,bit,L]
    have := Bool.toNat_le ((selectedLabels T q).contains (R.label a.val))
    omega
  have lengthEq : (layer T q).degrees.length = n + K T q := layer_order T q
  have cost : mass R.vertices.vertices target = T.degrees.sum := by
    rw [show mass R.vertices.vertices target = _ from label_sum R (fun i => T.degrees[i]?.getD 0),lengthEq]
    exact mass_get _ _
  have selected : mass R.vertices.vertices bit = 3*q.group.length := by
    change mass R.vertices.vertices (fun x => (L.contains (R.label x)).toNat) = _
    rw [label_sum R (fun i => (L.contains i).toNat),selected_mass _ nodup _ (fun i h => by have := NB _ h; omega)]
    exact label_count T q
  have tagged : P.newCount R.vertices = K T q := by
    change mass R.vertices.vertices (fun x => mark (n ≤ R.label x)) = _
    rw [label_sum R (fun i => mark (n ≤ i)),lengthEq,range_tail]
  have sz := nodup.length_le_of_subset (l₂ := List.range n) (fun _ h => List.mem_range.mpr (bounded _ h))
  rw [label_count,List.length_range] at sz
  have budget : mass R.vertices.vertices target = 3*P.newCount R.vertices + mass R.vertices.vertices bit := by
    rw [cost,tagged,selected]
    have e := valid.2.1
    change T.degrees.sum + 12 = 6 * n at e
    change T.degrees.sum = 3*(2*n-4-q.group.length) + 3*q.group.length
    omega
  have none (v : R.V) (hv : P.fresh v) : target v = 0 ∧ bit v = 0 := by
    have ge : n ≤ R.label v := hv
    have out : R.label v ∉ L := fun h => Nat.not_lt_of_ge ge (NB _ h)
    simp [target,bit,List.getElem?_eq_none hv,out]
  have recover := inverse_layer P R.vertices target bit (fun x => Bool.toNat_le _)
    none (fun x h => deg ⟨x,h⟩) budget
  let base : Model T.degrees := {
    V := P.Old
    map := P.map
    vertices := P.enumeration R.vertices
    label := fun x => R.label x.val
    inj := fun x y h => Subtype.ext (R.inj x.val y.val h)
    hits := fun i => by
      constructor
      · intro hi
        obtain ⟨x,lab⟩ := (R.hits _).mp (by change i < (layer T q).degrees.length; rw [lengthEq]; omega)
        have old : ¬ P.fresh x := by rw [F,lab]; omega
        exact ⟨⟨x,old⟩,lab⟩
      · rintro ⟨x,lab⟩
        exact lab ▸ Nat.lt_of_not_ge x.property
    value := fun x => (degree_of_peeled_map P R.vertices x).trans (recover x).1
  }
  have selected_iff (x : P.Old) :
      R.label x.val ∈ L ↔ ∃ b c : P.Old, R.map.face x.val b.val c.val := by
    have h := (recover x).2.2.1
    simpa [bit,List.contains_iff_mem] using h
  have more (i : Nat) (hi : i < n) : i < (layer T q).degrees.length := by rw [lengthEq]; omega
  have old {i} {x : R.V} (lab : R.label x = i) (hi : i < n) : ¬ P.fresh x := by rw [F,lab]; omega
  have five : ∀ a b c d : R.V, ∃ z, z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ z ≠ d := by
    intro a b c d
    have h (j : Nat) (hj : j < 5) : ∃ x, R.label x = j := (R.hits j).mp (more j (by omega))
    by_cases h₀ : R.label a ≠ 0 ∧ R.label b ≠ 0 ∧ R.label c ≠ 0 ∧ R.label d ≠ 0
    · obtain ⟨x,hx⟩ := h 0 (by decide); exact ⟨x,by grind⟩
    by_cases h₁ : R.label a ≠ 1 ∧ R.label b ≠ 1 ∧ R.label c ≠ 1 ∧ R.label d ≠ 1
    · obtain ⟨x,hx⟩ := h 1 (by decide); exact ⟨x,by grind⟩
    by_cases h₂ : R.label a ≠ 2 ∧ R.label b ≠ 2 ∧ R.label c ≠ 2 ∧ R.label d ≠ 2
    · obtain ⟨x,hx⟩ := h 2 (by decide); exact ⟨x,by grind⟩
    by_cases h₃ : R.label a ≠ 3 ∧ R.label b ≠ 3 ∧ R.label c ≠ 3 ∧ R.label d ≠ 3
    · obtain ⟨x,hx⟩ := h 3 (by decide); exact ⟨x,by grind⟩
    obtain ⟨x,hx⟩ := h 4 (by decide)
    exact ⟨x,by grind⟩
  have indep (x y : R.V) (hx : P.fresh x) (hy : P.fresh y) : ¬ R.map.adj x y :=
    cubic_independent R.map five (P.cubic _ hx) (P.cubic _ hy)
  refine ⟨⟨base,bounded,?_,?_,?_,?_,?_⟩⟩
  · intro i j hi hj
    constructor
    · rintro ⟨a,b,ha,hb,edge⟩
      exact ⟨a.val,b.val,ha,hb,(peeled_edges P).mp edge⟩
    · rintro ⟨a,b,ha,hb,edge⟩
      exact ⟨⟨a,old ha hi⟩,⟨b,old hb hj⟩,ha,hb,(peeled_edges P).mpr edge⟩
  · intro i hi
    obtain ⟨x,hx⟩ := (R.hits i).mp (more _ (NB _ hi))
    let a : P.Old := ⟨x,old hx (NB _ hi)⟩
    obtain ⟨b,c,f⟩ := (selected_iff a).mp (hx ▸ hi)
    exact ⟨R.label b.val,(selected_iff b).mpr ⟨c,a,R.map.rot f⟩,
      R.label c.val,(selected_iff c).mpr ⟨a,b,R.map.rot (R.map.rot f)⟩,
      a.val,b.val,c.val,hx,rfl,rfl,f⟩
  · rintro i j k hi hj hk ⟨x,y,z,hx,hy,hz,f⟩
    exact hx ▸ (selected_iff ⟨x,old hx hi⟩).mpr ⟨⟨y,old hy hj⟩,⟨z,old hz hk⟩,f⟩
  · rintro i j hi hj ⟨x,y,hx,hy,e⟩
    exact indep x y ((F x).mpr (hx ▸ hi)) ((F y).mpr (hy ▸ hj)) e
  · intro i hi boundI
    obtain ⟨x,hx⟩ := (R.hits _).mp boundI
    have fresh : P.fresh x := (F x).mpr (hx ▸ hi)
    obtain ⟨a,b,c,N⟩ := P.cubic x fresh
    have isOld (v : R.V) (e : R.map.adj x v) : ¬ P.fresh v := fun h => indep x v fresh h e
    have ha := isOld a ((N.2.2.2 a).mpr (by simp))
    have hb := isOld b ((N.2.2.2 b).mpr (by simp))
    have hc := isOld c ((N.2.2.2 c).mpr (by simp))
    refine ⟨R.label a,R.label b,R.label c,Nat.lt_of_not_ge ha,Nat.lt_of_not_ge hb,Nat.lt_of_not_ge hc,
      ⟨⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,rfl,rfl,rfl,Or.inr ⟨x,fresh,N⟩⟩,?_⟩
    intro j
    constructor
    · rintro ⟨w,v,hw,hv,e⟩
      obtain rfl : w = x := R.inj _ _ (hw.trans hx.symm)
      have := (N.2.2.2 v).mp e
      grind
    · rintro (rfl | rfl | rfl)
      · exact ⟨x,a,hx,rfl,(N.2.2.2 a).mpr (by simp)⟩
      · exact ⟨x,b,hx,rfl,(N.2.2.2 b).mpr (by simp)⟩
      · exact ⟨x,c,hx,rfl,(N.2.2.2 c).mpr (by simp)⟩


/-- A whole sequence of recovered maps with the same persistent position labels. -/
inductive Trail : (A : Table) → Model A.degrees → List Test → (Z : Table) → Model Z.degrees → Prop
  | nil (A : Table) (R : Model A.degrees) : Trail A R [] A R
  | cons {A q qs Z R S} (step : Step A q R) (rest : Trail (layer A q) R qs Z S) :
      Trail A step.base (q::qs) Z S

theorem reverse_run {A qs Z} (prog : Run A qs Z) (R : Model Z.degrees) :
    ∃ S, Trail A S qs Z R := by
  induction prog with
  | nil => exact ⟨R,.nil _ _⟩
  | cons valid nd bound _ ih =>
    obtain ⟨mid,h⟩ := ih R
    obtain ⟨s⟩ := reverse_step _ _ mid valid nd bound
    exact ⟨s.base,.cons s h⟩

private theorem face_edges {xs : List Nat} (A : Model xs) {i j k} (f : A.triangle i j k) :
    A.edge i j ∧ A.edge i k ∧ A.edge j k := by
  obtain ⟨a,b,c,ha,hb,hc,g⟩ := f
  exact ⟨⟨a,b,ha,hb,c,g⟩, ⟨a,c,ha,hc,b,A.map.flip (A.map.rot (A.map.rot g))⟩,
    ⟨b,c,hb,hc,a,A.map.rot g⟩⟩

theorem test_group (I : Instance) {t : Test} (h : t ∈ schedule I) (a : Mark) (ha : a ∈ t.group) :
    a ∈ marks I := by
  obtain ⟨c,_,ht⟩ := List.mem_flatMap.mp h
  exact (class_props I ((class_sublist ht).subset ha)).1

private def limit (I : Instance) := fullOrder (sourceTable I).length+(prescribed I).length

private theorem original_bound (I : Instance) : (sourceTable I).length ≤ limit I := by
  simp only [limit,fullOrder]
  omega

theorem end_bound (I : Instance) {a : Mark} (ha : a ∈ marks I) (b : Bool) :
    endpoint b a < (sourceTable I).length := by
  have := edges_bounds I a.edge (mark_info I ha).1
  cases b <;> simp [endpoint] <;> omega

/-- The selected triangle of each marker gives a selected endpoint. The other
two available kinds of corner are each an independent set. -/
private theorem passes_step (I : Instance) {A : Table} {t : Test} {R : Model (layer A t).degrees}
    (s : Step A t R) (ht : t ∈ schedule I)
    (markers : ∀ a ∈ marks I, ∀ b ∈ marks I, ¬ s.base.edge a.marker b.marker)
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

private theorem schedule_passes (I : Instance) (fixed : Nat → Nat → Prop)
    {A R qs Z S} (h : Trail A R qs Z S) (sub : qs ⊆ schedule I)
    (room : limit I ≤ A.fresh ∧ A.fresh ≤ A.degrees.length)
    (preserve : ∀ i j, i < limit I → j < limit I → (R.edge i j ↔ fixed i j))
    (markers : ∀ a ∈ marks I, ∀ b ∈ marks I, ¬ fixed a.marker b.marker)
    (aux : ∀ i j, A.fresh ≤ i → A.fresh ≤ j → ¬ R.edge i j) :
    ∀ t ∈ qs, Passes fixed t := by
  induction h with
  | nil => simp
  | @cons A t qs Z R S s _ ih =>
    have ht : t ∈ schedule I := sub (List.mem_cons_self ..)
    have pin {i j} (hi : i < limit I) (hj : j < limit I) : R.edge i j ↔ fixed i j :=
      (s.edges i j (by omega) (by omega)).symm.trans (preserve _ _ hi hj)
    have keep := ih (fun _ h => sub (List.mem_cons_of_mem _ h)) (by
      change limit I ≤ A.degrees.length ∧ A.degrees.length ≤ (layer A t).degrees.length
      rw [layer_order]; omega) (fun _ _ a b => pin a b) s.independent
    intro q hq
    rcases List.mem_cons.mp hq with rfl | h'
    · have localPass := passes_step I s ht (fun a ha b hb e => markers a ha b hb
          ((preserve _ _ (mark_info I ha).2.2 (mark_info I hb).2.2).mp e)) aux
      intro a ha
      obtain ⟨b,hb,e⟩ := localPass a ha
      have endLt := Nat.lt_of_lt_of_le (end_bound I (test_group I ht b hb) q.side) (original_bound I)
      exact ⟨b,hb,(preserve _ _ (mark_info I (test_group I ht a ha)).2.2 endLt).mp e⟩
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

theorem full_length (A : Table) : (layer A full).degrees.length = fullOrder A.degrees.length := by
  simp [layer_order,full,fullOrder]

theorem layer_ge (A : Table) (t : Test) : A.degrees.length ≤ (layer A t).degrees.length := by
  rw [layer_order]; exact Nat.le_add_right ..

private theorem force_from_trail (I : Instance) {Z R S}
    (trail : Trail ⟨sourceTable I,0⟩ S (full :: full :: full :: schedule I) Z R) :
    ∀ e ∈ prescribed I, S.edge e.left e.right := by
  cases trail with
  | @cons _ _ _ _ _ _ s1 tr1 =>
    cases tr1 with
    | @cons _ _ _ _ _ _ s2 tr2 =>
      cases tr2 with
      | @cons A _ _ Z M3 R s3 rest =>
        let T0 : Table := ⟨sourceTable I,0⟩
        let n := (sourceTable I).length
        let n1 := fullOrder n
        let n2 := fullOrder n1
        have l1 : (layer T0 full).degrees.length = n1 := full_length T0
        have l2 : (layer (layer T0 full) full).degrees.length = n2 := (full_length _).trans (congrArg fullOrder l1)
        have protect : limit I ≤ n2 := by
          have room := marker_room I
          change n1+(prescribed I).length ≤ n1+(2*n1-4)
          exact Nat.add_le_add_left room _
        have baseSmall : n ≤ n1 := Nat.le_add_right .. 
        have inputSmall := original_bound I
        have markerInd : ∀ a ∈ marks I, ∀ b ∈ marks I, ¬ M3.edge a.marker b.marker := by
          intro a ha b hb adj
          have pa := (mark_info I ha).2
          have pb := (mark_info I hb).2
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
        have pass : ∀ q ∈ schedule I, Passes adj q := by
          intro q hq a ha
          obtain ⟨b,hb,e⟩ := ok q hq a ha
          exact ⟨b,hb,end_bound I (test_group I hq b hb) q.side,e⟩
        have triangle (m : Mark) (hm : m ∈ marks I) :
            ∃ a b c, s2.base.triangle a b c ∧
              ¬ (a < n ∧ b < n ∧ c < n) ∧
              ∀ j, adj m.marker j → j = a ∨ j = b ∨ j = c := by
          have p := (mark_info I hm).2
          have hi : m.marker < n2 := Nat.lt_of_lt_of_le p.2 protect
          obtain ⟨a,b,c,_,_,_,f,neighbors⟩ := s2.star m.marker (l1 ▸ p.1) (l2 ▸ hi)
          refine ⟨a,b,c,f,?_,?_⟩
          · rintro ⟨a₀,b₀,c₀⟩
            have := s1.allOld a b c a₀ b₀ c₀ f
            simp [selectedLabels,full] at this
          · intro j h
            have hj : j < n2 := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h.1 inputSmall) protect
            exact (neighbors j).mp ((s3.edges _ _ (l2 ▸ hi) (l2 ▸ hj)).mpr h.2)
        have two (m : Mark) (hm : m ∈ marks I) (x y z : Nat)
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
          (Nat.ne_of_lt (edges_bounds I e he).1)
        exact (s1.edges _ _ left.1 right.1).mpr edge

/-- Every labelled triangular-map realization of the compiled list induces
one source realization containing every prescribed edge simultaneously. -/
theorem decode_prescribed (I : Instance) (hv : Valid I) (R : Model (encode I)) :
    ∃ S : Model (sourceTable I), ∀ e ∈ prescribed I, S.edge e.left e.right := by
  obtain ⟨S,h⟩ := reverse_run (compilation_run I hv) R
  exact ⟨S,force_from_trail I h⟩

theorem Trail.induced {A S qs Z R} (t : Trail A S qs Z R) (i j : Nat)
    (hi : i < A.degrees.length) (hj : j < A.degrees.length) : S.edge i j ↔ R.edge i j := by
  induction t with
  | nil => exact Iff.rfl
  | cons s _ ih =>
    exact (s.edges _ _ hi hj).trans (ih (Nat.lt_of_lt_of_le hi (layer_ge ..)) (Nat.lt_of_lt_of_le hj (layer_ge ..)))

theorem decode_induced (I : Instance) (hv : Valid I) (R : Model (encode I)) :
    ∃ S : Model (sourceTable I), (∀ e ∈ prescribed I, S.edge e.left e.right) ∧
    ∀ i j, i < (sourceTable I).length → j < (sourceTable I).length → (S.edge i j ↔ R.edge i j) := by
  obtain ⟨S,h⟩ := reverse_run (compilation_run I hv) R
  exact ⟨S,force_from_trail I h,h.induced⟩

#print axioms reverse_step
#print axioms decode_prescribed

end Recognition.Layers
