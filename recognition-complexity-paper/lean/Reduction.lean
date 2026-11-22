import Std

/-! The finite, numerical part of the reduction from unary 3-PARTITION.
Vertices are zero based. The encoder writes every degree separately.
Its fixed nine matching classes specialize the coloring step to the prescribed graph
used by the reduction. An empty test simply stellates every face.
-/
namespace Recognition.Reduction

structure Instance where
  weights : List Nat
  bins : Nat
  capacity : Nat

def Valid (I : Instance) : Prop :=
  0 < I.bins ∧ I.weights.length = 3 * I.bins ∧
  I.weights.sum = I.bins * I.capacity ∧
  ∀ w ∈ I.weights, I.capacity < 4*w ∧ 2*w < I.capacity

def skeletonOrder (I : Instance) := 4*I.bins + 3

/-- Degrees of the cube of the path on 4m+3 vertices, in path order.
The degenerate m=0 branch makes the encoder total. -/
def skeletonBase : Nat → List Nat
  | 0 => [2,2,2]
  | m+1 => [3,4,5] ++ List.replicate (4*m+1) 6 ++ [5,4,3]

/-- In each block of four, use the face with corners r,r+1,r+3 at r = 4i.
It survives the subsequent insertions in the last three consecutive vertices. -/
def bonuses (B : Nat) : Nat → List Nat
  | 0 => [0,0,0]
  | m+1 => [B+1,B+1,0,1] ++ bonuses B m

def sourceTable (I : Instance) : List Nat :=
  (List.zipWith (·+·) (skeletonBase I.bins) (bonuses I.capacity I.bins)) ++
  List.replicate I.weights.sum 4 ++ List.replicate I.bins 3

private theorem base_length (m : Nat) : (skeletonBase m).length = 4*m+3 := by
  cases m <;> simp [skeletonBase] <;> omega

private theorem bonus_length (m B : Nat) : (bonuses B m).length = 4*m+3 := by
  induction m with
  | zero => rfl
  | succ _ ih => simp [bonuses, ih]; omega

theorem source_order (I : Instance) :
    (sourceTable I).length = skeletonOrder I + I.weights.sum + I.bins := by
  simp [sourceTable, base_length, bonus_length, skeletonOrder, Nat.add_assoc]

private theorem base_sum (m : Nat) : (skeletonBase m).sum + 12 = 6*(4*m+3) := by
  cases m <;> simp [skeletonBase] <;> omega

private theorem bonus_sum (m B : Nat) : (bonuses B m).sum = m*(2*B+3) := by
  induction m with
  | zero => simp [bonuses]
  | succ _ ih => simp [bonuses, ih, Nat.succ_mul]; omega

private theorem zip_sum (as bs : List Nat) (h : as.length = bs.length) :
    (List.zipWith (·+·) as bs).sum = as.sum + bs.sum := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all
  | cons a as ih =>
    cases bs with
    | nil => simp at h
    | cons b bs =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp [ih bs h]; omega

theorem source_euler (I : Instance) (hv : Valid I) :
    (sourceTable I).sum + 12 = 6*(sourceTable I).length := by
  obtain ⟨_,_,hs,_⟩ := hv
  have hb := base_sum I.bins
  rw [source_order]
  simp [sourceTable, skeletonOrder, base_length, bonus_length, zip_sum, bonus_sum,
    Nat.mul_add, Nat.mul_left_comm I.bins 2 I.capacity, hs] at *
  omega

theorem source_linear (I : Instance) (hv : Valid I) :
    (sourceTable I).length ≤ 3*(I.weights.length + I.weights.sum + 1) := by
  obtain ⟨_, hc, _, _⟩ := hv
  rw [source_order]
  unfold skeletonOrder
  omega

structure Edge where
  left : Nat
  right : Nat
  color : Nat
  deriving DecidableEq, Repr

def itemEdges (offset : Nat) : List Nat → List Edge
  | [] => []
  | w :: ws =>
      (List.range (w-1)).map (fun j => ⟨offset+j, offset+j+1, 6+(offset+j)%2⟩) ++
      itemEdges (offset+w) ws

def prescribed (I : Instance) : List Edge :=
  let q := skeletonOrder I
  let cube := [1,2,3].flatMap fun d =>
    (List.range (q-d)).map fun v => ⟨v,v+d,2*(d-1)+(v/d)%2⟩
  let caps := (List.range I.bins).map fun i => ⟨4*i,q+I.weights.sum+i,8⟩
  cube ++ itemEdges q I.weights ++ caps

/-- A matched edge is identified within its color class by its left endpoint.
The other label is the position of the second-generation marker. -/
structure Mark where
  edge : Edge
  marker : Nat

structure Test where
  side : Bool
  group : List Mark

def bothSides (g : List Mark) : List Test := [⟨false,g⟩,⟨true,g⟩]

def bitWidth (s : Nat) := s.log2+1

def classTests (w : Nat) (g : List Mark) : List Test :=
  bothSides g ++ (List.range w).flatMap fun b =>
    bothSides (g.filter (fun a => !(a.edge.left.testBit b))) ++
    bothSides (g.filter (fun a => a.edge.left.testBit b))

private theorem map_const_sum (xs : List α) (k : Nat) :
    (xs.map (fun _ => k)).sum = xs.length*k := by
  induction xs with
  | nil => simp
  | cons _ _ ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem classTests_length (w : Nat) (g : List Mark) :
    (classTests w g).length = 2+4*w := by
  simp [classTests, bothSides, List.length_flatMap, map_const_sum, Nat.mul_comm]; omega

def fullOrder (n : Nat) := n + (2*n-4)

def marks (I : Instance) : List Mark :=
  (prescribed I).zipIdx.map fun (e,j) => Mark.mk e (fullOrder (sourceTable I).length+j)

def colorClass (I : Instance) (c : Nat) := (marks I).filter (·.edge.color == c)

def schedule (I : Instance) : List Test :=
  (List.range 9).flatMap fun c => classTests (bitWidth (sourceTable I).length) (colorClass I c)

theorem schedule_length (I : Instance) :
    (schedule I).length = 9*(2+4*bitWidth (sourceTable I).length) := by
  simp [schedule, List.length_flatMap, classTests_length, map_const_sum]

structure Table where
  degrees : List Nat
  /-- Offset of the latest batch of stars. -/
  fresh : Nat

def endpoint (side : Bool) (a : Mark) : Nat := if side then a.edge.right else a.edge.left

def selectedLabels (T : Table) (q : Test) : List Nat :=
  q.group.map Mark.marker ++ q.group.map (endpoint q.side) ++ List.range' T.fresh q.group.length

def raised (xs labels : List Nat) : List Nat :=
  xs.zipIdx.map fun (d,v) => 2*d - (labels.contains v).toNat

def layer (T : Table) (q : Test) : Table :=
  let n := T.degrees.length
  ⟨raised T.degrees (selectedLabels T q) ++ List.replicate (2*n-4-q.group.length) 3,n⟩

def full : Test := ⟨false,[]⟩

def allTests (I : Instance) := [full,full,full] ++ schedule I

/-- For a valid unary instance, return the explicit ordinary degree list. -/
def encode (I : Instance) : List Nat :=
  ((allTests I).foldl layer ⟨sourceTable I,0⟩).degrees

theorem layer_order (T : Table) (q : Test) :
    (layer T q).degrees.length = T.degrees.length + (2*T.degrees.length-4-q.group.length) := by
  simp [layer, raised]

private theorem growth (ts : List Test) (T : Table) :
    (ts.foldl layer T).degrees.length ≤ T.degrees.length * 3^ts.length := by
  induction ts generalizing T with
  | nil => simp
  | cons q qs ih =>
    have one : (layer T q).degrees.length ≤ T.degrees.length * 3 := by rw [layer_order]; omega
    calc
      _ ≤ (layer T q).degrees.length * 3^qs.length := ih _
      _ ≤ (T.degrees.length * 3) * 3^qs.length := Nat.mul_le_mul_right _ one
      _ = _ := by simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 3]

theorem encoded_order (I : Instance) :
    (encode I).length ≤ (sourceTable I).length *
      3^(3+9*(2+4*bitWidth (sourceTable I).length)) := by
  have h := growth (allTests I) ⟨sourceTable I,0⟩
  have H : (allTests I).length = 3+9*(2+4*bitWidth (sourceTable I).length) := by
    rw [allTests, List.length_append, schedule_length]
    rfl
  rw [H] at h
  exact h

/-- A loose but fixed polynomial bound on the length of the actual list. -/
theorem encoded_polynomial (I : Instance) :
    (encode I).length ≤ 3^57 * (sourceTable I).length^73 := by
  let s := (sourceTable I).length
  have hs : s ≠ 0 := by dsimp [s]; rw [source_order]; unfold skeletonOrder; omega
  have hlog : 2^s.log2 ≤ s := (Nat.le_log2 hs).mp (Nat.le_refl _)
  have he : 3+9*(2+4*bitWidth s) = 57+36*s.log2 := by unfold bitWidth; omega
  have hp : 3^(36*s.log2) ≤ s^72 := calc
    _ ≤ (2^2)^(36*s.log2) := Nat.pow_le_pow_left (by decide) _
    _ = (2^s.log2)^72 := by rw [← Nat.pow_mul, ← Nat.pow_mul]; congr 1; omega
    _ ≤ s^72 := Nat.pow_le_pow_left hlog _
  change (encode I).length ≤ 3^57*s^73
  have h := encoded_order I
  change (encode I).length ≤ s*3^(3+9*(2+4*bitWidth s)) at h
  rw [he, Nat.pow_add] at h
  calc
    _ ≤ s*(3^57 * 3^(36*s.log2)) := h
    _ ≤ s*(3^57 * s^72) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hp)
    _ = _ := by rw [show s^73 = s^72*s from Nat.pow_succ ..]; ac_rfl

/-- On a common recovered graph, the full tests yield a unique neighbor on
each side. Its membership in every tested bit class determines the endpoint. -/
theorem recover_endpoint {s i j : Nat} (hi : i < s) (hj : j < s)
    (tests : ∀ b < bitWidth s, ∃ u, u = j ∧ u.testBit b = i.testBit b) : j = i := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases small : b < bitWidth s
  · obtain ⟨_,rfl,h⟩ := tests b small
    exact h
  · have hlog : s < 2^(bitWidth s) := (Nat.log2_lt (by omega : s ≠ 0)).mp (by simp [bitWidth])
    have big : 2^(bitWidth s) ≤ 2^b := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_trans hj hlog) big),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.lt_trans hi hlog) big)]


/-- A decoration of the input list chooses one bin for each occurrence (so
two equal weights are still distinct items). -/
def binWeights {m : Nat} (d : List (Fin m × Nat)) (r : Fin m) :=
  (d.filter (fun a => a.1 == r)).map Prod.snd

def ThreePartition (I : Instance) : Prop :=
  ∃ d : List (Fin I.bins × Nat), d.map Prod.snd = I.weights ∧
    ∀ r, (binWeights d r).sum = I.capacity ∧ (binWeights d r).length = 3

/-- One entry per vertex of the prescribed path. A missing root is allowed
until saturation is proved. The chosen owner is the root on its skeleton
face, or an arbitrary bin if that face has no root. -/
abbrev PathRecord (m : Nat) := Fin m × List (Option (Fin m))

def observed {m : Nat} (rows : List (PathRecord m)) :=
  (rows.flatMap Prod.snd).filterMap id

def slots (m : Nat) : Nat → List (Fin m)
  | 0 => []
  | B+1 => List.finRange m ++ slots m B

private theorem slots_length (m B : Nat) : (slots m B).length = m*B := by
  induction B with
  | zero => simp [slots]
  | succ _ ih => simp [slots, ih, Nat.mul_succ, Nat.add_comm]

private theorem slots_count {m : Nat} (B : Nat) (r : Fin m) : (slots m B).count r = B := by
  induction B with
  | zero => simp [slots]
  | succ _ ih =>
    rw [slots, List.count_append, ih, (List.nodup_finRange _).count_of_mem (List.mem_finRange _)]
    omega

private theorem saturated {xs : List (Option α)} (h : (xs.filterMap id).length = xs.length) :
    none ∉ xs := by
  induction xs with
  | nil => simp
  | cons x xs _ =>
    cases x with
    | none =>
      have := List.length_filterMap_le (id : Option α → Option α) xs
      simp at h
      omega
    | some x =>
      simp at h
      intro hx
      have hin : none ∈ xs := by simpa using hx
      have H := h none hin
      contradiction

private def decoration {m : Nat} (rows : List (PathRecord m)) : List (Fin m × Nat) :=
  rows.map fun (r,xs) => (r,xs.length)

private theorem bin_sum {m : Nat} (rows : List (PathRecord m)) (r : Fin m)
    (filled : ∀ a ∈ rows, ∀ z ∈ a.2, z = some a.1) :
    (binWeights (decoration rows) r).sum = (observed rows).count r := by
  induction rows with
  | nil => simp [binWeights, decoration, observed]
  | cons a rows ih =>
    have tail := ih (fun b hb => filled b (by simp [hb]))
    have eq := List.eq_replicate_of_mem (filled a (by simp))
    have HH : (a.2.filterMap id).count r = if a.1 = r then a.2.length else 0 := by
      conv => lhs; rw [eq]
      simp [List.count_replicate]
    rw [show observed (a :: rows) = a.2.filterMap id ++ observed rows from by
      simp [observed], List.count_append, HH, ← tail]
    by_cases h : a.1 = r <;> simp [binWeights, decoration, h]

theorem exactly_three {B : Nat} (hB : 0 < B) (ws : List Nat)
    (bounds : ∀ w ∈ ws, B < 4*w ∧ 2*w < B) (total : ws.sum = B) :
    ws.length = 3 := by
  match ws with
  | [] => simp at total; omega
  | [a] => have := bounds a (by simp); simp at total; omega
  | [a,b] =>
    have := bounds a (by simp)
    have := bounds b (by simp)
    simp at total
    omega
  | [_,_,_] => rfl
  | a::b::c::d::rest =>
    have := bounds a (by simp)
    have := bounds b (by simp)
    have := bounds c (by simp)
    have := bounds d (by simp)
    simp at total
    omega

/-- Converse at the interface with the embedded skeleton. The geometric input
is explicit: each item occupies a single face touching at most its owner root;
after the pinned cap at each root is excluded, that root meets B item vertices.
The conclusion supplies an assignment for the original, occurrence-indexed list. -/
theorem decode_partition (I : Instance) (hv : Valid I) (rows : List (PathRecord I.bins))
    (sizes : (rows.map (fun a => a.2.length)) = I.weights)
    (oneFace : ∀ a ∈ rows, ∀ r, some r ∈ a.2 → r = a.1)
    (quotas : ∀ r, (observed rows).count r = I.capacity) : ThreePartition I := by
  obtain ⟨hm, hlen, hsum, bounds⟩ := hv
  have hB : 0 < I.capacity := by
    have hpos : 0 < I.weights.length := by omega
    have := bounds I.weights[0] (List.getElem_mem (by omega))
    omega
  have p : (observed rows).Perm (slots I.bins I.capacity) := by
    apply List.perm_iff_count.mpr
    intro r
    rw [quotas, slots_count]
  have sat : none ∉ rows.flatMap Prod.snd := by
    apply saturated
    have := p.length_eq
    rw [slots_length] at this
    simpa only [observed, ← hsum, ← sizes, List.length_flatMap, Function.comp_def] using this
  have filled : ∀ a ∈ rows, ∀ z ∈ a.2, z = some a.1 := by
    intro a ha z hz
    cases z with
    | none => exact False.elim (sat (List.mem_flatMap.mpr ⟨a,ha,hz⟩))
    | some r => rw [oneFace a ha r hz]
  have dw : (decoration rows).map Prod.snd = I.weights := by
    simpa [decoration, Function.comp_def] using sizes
  refine ⟨decoration rows,dw,fun r => ?_⟩
  have sum := (bin_sum rows r filled).trans (quotas r)
  refine ⟨sum,exactly_three hB _ (fun w hw => bounds w ?_) sum⟩
  rw [← dw]
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
  exact List.mem_map.mpr ⟨a,(List.mem_filter.mp ha).1,rfl⟩


/-- Each successful face test covers each of its markers by a face containing
a selected endpoint. Neighbor relations refer to the same recovered graph. -/
def Passes (adj : Nat → Nat → Prop) (q : Test) :=
  ∀ a ∈ q.group, ∃ v ∈ q.group, adj a.marker (endpoint q.side v)

private theorem side_mem (g : List Mark) (side : Bool) :
    (⟨side,g⟩ : Test) ∈ bothSides g := by cases side <;> simp [bothSides]

private theorem whole_test (g : List Mark) (s : Nat) (side : Bool) :
    (⟨side,g⟩ : Test) ∈ classTests (bitWidth s) g :=
  List.mem_append_left _ (side_mem _ _)

private theorem bit_test (g : List Mark) (s b : Nat) (hb : b < bitWidth s)
    (value side : Bool) :
    let part := g.filter fun a => a.edge.left.testBit b == value
    (⟨side,part⟩ : Test) ∈ classTests (bitWidth s) g := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨b,List.mem_range.mpr hb,?_⟩
  cases value
  · apply List.mem_append_left
    simpa using side_mem (g.filter (fun a => !(a.edge.left.testBit b))) side
  · apply List.mem_append_right
    simpa using side_mem (g.filter (fun a => a.edge.left.testBit b)) side

/-- All tests of one matching force each marker's two intended neighbors.
The at-most-two condition and disjoint endpoints are graph hypotheses;
membership in the scheduled groups and identification of both neighbors are derived. -/
theorem matching_forces (s : Nat) (g : List Mark) (adj : Nat → Nat → Prop)
    (small : ∀ a ∈ g, a.edge.left < s)
    (unique : ∀ (side : Bool) (a : Mark), a ∈ g → ∀ b ∈ g, endpoint side a = endpoint side b → a = b)
    (cross : ∀ (side : Bool) (a : Mark), a ∈ g → ∀ b ∈ g, endpoint side a ≠ endpoint (!side) b)
    (two : ∀ a ∈ g, ∀ x y z, adj a.marker x → adj a.marker y → adj a.marker z →
      x = y ∨ x = z ∨ y = z)
    (ok : ∀ q ∈ classTests (bitWidth s) g, Passes adj q) :
    ∀ a ∈ g, ∀ side, adj a.marker (endpoint side a) := by
  intro a ha side
  obtain ⟨v,hv,av⟩ := ok _ (whole_test g s side) a ha
  obtain ⟨u,hu,au⟩ := ok _ (whole_test g s (!side)) a ha
  have only (z : Mark) (hz : z ∈ g) (az : adj a.marker (endpoint side z)) : z = v := by
    apply unique side z hz v hv
    rcases two a ha _ _ _ az av au with eq|eq|eq
    · exact eq
    · exact False.elim (cross side z hz u hu eq)
    · exact False.elim (cross side v hv u hu eq)
  have ident : v.edge.left = a.edge.left := by
    apply recover_endpoint (small a ha) (small v hv)
    intro b hb
    let part := g.filter fun j => j.edge.left.testBit b == a.edge.left.testBit b
    have ht : (⟨side,part⟩ : Test) ∈ classTests (bitWidth s) g :=
      bit_test g s b hb _ _
    have hap : a ∈ part := by simp [part, ha]
    obtain ⟨z,hz,az⟩ := ok _ ht a hap
    have hp := List.mem_filter.mp hz
    have e := only z hp.1 az
    exact ⟨z.edge.left,congrArg (fun j : Mark => j.edge.left) e,by simpa using hp.2⟩
  have eq : v = a := unique false v hv a ha ident
  simpa [eq] using av



private theorem layer_degree (T : Table) (q : Test) (k : Nat) (hk : 3 ≤ k)
    (old : ∀ d ∈ T.degrees, d ≤ k) : ∀ d ∈ (layer T q).degrees, d ≤ 2*k := by
  intro d hd
  rcases List.mem_append.mp hd with h | h
  · obtain ⟨⟨a,v⟩,ha,rfl⟩ := List.mem_map.mp h
    have ha' : a ∈ T.degrees := by
      have e : a ∈ T.degrees.zipIdx.map Prod.fst := List.mem_map.mpr ⟨(a,v),ha,rfl⟩
      simpa using e
    have := old a ha'
    dsimp only
    omega
  · have := List.eq_of_mem_replicate h
    omega

private theorem degree_growth (ts : List Test) (T : Table) (k : Nat) (hk : 3 ≤ k)
    (old : ∀ d ∈ T.degrees, d ≤ k) :
    ∀ d ∈ (ts.foldl layer T).degrees, d ≤ k * 2^ts.length := by
  induction ts generalizing T k with
  | nil => simpa using old
  | cons t ts ih =>
    intro d hd
    have H := ih (layer T t) (2*k) (by omega) (layer_degree T t k hk old) d hd
    simpa only [List.length_cons, Nat.pow_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
      using H

private theorem le_list_sum {d : Nat} (xs : List Nat) (hd : d ∈ xs) : d ≤ xs.sum := by
  induction xs with
  | nil => simp at hd
  | cons a xs ih =>
    simp only [List.mem_cons] at hd
    rcases hd with rfl | h
    · simp
    · have := ih h; simp; omega

/-- Each explicitly written degree is bounded by a fixed polynomial in the
source order. Binary encoding therefore costs O(log s) bits per degree. -/
theorem encoded_degree_polynomial (I : Instance) (hv : Valid I) :
    ∀ d ∈ encode I, d ≤ (6*2^57) * (sourceTable I).length^37 := by
  let s := (sourceTable I).length
  have hs : 3 ≤ s := by dsimp [s]; rw [source_order]; unfold skeletonOrder; omega
  have hsum := source_euler I hv
  have old (d : Nat) (h : d ∈ sourceTable I) : d ≤ 6*s := by
    have := le_list_sum _ h
    unfold s
    omega
  intro d hd
  have hd' := degree_growth (allTests I) ⟨sourceTable I,0⟩ (6*s) (by omega) old d hd
  have hlen : (allTests I).length = 57+36*s.log2 := by
    simp only [allTests, List.length_append, List.length_cons, List.length_nil, schedule_length]
    change 0+1+1+1 + 9*(2+4*(s.log2+1)) = _
    omega
  rw [hlen, Nat.pow_add] at hd'
  have hlog : 2^s.log2 ≤ s := (Nat.le_log2 (by omega : s ≠ 0)).mp (Nat.le_refl _)
  have hp : 2^(36*s.log2) ≤ s^36 := by
    rw [Nat.mul_comm 36, Nat.pow_mul]
    exact Nat.pow_le_pow_left hlog _
  calc
    _ ≤ 6*s * (2^57 * 2^(36*s.log2)) := hd'
    _ ≤ 6*s * (2^57 * s^36) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hp)
    _ = 6*2^57 * s^37 := by rw [show s^37 = s^36*s from Nat.pow_succ ..]; ac_rfl



private theorem item_info (ws : List Nat) (k : Nat) (e : Edge) (h : e ∈ itemEdges k ws) :
    k ≤ e.left ∧ e.right < k+ws.sum ∧ e.right = e.left+1 ∧ e.color = 6+e.left%2 := by
  induction ws generalizing k with
  | nil => simp [itemEdges] at h
  | cons w ws ih =>
    rcases List.mem_append.mp h with g|g
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp g
      have := List.mem_range.mp hv
      simp
      omega
    · have := ih (k+w) g
      simp; omega

private def distanceEdges (n d : Nat) :=
  (List.range (n-d)).map fun v => Edge.mk v (v+d) (2*(d-1)+(v/d)%2)

private theorem distance_info (d n : Nat) {e : Edge} (h : e ∈ distanceEdges n d) :
    e.left < n-d ∧ e.right = e.left+d ∧ e.color = 2*(d-1)+(e.left/d)%2 := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
  exact ⟨List.mem_range.mp hv,rfl,rfl⟩

private def caps (I : Instance) :=
  (List.range I.bins).map fun i => Edge.mk (4*i) (skeletonOrder I+I.weights.sum+i) 8

private theorem caps_info (I : Instance) {e : Edge} (h : e ∈ caps I) :
    ∃ i < I.bins, e.left = 4*i ∧ e.right = skeletonOrder I + I.weights.sum+i ∧ e.color = 8 := by
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
  exact ⟨v,List.mem_range.mp hv,rfl,rfl,rfl⟩

private theorem prescribed_eq (I : Instance) :
    prescribed I = distanceEdges (skeletonOrder I) 1 ++ distanceEdges (skeletonOrder I) 2 ++
      distanceEdges (skeletonOrder I) 3 ++ itemEdges (skeletonOrder I) I.weights ++ caps I := by
  simp [prescribed,distanceEdges,caps, List.append_assoc]

theorem edges_bounds (I : Instance) (e : Edge) (he : e ∈ prescribed I) :
    e.left < e.right ∧ e.right < (sourceTable I).length ∧ e.color < 9 := by
  rw [prescribed_eq] at he
  simp only [List.mem_append] at he
  rw [source_order]
  rcases he with (((h|h)|h)|h)|h
  · have := distance_info 1 _ h; omega
  · have := distance_info 2 _ h; omega
  · have := distance_info 3 _ h; omega
  · have := item_info _ _ _ h; omega
  · obtain ⟨i,hi,h₁,h₂,h₃⟩ := caps_info I h
    unfold skeletonOrder at *
    omega

theorem prescribed_color (I : Instance) (e : Edge) (he : e ∈ prescribed I) :
    e.color = (if e.right < skeletonOrder I then
      2*(e.right-e.left-1)+(e.left/(e.right-e.left))%2
      else if skeletonOrder I ≤ e.left then 6+e.left%2 else 8) := by
  rw [prescribed_eq] at he
  simp only [List.mem_append] at he
  rcases he with (((h|h)|h)|h)|h
  · have ⟨hl,hr,hc⟩ := distance_info 1 _ h
    simp [hr,hc,show e.left+1 < skeletonOrder I by omega]
  · have ⟨hl,hr,hc⟩ := distance_info 2 _ h
    simp [hr,hc,show e.left+2 < skeletonOrder I by omega]
  · have ⟨hl,hr,hc⟩ := distance_info 3 _ h
    simp [hr,hc,show e.left+3 < skeletonOrder I by omega]
  · have ⟨hl,_,hr,hc⟩ := item_info _ _ _ h
    simp [show ¬e.right < skeletonOrder I by omega,hl,hc]
  · obtain ⟨i,hi,hl,hr,hc⟩ := caps_info I h
    have hx : e.left < skeletonOrder I := by unfold skeletonOrder; omega
    simp [show ¬e.right < skeletonOrder I by omega,Nat.not_le_of_lt hx,hc]

private def ClassShape (I : Instance) (e : Edge) : Prop :=
  if e.color < 6 then
    e.right = e.left + (e.color/2+1) ∧
    (e.left/(e.color/2+1))%2 = e.color%2
  else if e.color < 8 then e.right = e.left+1 ∧ e.left%2 = e.color%2
  else ∃ i < I.bins, e.left = 4*i ∧ e.right = skeletonOrder I+I.weights.sum+i

private theorem edge_shape (I : Instance) (e : Edge) (he : e ∈ prescribed I) :
    ClassShape I e := by
  rw [prescribed_eq] at he
  simp only [List.mem_append] at he
  unfold ClassShape
  rcases he with (((h|h)|h)|h)|h
  · obtain ⟨_,hr,hc⟩ := distance_info 1 _ h
    have hd : e.color/2+1 = 1 := by omega
    simp only [hd]; split <;> omega
  · obtain ⟨_,hr,hc⟩ := distance_info 2 _ h
    have hd : e.color/2+1 = 2 := by omega
    simp only [hd]; split <;> omega
  · obtain ⟨_,hr,hc⟩ := distance_info 3 _ h
    have hd : e.color/2+1 = 3 := by omega
    simp only [hd]; split <;> omega
  · obtain ⟨_,_,hr,hc⟩ := item_info _ _ _ h
    split <;> try omega
    split <;> omega
  · obtain ⟨i,hi,hl,hr,hc⟩ := caps_info I h
    simp [hc]
    exact ⟨i,hi,hl,hr⟩

/-- Equality of left or right endpoints within a class identifies its edge;
left and right endpoint sets are disjoint. -/
theorem prescribed_matching (I : Instance) (a b : Edge)
    (ha : a ∈ prescribed I) (hb : b ∈ prescribed I) (hs : a.color = b.color) :
    ((a.left = b.left ∨ a.right = b.right) → a = b) ∧ a.left ≠ b.right := by
  have A := edge_shape I a ha
  have B := edge_shape I b hb
  unfold ClassShape at A B
  rw [← hs] at B
  have ext (hl : a.left = b.left) (hr : a.right = b.right) : a = b := by
    cases a; cases b; simp_all
  by_cases h : a.color < 6
  · simp [h] at A B
    constructor
    · intro he; apply ext <;> omega
    · have hc : a.color/2+1 = 1 ∨ a.color/2+1 = 2 ∨ a.color/2+1 = 3 := by omega
      rcases hc with hc|hc|hc <;> rw [hc] at A B <;> omega
  · simp [h] at A B
    by_cases h' : a.color < 8
    · simp [h'] at A B
      constructor
      · intro he; apply ext <;> omega
      · omega
    · simp [h'] at A B
      obtain ⟨i,hi,al,ar⟩ := A
      obtain ⟨j,hj,bl,br⟩ := B
      constructor
      · intro he; apply ext <;> omega
      · unfold skeletonOrder at br; omega


private theorem nodup_range_map {α : Type} (n : Nat) (f : Nat → α)
    (inj : ∀ i j, f i = f j → i = j) : ((List.range n).map f).Nodup := by
  apply List.pairwise_map.mpr
  apply List.pairwise_lt_range.imp
  intro i j h eq
  exact (Nat.ne_of_lt h) (inj _ _ eq)

private theorem item_nd (ws : List Nat) (k : Nat) : (itemEdges k ws).Nodup := by
  induction ws generalizing k with
  | nil => simp [itemEdges]
  | cons w ws ih =>
    apply List.nodup_append.mpr
    refine ⟨nodup_range_map _ _ (fun i j h => ?_),ih _,?_⟩
    · have := congrArg Edge.left h; simp at this; exact this
    · intro a ha b hb eq
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp ha
      have := List.mem_range.mp hj
      have := (item_info _ _ _ hb).1
      subst b
      simp at *
      omega

theorem prescribed_nd (I : Instance) : (prescribed I).Nodup := by
  have dn (d : Nat) : (distanceEdges (skeletonOrder I) d).Nodup :=
    nodup_range_map _ _ (fun _ _ h => congrArg Edge.left h)
  have cn : (caps I).Nodup := by
    apply nodup_range_map
    intro i j h
    have := congrArg Edge.right h
    simpa using this
  have c₁ {e} (h : e ∈ distanceEdges (skeletonOrder I) 1) : e.color < 2 := by
    have := distance_info 1 _ h; omega
  have c₂ {e} (h : e ∈ distanceEdges (skeletonOrder I) 2) : 2 ≤ e.color ∧ e.color < 4 := by
    have := distance_info 2 _ h; omega
  have c₃ {e} (h : e ∈ distanceEdges (skeletonOrder I) 3) : 4 ≤ e.color ∧ e.color < 6 := by
    have := distance_info 3 _ h; omega
  have c₄ {e} (h : e ∈ itemEdges (skeletonOrder I) I.weights) : 6 ≤ e.color ∧ e.color < 8 := by
    have := item_info _ _ _ h; omega
  have c₅ {e} (h : e ∈ caps I) : e.color = 8 := by
    obtain ⟨_,_,_,_,hc⟩ := caps_info _ h; exact hc
  simp only [prescribed_eq, List.nodup_append, List.mem_append, dn, cn, item_nd, true_and]
  grind only

private theorem item_count (ws : List Nat) (k : Nat) : (itemEdges k ws).length ≤ ws.sum := by
  induction ws generalizing k with
  | nil => simp [itemEdges]
  | cons w ws ih =>
    have := ih (k+w)
    simp [itemEdges]
    omega

theorem marker_room (I : Instance) :
    (prescribed I).length ≤ 2*fullOrder (sourceTable I).length-4 := by
  have h := item_count I.weights (skeletonOrder I)
  simp [prescribed_eq, distanceEdges, caps, fullOrder, source_order, skeletonOrder] at *
  omega

theorem mark_info (I : Instance) {a : Mark} (ha : a ∈ marks I) :
    a.edge ∈ prescribed I ∧ fullOrder (sourceTable I).length ≤ a.marker ∧
    a.marker < fullOrder (sourceTable I).length+(prescribed I).length := by
  obtain ⟨⟨e,j⟩,hj,rfl⟩ := List.mem_map.mp ha
  exact ⟨List.fst_mem_of_mem_zipIdx hj,Nat.le_add_right _ _, by
    have := List.snd_lt_of_mem_zipIdx hj; simp at *; omega⟩

private theorem mark_ident (I : Instance) (a b : Mark) (ha : a ∈ marks I) (hb : b ∈ marks I)
    (he : a.edge = b.edge) : a = b := by
  obtain ⟨⟨e,i⟩,hi,rfl⟩ := List.mem_map.mp ha
  obtain ⟨⟨f,j⟩,hj,rfl⟩ := List.mem_map.mp hb
  have ei := List.mem_zipIdx' hi
  have ej := List.mem_zipIdx' hj
  have hij := (prescribed_nd I).eq_of_getElem_eq ei.1 ej.1 (ei.2.symm.trans (he.trans ej.2))
  dsimp at he hij
  subst_vars
  rfl

theorem class_props (I : Instance) {c : Nat} {a : Mark} (h : a ∈ colorClass I c) :
    a ∈ marks I ∧ a.edge.color = c := by simpa [colorClass] using h

theorem class_matching (I : Instance) (c : Nat) (side : Bool) (a b : Mark)
    (ha : a ∈ colorClass I c) (hb : b ∈ colorClass I c) :
    (endpoint side a = endpoint side b → a = b) ∧ endpoint side a ≠ endpoint (!side) b := by
  obtain ⟨ham,hac⟩ := class_props I ha
  obtain ⟨hbm,hbc⟩ := class_props I hb
  have he := hac.trans hbc.symm
  have hae := (mark_info I ham).1
  have hbe := (mark_info I hbm).1
  have f := prescribed_matching I _ _ hae hbe he
  have g := prescribed_matching I _ _ hbe hae he.symm
  cases side
  · exact ⟨fun h => mark_ident I _ _ ham hbm (f.1 (.inl h)),f.2⟩
  · exact ⟨fun h => mark_ident I _ _ ham hbm (f.1 (.inr h)),Ne.symm g.2⟩

/-- Every prescribed edge is forced if all scheduled tests pass in the same
graph and each marker has at most two original neighbors. -/
theorem schedule_forces (I : Instance) (adj : Nat → Nat → Prop)
    (two : ∀ a ∈ marks I, ∀ x y z, adj a.marker x → adj a.marker y → adj a.marker z →
      x = y ∨ x = z ∨ y = z)
    (ok : ∀ q ∈ schedule I, Passes adj q) :
    ∀ e ∈ prescribed I, ∃ a ∈ marks I, a.edge = e ∧ adj a.marker e.left ∧ adj a.marker e.right := by
  intro e he
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp he
  let a := (marks I)[j]'(by simpa [marks] using hj)
  have ha : a ∈ marks I := List.getElem_mem ..
  have heqa : a.edge = (prescribed I)[j] := by simp [a, marks, List.getElem_zipIdx]
  have hc := (edges_bounds I _ he).2.2
  let c := a.edge.color
  have hcls : a ∈ colorClass I c := by simp [colorClass, ha, c]
  have pass := matching_forces (sourceTable I).length (colorClass I c) adj
    (fun x hx => by
      have := edges_bounds I _ (mark_info I (class_props I hx).1).1
      omega)
    (fun side x hx y hy => (class_matching I c side x y hx hy).1)
    (fun side x hx y hy => (class_matching I c side x y hx hy).2)
    (fun x hx => two x (class_props I hx).1)
    (fun t ht => ok _ (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr (by simpa [c, heqa] using hc),ht⟩))
  exact ⟨a,ha,heqa,heqa ▸ pass a hcls false,heqa ▸ pass a hcls true⟩



/-- The numerical promise imposed on every degree table. -/
def TableValid (xs : List Nat) : Prop :=
  5 ≤ xs.length ∧ xs.sum+12 = 6*xs.length ∧ ∀ d ∈ xs, 3 ≤ d ∧ d < xs.length

private theorem bonus_bound (m B : Nat) : ∀ d ∈ bonuses B m, d ≤ B+1 := by
  induction m with
  | zero => simp [bonuses]
  | succ _ ih => simpa [bonuses] using ih

theorem source_valid (I : Instance) (hv : Valid I) : TableValid (sourceTable I) := by
  have hm := hv.1
  have hsum := hv.2.2.1
  have hb : I.capacity ≤ I.weights.sum := by
    rw [hsum]; simpa using Nat.mul_le_mul_right I.capacity hm
  have hn := source_order I
  unfold skeletonOrder at hn
  refine ⟨by omega, source_euler I hv, ?_⟩
  intro d hd
  rcases List.mem_append.mp hd with old|cap
  · rcases List.mem_append.mp old with core|item
    · obtain ⟨j,hj,h⟩ := List.mem_iff_getElem.mp core
      simp only [List.getElem_zipWith] at h
      have bound (a : Nat) (ha : a ∈ skeletonBase I.bins) : 3 ≤ a ∧ a ≤ 6 := by
        cases eq : I.bins with
        | zero => omega
        | succ m =>
          simp [skeletonBase, eq] at ha
          rcases ha with h|h|h|h|h|h|h <;> omega
      have H := bound _ (List.getElem_mem (l := skeletonBase I.bins) (n := j) (by simpa [base_length, bonus_length] using hj))
      have K := bonus_bound _ _ _ (List.getElem_mem (l := bonuses I.capacity I.bins) (n := j)
        (by simpa [base_length, bonus_length] using hj))
      omega
    · have := List.eq_of_mem_replicate item; omega
  · have := List.eq_of_mem_replicate cap; omega

theorem label_count (T : Table) (q : Test) :
    (selectedLabels T q).length = 3*q.group.length := by simp [selectedLabels]; omega

private theorem raised_sum_aux (xs labels : List Nat) (k : Nat)
    (lo : ∀ d ∈ xs, 1 ≤ d) :
    (xs.zipIdx k |>.map (fun (d,v) => 2*d - (labels.contains v).toNat)).sum +
    ((List.range' k xs.length).filter labels.contains).length = 2*xs.sum := by
  induction xs generalizing k with
  | nil => simp
  | cons a as ih =>
    have ha := lo a (by simp)
    have H := ih (k+1) (fun d hd => lo d (by simp [hd]))
    by_cases h : k ∈ labels <;>
      simp [List.zipIdx_cons, List.range'_succ, h] at * <;> omega

theorem valid_layer (T : Table) (q : Test) (hv : TableValid T.degrees)
    (nd : (selectedLabels T q).Nodup)
    (bounded : ∀ v ∈ selectedLabels T q, v < T.degrees.length) :
    TableValid (layer T q).degrees := by
  let n := T.degrees.length
  let t := q.group.length
  let labels := selectedLabels T q
  have hf : ((List.range' 0 n).filter labels.contains).Perm labels := by
    apply (List.perm_ext_iff_of_nodup (List.Pairwise.filter _ (List.nodup_range' 1)) nd).mpr
    intro i
    simp only [List.mem_filter, List.contains_iff_mem]
    exact ⟨And.right, fun h => ⟨List.mem_range'.mpr ⟨i,bounded i h,by simp⟩,h⟩⟩
  have hs : 3*t ≤ n := by
    have H := List.length_filter_le labels.contains (List.range' 0 n)
    rw [hf.length_eq, List.length_range'] at H
    simpa [labels,label_count,t] using H
  obtain ⟨hn,he,deg⟩ := hv
  have H := raised_sum_aux T.degrees labels 0 (fun d h => Nat.le_trans (by decide) (deg d h).1)
  change (raised T.degrees labels).sum + _ = _ at H
  change 5 ≤ n at hn
  change T.degrees.sum+12 = 6*n at he
  change (raised T.degrees labels).sum +
    ((List.range' 0 n).filter labels.contains).length = _ at H
  rw [hf.length_eq] at H
  change (raised T.degrees labels).sum + (selectedLabels T q).length = _ at H
  rw [label_count] at H
  have ord := layer_order T q
  change (layer T q).degrees.length = n + (2*n-4-t) at ord
  refine ⟨by omega, ?_, ?_⟩
  · change (raised T.degrees labels ++ List.replicate (2*n-4-t) 3).sum + 12 = _
    simp only [List.sum_append,List.sum_replicate_nat,Nat.mul_comm 3] at *
    unfold t at *
    omega
  · intro d hd
    rcases List.mem_append.mp hd with old|new
    · obtain ⟨⟨x,v⟩,hx,rfl⟩ := List.mem_map.mp old
      have hh := deg x (List.fst_mem_of_mem_zipIdx hx)
      change 3 ≤ x ∧ x < n at hh
      change 3 ≤ 2*x-(labels.contains v).toNat ∧ _
      change _ ∧ 2*x-(labels.contains v).toNat < _
      cases labels.contains v <;> simp <;> omega
    · have := List.eq_of_mem_replicate new
      omega

theorem class_sublist {s : Nat} {g : List Mark} {q : Test} (h : q ∈ classTests s g) :
    q.group.Sublist g := by
  rcases List.mem_append.mp h with h|h
  · simp only [bothSides,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl <;> exact .refl _
  · obtain ⟨b,_,hb⟩ := List.mem_flatMap.mp h
    simp only [bothSides,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hb
    rcases hb with (rfl|rfl)|(rfl|rfl) <;> exact List.filter_sublist

private theorem markers_distinct (I : Instance) : ((marks I).map Mark.marker).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj eq
  simpa [marks,List.getElem_zipIdx] using eq

private structure Ready (I : Instance) (T : Table) : Prop where
  valid : TableValid T.degrees
  generation : fullOrder (sourceTable I).length+(prescribed I).length ≤ T.fresh
  room : T.fresh+(sourceTable I).length ≤ T.degrees.length

private theorem test_labels (I : Instance) (T : Table) (q : Test) (hr : Ready I T)
    (hq : q ∈ schedule I) :
    (selectedLabels T q).Nodup ∧ (∀ v ∈ selectedLabels T q, v < T.degrees.length) ∧
      q.group.length ≤ (sourceTable I).length := by
  obtain ⟨c,_,hc⟩ := List.mem_flatMap.mp hq
  have subc : q.group.Sublist (colorClass I c) := class_sublist hc
  have subm : q.group.Sublist (marks I) := subc.trans List.filter_sublist
  have ndm : (q.group.map Mark.marker).Nodup :=
    List.Pairwise.sublist (subm.map _) (markers_distinct I)
  have nde : (q.group.map (endpoint q.side)).Nodup := by
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem (p := List.pairwise_map.mp ndm)
    intro a b ha hb ne eq
    have H := (class_matching I c q.side a b (subc.subset ha) (subc.subset hb)).1 eq
    apply ne
    rw [H]
  let s := (sourceTable I).length
  have boundEnd {v : Nat} (h : v ∈ q.group.map (endpoint q.side)) : v < s := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    have ⟨hl,hr,_⟩ := edges_bounds I a.edge (mark_info I (subm.subset ha)).1
    unfold endpoint
    split
    · exact hr
    · exact Nat.lt_trans hl hr
  have boundMark {v : Nat} (h : v ∈ q.group.map Mark.marker) :
      fullOrder s ≤ v ∧ v < T.fresh := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    have H := (mark_info I (subm.subset ha)).2
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
private theorem ready_step (I : Instance) (T : Table) (q : Test) (hr : Ready I T)
    (hq : q ∈ schedule I) : Ready I (layer T q) := by
  obtain ⟨nd,hb,hs⟩ := test_labels I T q hr hq
  refine ⟨valid_layer T q hr.valid nd hb, ?_, ?_⟩
  · exact Nat.le_trans hr.generation (Nat.le_trans (Nat.le_add_right ..) hr.room)
  · change T.degrees.length+_ ≤ _
    rw [layer_order]
    have hsf : (sourceTable I).length ≤ fullOrder (sourceTable I).length := Nat.le_add_right ..
    have hg := hr.generation
    have hm := hr.room
    have hn := hr.valid.1
    omega

private theorem valid_full (T : Table) (hv : TableValid T.degrees) : TableValid (layer T full).degrees :=
  valid_layer T full hv (by simp [selectedLabels,full]) (by simp [selectedLabels,full])

private def prepared (I : Instance) :=
  layer (layer (layer ⟨sourceTable I,0⟩ full) full) full

private theorem ready_prepared (I : Instance) (hv : Valid I) : Ready I (prepared I) := by
  have hs := source_valid I hv
  refine ⟨valid_full _ (valid_full _ (valid_full _ hs)), ?_, ?_⟩
  · have := marker_room I
    change _ ≤ (layer (layer ⟨sourceTable I,0⟩ full) full).degrees.length
    simp only [layer_order, full,List.length_nil, Nat.sub_zero]
    unfold fullOrder at *
    omega
  · change (layer (layer ⟨sourceTable I,0⟩ full) full).degrees.length + _ ≤ _
    simp only [prepared, layer_order, full,List.length_nil, Nat.sub_zero]
    have := hs.1; omega

private theorem ready_fold (I : Instance) (qs : List Test) (T : Table) (hr : Ready I T)
    (sub : qs ⊆ schedule I) : Ready I (qs.foldl layer T) := by
  induction qs generalizing T with
  | nil => exact hr
  | cons q qs ih => exact ih _ (ready_step I T q hr (sub (by simp))) (fun _ h => sub (by simp [h]))

theorem encoded_valid (I : Instance) (hv : Valid I) : TableValid (encode I) := by
  have h := ready_fold I (schedule I) (prepared I) (ready_prepared I hv) (fun _ h => h)
  simpa only [encode,allTests,List.foldl_append,List.foldl_cons,List.foldl_nil,prepared] using h.valid


instance (I : Instance) : Decidable (Valid I) := by
  unfold Valid
  infer_instance

def malformedOutput : List Nat := [5,5,5,3,3,3]

/-- Total encoding on arbitrary parsed weight lists, bin counts, and capacities. -/
def reduceInstance (I : Instance) : List Nat := if Valid I then encode I else malformedOutput

@[simp] theorem reduce_valid (I : Instance) (hv : Valid I) : reduceInstance I = encode I := by
  simp [reduceInstance,hv]

@[simp] theorem reduce_invalid (I : Instance) (hv : ¬ Valid I) :
    reduceInstance I = [5,5,5,3,3,3] := by simp [reduceInstance,hv,malformedOutput]

theorem reduce_promise (I : Instance) : TableValid (reduceInstance I) := by
  by_cases hv : Valid I
  · rw [reduce_valid I hv]; exact encoded_valid I hv
  · rw [reduce_invalid I hv]; unfold TableValid; decide

theorem fold_invariant (I : Instance) (hv : Valid I) (P : Table → Prop)
    (init : P ⟨sourceTable I,0⟩)
    (step : ∀ T q, TableValid T.degrees → TableValid (layer T q).degrees →
      3*q.group.length ≤ T.degrees.length → P T → P (layer T q)) :
    P ((allTests I).foldl layer ⟨sourceTable I,0⟩) := by
  have ful (T : Table) (v : TableValid T.degrees) (h : P T) : P (layer T full) :=
    step T full v (valid_full T v) (by simp [full]) h
  have prep := ful _ (valid_full _ (valid_full _ (source_valid I hv)))
    (ful _ (valid_full _ (source_valid I hv)) (ful _ (source_valid I hv) init))
  have loop (qs : List Test) (sub : qs ⊆ schedule I) (T : Table) (hr : Ready I T) (h : P T) :
      P (qs.foldl layer T) := by
    induction qs generalizing T with
    | nil => exact h
    | cons q qs ih =>
      have hq := sub (List.mem_cons_self (a:=q) (l:=qs))
      have next := ready_step I T q hr hq
      have ⟨nd,bound,_⟩ := test_labels I T q hr hq
      have hh := nd.length_le_of_subset (l₂ := List.range T.degrees.length)
        (fun _ hm => List.mem_range.mpr (bound _ hm))
      have sz : 3*q.group.length ≤ T.degrees.length := by simpa [label_count] using hh
      exact ih (fun _ hm => sub (List.mem_cons_of_mem _ hm)) _ next
        (step _ _ hr.valid next.valid sz h)
  simpa only [allTests,List.foldl_append,List.foldl_cons,List.foldl_nil,prepared] using
    loop (schedule I) (fun _ h => h) (prepared I) (ready_prepared I hv) prep

/-- Numerical preconditions for every individual peeling in a compiled schedule. -/
inductive Run : Table → List Test → Table → Prop
  | nil (T) : Run T [] T
  | cons {T q qs R} : TableValid T.degrees → (selectedLabels T q).Nodup →
      (∀ v ∈ selectedLabels T q, v < T.degrees.length) →
      Run (layer T q) qs R → Run T (q :: qs) R

theorem compilation_run (I : Instance) (hv : Valid I) :
    Run ⟨sourceTable I,0⟩ (allTests I) ((allTests I).foldl layer ⟨sourceTable I,0⟩) := by
  have loop (qs : List Test) (sub : qs ⊆ schedule I) (T : Table) (r : Ready I T) :
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
  have v := source_valid I hv
  let T : Table := ⟨sourceTable I,0⟩
  let A := layer T full
  let B := layer A full
  have pre := loop (schedule I) (fun _ h => h) (prepared I) (ready_prepared I hv)
  have hB := f (T := B) (valid_full A (valid_full T v)) pre
  have hA := f (T := A) (valid_full T v) hB
  simpa only [T,A,B,prepared,allTests,List.foldl_append,List.foldl_cons,List.foldl_nil,List.cons_append,List.nil_append] using f (T := T) v hA

end Recognition.Reduction
