import DiskFullerene.DualIncidence
import DiskFullerene.CheckMap

/-! Recover the unique required cyclic orders from oriented facial words on
a cubic graph. This closes the gap between face-list presentations and the
rotation-system input of the main statement. -/
namespace DiskFullerene.FaceMap

def corners (fs : List (List Nat)) : List (Dart × Dart) :=
  fs.flatMap fun f => sides (sides f)

private theorem fst_sides (xs : List α) : (sides xs).map Prod.fst = xs := by
  cases xs with
  | nil => rfl
  | cons a l => exact List.map_fst_zip (by simp)

private theorem snd_sides (xs : List α) : ((sides xs).map Prod.snd).Perm xs := by
  cases xs with
  | nil => rfl
  | cons a l =>
    rw [sides,List.map_snd_zip (by simp)]
    exact List.perm_append_comm

private theorem corner_first (fs) : ((corners fs).map Prod.fst) = fs.flatMap sides := by
  simp [corners,List.map_flatMap,fst_sides]

private theorem corner_last (fs) : ((corners fs).map Prod.snd).Perm (fs.flatMap sides) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simpa [corners] using (snd_sides (sides f)).append ih

private theorem mid {f : List Nat} {d e : Dart} (c : (d,e) ∈ sides (sides f)) : d.2=e.1 := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp c
  rw [Dual.sides_size] at hi
  rw [Dual.side_at _ _ hi] at eq
  have ihi : i < f.length := by simpa [Dual.sides_size] using hi
  let j := Dual.next (sides f).length i
  have hj : j < f.length := by simpa [j,Dual.sides_size] using Dual.next_bound ihi
  have ld := (Prod.mk.inj eq).1
  have re := (Prod.mk.inj eq).2
  change (sides f)[j]'(by simpa [Dual.sides_size] using hj) = e at re
  rw [Dual.side_at _ _ ihi] at ld
  rw [Dual.side_at _ _ hj] at re
  rw [← ld,← re]
  simp [j,Dual.sides_size]

private theorem keyed {α β} [DecidableEq α] {xs : List (α × β)}
    (nd : (xs.map Prod.fst).Nodup) {x : α} {y z : β} (a : (x,y)∈xs) (b : (x,z)∈xs) : y=z := by
  induction xs with
  | nil => simp at a
  | cons h xs ih =>
    have nd' := List.nodup_cons.mp nd
    rcases List.mem_cons.mp a with e|m <;> rcases List.mem_cons.mp b with e'|m'
    · exact congrArg Prod.snd (e.trans e'.symm)
    · exact False.elim (nd'.1 (e ▸ List.mem_map.mpr ⟨_,m',rfl⟩))
    · exact False.elim (nd'.1 (e' ▸ List.mem_map.mpr ⟨_,m,rfl⟩))
    · exact ih nd'.2 m m'

def turnAt (n : Nat) (r : List Nat) (a : Nat) : Nat := r[(r.idxOf a+1)%r.length]?.getD n

/-- A fixed-point-free injective function on three neighbours is one of the
two 3-cycles. A partial relation suffices if its domain is the whole row. -/
private theorem cubicCycle (r : List Nat) (deg : r.length=3) (nd : r.Nodup) (n : Nat)
    (R : Nat → Nat → Prop) (domain : ∀ a ∈ r, ∃ b ∈ r, R a b)
    (outputs : ∀ a b, R a b → b ∈ r) (noFixed : ∀ a, ¬R a a)
    (func : ∀ a b c, R a b → R a c → b=c)
    (inj : ∀ a b c, R a c → R b c → a=b) :
    ∃ s, s.Perm r ∧ ∀ a b, a∈r → R a b → turnAt n s a=b := by
  obtain ⟨a,b,c,rr⟩ : ∃ a b c, r=[a,b,c] :=
    ⟨_,_,_,List.eq_getElem_of_length_eq_three r deg⟩
  subst r
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at nd
  obtain ⟨⟨ab,ac⟩,bc,_⟩ := nd
  have seq (a b c : Nat) (ab : a≠b) (ac : a≠c) (bc : b≠c)
      (rab : R a b) (rbc : R b c) (rca : R c a) (x y : Nat)
      (hx : x∈[a,b,c]) (hxy : R x y) : turnAt n [a,b,c] x=y := by
    simp at hx
    rcases hx with rfl|rfl|rfl <;> simp [turnAt,List.idxOf_cons,ab,ac,bc] <;> grind
  obtain ⟨aa,aaMem,aR⟩ := domain a (by simp)
  obtain ⟨bb,bbMem,bR⟩ := domain b (by simp)
  obtain ⟨cc,ccMem,cR⟩ := domain c (by simp)
  simp only [List.mem_cons] at aaMem bbMem ccMem
  by_cases abR : R a b
  · have bcr : R b c := by grind
    have car : R c a := by grind
    exact ⟨[a,b,c],.refl _,seq a b c ab ac bc abR bcr car⟩
  · have acr : R a c := by grind
    have cbr : R c b := by grind
    have bar : R b a := by grind
    refine ⟨[a,c,b],.cons a (.swap ..),?_⟩
    intro x y hx hr
    apply seq a c b ac ab (Ne.symm bc) acr cbr bar x y _ hr
    simpa [or_comm,or_left_comm,or_assoc] using hx

/-- An unordered adjacency input and its oriented face words. All fields
refer to degrees, directed edge incidences or single-face simplicity. -/
structure WordsOK (M : MapData) : Prop where
  cubic : ∀ r ∈ M.rows, r.length = 3
  graph : M.rotationOK = true
  partition : (M.faces.flatMap sides).Perm M.darts
  faces : ∀ f ∈ M.faces, f.Nodup ∧ 3 ≤ f.length

theorem graph_dart_nodup {M : MapData} (valid : M.rotationOK = true) : M.darts.Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · rintro ⟨r,u⟩ m
    have nd := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp valid _ m)).1
    apply List.pairwise_map.mpr
    exact (of_decide_eq_true nd).imp (fun h eq => h (congrArg Prod.snd eq))
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt x hx y hy
    simp only [List.getElem_zipIdx,Nat.zero_add,List.mem_map] at hx hy
    obtain ⟨_,_,rfl⟩ := hx; obtain ⟨_,_,rfl⟩ := hy
    exact fun eq => Nat.ne_of_lt lt (congrArg Prod.fst eq)

private theorem rowExists {M} (W : WordsOK M) (v : Fin M.ord) :
    ∃ s, s.Perm (M.rows[v.val]'v.isLt) ∧ ∀ a b,
      ((a,v.val),(v.val,b)) ∈ corners M.faces → turnAt M.ord s a=b := by
  let R := fun a b => ((a,v.val),(v.val,b)) ∈ corners M.faces
  let r := M.rows[v.val]'v.isLt
  have deg := W.cubic r (List.getElem_mem v.isLt)
  have m : (r,v.val) ∈ M.rows.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem v.isLt)
  have checks := Bool.and_eq_true_iff.mp (List.all_eq_true.mp W.graph _ m)
  have nd : r.Nodup := of_decide_eq_true checks.1
  have rel (b) : (v.val,b) ∈ M.darts ↔ b ∈ r := by
    rw [Dual.dart_iff]; unfold MapData.adj; rw [List.getElem?_eq_getElem (show v.val < M.rows.length from v.isLt)]; rfl
  have back (a) (mem : a ∈ r) : (a,v.val) ∈ M.darts := by
    have h := List.all_eq_true.mp checks.2 a mem
    exact Dual.dart_iff.mpr (by simpa [MapData.adj] using (Bool.and_eq_true_iff.mp h).2)
  have good := W.partition.nodup_iff.mpr (graph_dart_nodup W.graph)
  have firstND : ((corners M.faces).map Prod.fst).Nodup := corner_first _ ▸ good
  have lastND : ((corners M.faces).map Prod.snd).Nodup := (corner_last _).nodup_iff.mpr good
  have out {a b} (hr : R a b) : b ∈ r := by
    apply (rel _).mp
    exact W.partition.mem_iff.mp ((corner_last _).mem_iff.mp (List.mem_map.mpr ⟨_,hr,rfl⟩))
  have noFixed (a) (hr : R a a) : False := by
    obtain ⟨f,hf,hc⟩ := List.mem_flatMap.mp hr
    have left : (a,v.val) ∈ sides f := by
      rw [← fst_sides (sides f)]; exact List.mem_map.mpr ⟨_,hc,rfl⟩
    have right : (v.val,a) ∈ sides f := (snd_sides _).mem_iff.mp (List.mem_map.mpr ⟨_,hc,rfl⟩)
    exact Dual.face_has_no_reverse (W.faces f hf).1 (W.faces f hf).2 left right
  have symmetricKey : ∀ a b c, R a c → R b c → a=b := by
    intro a b c ha hb
    let flipped := (corners M.faces).map Prod.swap
    have ns : (flipped.map Prod.fst).Nodup := by simpa [flipped,List.map_map,Function.comp_def] using lastND
    have pick {w} (hw : R w c) : ((v.val,c),(w,v.val)) ∈ flipped := List.mem_map.mpr ⟨_,hw,rfl⟩
    exact congrArg Prod.fst (keyed ns (pick ha) (pick hb))
  have dom (a) (ha : a∈r) : ∃ b∈r, R a b := by
    have member := W.partition.mem_iff.mpr (back a ha)
    rw [← corner_first] at member
    obtain ⟨⟨d,e⟩,me,deq⟩ := List.mem_map.mp member
    change d = (a,v.val) at deq
    subst d
    obtain ⟨f,_,hc⟩ := List.mem_flatMap.mp me
    have starts : v.val=e.1 := mid hc
    obtain ⟨u,b⟩ := e
    change v.val=u at starts; subst u
    exact ⟨b,out me,me⟩
  obtain ⟨s,hs,turn⟩ := cubicCycle r deg nd M.ord R dom (fun _ _ => out) noFixed
    (fun _ _ _ p q => congrArg Prod.snd (keyed firstND p q)) symmetricKey
  refine ⟨s,hs,fun a b req => turn a b ?_ req⟩
  have md : (a,v.val) ∈ M.darts := W.partition.mem_iff.mp (corner_first _ ▸ List.mem_map.mpr ⟨_,req,rfl⟩)
  have symm := Certificates.adj_symmetric W.graph a v.val (Dual.dart_iff.mp md)
  exact (rel _).mp (Dual.dart_iff.mpr symm)


noncomputable def oriented {M : MapData} (W : WordsOK M) : MapData :=
  { M with rows := (List.finRange M.ord).map fun v => (rowExists W v).choose }

@[simp] theorem oriented_ord {M} (W : WordsOK M) : (oriented W).ord = M.ord := by
  simp [oriented,MapData.ord]

private theorem rowExact {M} (W : WordsOK M) (v : Fin M.ord) :
    (oriented W).rows[v.val]?.getD [] = (rowExists W v).choose := by
  simp [oriented,v.isLt]

theorem rowPerm {M} (W : WordsOK M) (u : Nat) :
    ((oriented W).rows[u]?.getD []).Perm (M.rows[u]?.getD []) := by
  by_cases hu : u<M.ord
  · rw [rowExact W (⟨u,hu⟩ : Fin M.ord),List.getElem?_eq_getElem (show u<M.rows.length from hu)]
    exact (rowExists W ⟨u,hu⟩).choose_spec.1
  · have ho : u ≥ (oriented W).rows.length := by change u ≥ (oriented W).ord; rw [oriented_ord]; omega
    rw [List.getElem?_eq_none ho, List.getElem?_eq_none (show M.rows.length ≤ u from Nat.le_of_not_gt hu)]

theorem sameAdj {M} (W : WordsOK M) (u v : Nat) : (oriented W).adj u v ↔ M.adj u v :=
  (rowPerm W u).mem_iff

private theorem graphOK {M} (W : WordsOK M) : (oriented W).rotationOK = true := by
  apply List.all_eq_true.mpr
  rintro ⟨r,u⟩ mem
  have idx := List.mk_mem_zipIdx_iff_getElem?.mp mem
  obtain ⟨bound,eq⟩ := List.getElem?_eq_some_iff.mp idx
  have size : u<M.ord := by change u<(oriented W).ord at bound; simpa using bound
  let old := M.rows[u]'size
  have orig := List.all_eq_true.mp W.graph (old,u) (List.mk_mem_zipIdx_iff_getElem?.mpr
    (List.getElem?_eq_getElem size))
  have pr := rowPerm W u
  rw [idx,List.getElem?_eq_getElem size] at pr
  change r.Perm old at pr
  have ⟨nd,rows⟩ := Bool.and_eq_true_iff.mp orig
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true (pr.nodup_iff.mpr (of_decide_eq_true nd)),List.all_eq_true.mpr ?_⟩
  intro v hv
  have truth := List.all_eq_true.mp rows v (pr.mem_iff.mp hv)
  simp only [Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne,List.contains_iff_mem] at truth ⊢
  exact ⟨⟨by simpa using truth.1.1,truth.1.2⟩,(sameAdj W v u).mpr truth.2⟩

private theorem dartsIndices (M : MapData) : M.darts = (List.range M.ord).flatMap
    (fun u => (M.rows[u]?.getD []).map (u, ·)) := by
  have eq : M.rows.zipIdx = (List.range M.ord).map (fun u => (M.rows[u]?.getD [],u)) := by
    apply List.ext_getElem
    · simp [MapData.ord]
    · intro i hi _
      have pos : i<M.rows.length := by simpa using hi
      simp [List.getElem?_eq_getElem pos]
  unfold MapData.darts; rw [eq,List.flatMap_map]

private theorem darts_perm {M} (W : WordsOK M) : (oriented W).darts.Perm M.darts := by
  rw [dartsIndices,dartsIndices,oriented_ord]
  have merge (xs : List Nat) : (xs.flatMap (fun u => ((oriented W).rows[u]?.getD []).map (u, ·))).Perm
      (xs.flatMap (fun u => (M.rows[u]?.getD []).map (u, ·))) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => exact ((rowPerm W x).map (x, ·)).append ih
  exact merge _

private theorem checkOrbit {M} (W : WordsOK M) : M.faces.all (oriented W).faceOK = true := by
  apply List.all_eq_true.mpr
  intro f hf
  refine Bool.and_eq_true_iff.mpr ⟨decide_eq_true (W.faces f hf).1,List.all_eq_true.mpr ?_⟩
  rintro ⟨⟨a,v⟩,⟨v',b⟩⟩ c
  have same : v=v' := mid c
  subst v'
  have req : ((a,v),(v,b)) ∈ corners M.faces := List.mem_flatMap.mpr ⟨f,hf,c⟩
  have md : (v,b) ∈ M.darts := W.partition.mem_iff.mp
    ((corner_last _).mem_iff.mp (List.mem_map.mpr ⟨_,req,rfl⟩))
  have adj := Dual.dart_iff.mp md
  have bound : v<M.ord := by
    by_cases hb : v<M.rows.length
    · exact hb
    · simp [MapData.adj,List.getElem?_eq_none (Nat.le_of_not_gt hb)] at adj
  have t := (rowExists W (⟨v,bound⟩ : Fin M.ord)).choose_spec.2 a b req
  apply beq_iff_eq.mpr
  refine Prod.ext ?_ ?_
  · rfl
  change turnAt (oriented W).ord ((oriented W).rows[v]?.getD []) a = b
  rw [oriented_ord,rowExact W (⟨v,bound⟩ : Fin M.ord)]
  exact t

private theorem movePath {M} (W : WordsOK M) {u v gone} (p : PathAvoiding M.adj gone u v) :
    PathAvoiding (oriented W).adj gone u v := by
  induction p with
  | here ok => exact .here ok
  | step _ e ok ih => exact ih.step ((sameAdj W _ _).mpr e) ok

/-- A presentation using unordered adjacency rows and oriented face words
is realized on exactly the same vertex labels, with the same face words. -/
theorem realize {M : MapData} (W : WordsOK M) (h : Nat)
    (euler : 2*M.ord+2*M.faces.length=M.darts.length+4) (conn : M.ThreeConnected)
    (outer : M.outer.length=h) (inner : ∀ f∈M.inner, f.length=5 ∨ f.length=6) :
    IsDiskFullerene (oriented W) h := by
  refine ⟨?_,graphOK W,checkOrbit W,W.partition.trans (darts_perm W).symm,?_,?_,outer,inner⟩
  · intro r hr
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hr
    exact (rowExists W v).choose_spec.1.length_eq.trans (W.cubic _ (List.getElem_mem v.isLt))
  · change 2*(oriented W).ord+2*M.faces.length=(oriented W).darts.length+4
    rw [oriented_ord,(darts_perm W).length_eq,euler]
  · exact ⟨by rw [oriented_ord]; exact conn.1, fun gone small u v hu hv au av =>
       movePath W (conn.2 gone small u v (by simpa using hu) (by simpa using hv) au av)⟩

end DiskFullerene.FaceMap
