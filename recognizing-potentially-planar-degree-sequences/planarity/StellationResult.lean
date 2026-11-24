import EliminationResult
import SparseBoundary.InteriorRepairs

/-! The ordinary one-layer operation, with an arbitrary set of selected labels.
The four-vertex lower bound is on the original triangulation. No admissibility
upper bound on its prescribed degrees is assumed. -/
namespace Recognition.StellationResult
open SparseBoundary Reduction Rigidity Layers Stacking

/-- The selected list describes a set; its order plays no role. -/
def lift (p U : List Nat) (t : Nat) : List Nat :=
  raised p U ++ List.replicate (2*p.length-4-t) 3

structure FaceSelection {p : List Nat} (R : Model p) (U : List Nat) where
  fill : Choice R.V
  covers : ∀ a, R.label a ∈ U ↔ ∃ b c, vacant R.map fill a b c
  disjoint : ∀ a b c d e, vacant R.map fill a b c → vacant R.map fill a d e →
    (b=d ∧ c=e) ∨ (b=e ∧ c=d)

private theorem size_lift (p U : List Nat) (t : Nat) :
    (lift p U t).length = p.length+(2*p.length-4-t) := by simp [lift,raised]

private theorem old_value {p U : List Nat} {t i : Nat} (hi : i < p.length) :
    (lift p U t)[i]?.getD 0 = 2*(p[i]?.getD 0)-(U.contains i).toNat := by
  have h : i<(lift p U t).length := by rw [size_lift]; omega
  rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem h]
  unfold lift at *
  simp only [List.getElem_append_left (by simpa [raised] using hi : i < (raised p U).length)]
  simp [raised,List.getElem_zipIdx]

private theorem new_value {p U : List Nat} {t i : Nat} (h : p.length ≤ i)
    (b : i < (lift p U t).length) : (lift p U t)[i]?.getD 0 = 3 := by
  rw [List.getElem?_eq_getElem b]
  unfold lift at *
  exact (List.getElem_append_right (by simpa [raised] using h)).trans (List.getElem_replicate _)

private theorem raised_sum (p U : List Nat) (k : Nat) (lo : ∀ d ∈ p, 1 ≤ d) :
    (p.zipIdx k |>.map (fun (d,v) => 2*d - (U.contains v).toNat)).sum +
    ((List.range' k p.length).filter U.contains).length = 2*p.sum := by
  induction p generalizing k with
  | nil => simp
  | cons a as ih =>
    have ha := lo a (by simp)
    have I := ih (k+1) (fun d hd => lo d (by simp [hd]))
    by_cases h : k∈U <;> simp [List.zipIdx_cons,List.range'_succ,h] at * <;> omega

private theorem numeric {p U : List Nat} {t : Nat} (size : 4 ≤ p.length)
    (total : p.sum+12=6*p.length) (low : ∀ d ∈ p, 3≤d) (nd : U.Nodup)
    (bounds : ∀ i∈U, i<p.length) (len : U.length=3*t) :
    5 ≤ (lift p U t).length ∧ (lift p U t).sum+12=6*(lift p U t).length ∧
      ∀ d∈lift p U t, 3≤d := by
  have perm : ((List.range' 0 p.length).filter U.contains).Perm U := by
    apply (List.perm_ext_iff_of_nodup (List.Pairwise.filter _ (List.nodup_range' 1)) nd).mpr
    intro i
    simp only [List.mem_filter,List.contains_iff_mem]
    exact ⟨And.right,fun h => ⟨List.mem_range'.mpr ⟨i,bounds i h,by simp⟩,h⟩⟩
  have count := List.length_filter_le U.contains (List.range' 0 p.length)
  rw [perm.length_eq,List.length_range',len] at count
  have cost := raised_sum p U 0 (fun d hd => (by decide : 1≤3).trans (low d hd))
  rw [perm.length_eq,len] at cost
  change (raised p U).sum+3*t=2*p.sum at cost
  rw [size_lift]
  refine ⟨by omega,?_,?_⟩
  · simp only [lift,List.sum_append,List.sum_replicate_nat] at *
    omega
  · intro d hd
    rcases List.mem_append.mp hd with old|new
    · obtain ⟨⟨v,i⟩,hm,rfl⟩ := List.mem_map.mp old
      have := low v (List.fst_mem_of_mem_zipIdx hm)
      have := Bool.toNat_le (U.contains i)
      exact (by omega : 3≤2*v-(U.contains i).toNat)
    · rw [List.eq_of_mem_replicate new]

private theorem valid_of_graphic {d : List Nat} (nums : 5≤d.length ∧ d.sum+12=6*d.length ∧
    ∀ x∈d, 3≤x) (graph : Graphic d) : TableValid d :=
  ⟨nums.1,nums.2.1,fun x hx => ⟨nums.2.2 x hx,graphic_degree_lt graph x hx⟩⟩

private theorem extra_mass (n k : Nat) :
    mass (List.range (n+k)) (fun i => mark (n ≤ i)) = k := by
  unfold mass
  rw [List.range_add,List.map_append,List.map_map,List.sum_append]
  have z := List.map_congr_left (l := List.range n) (f := fun i => mark (n ≤ i)) (g := fun _ => 0)
    (fun i h => by have := List.mem_range.mp h; simp [mark,show ¬n ≤ i by omega])
  rw [z]
  simp [Function.comp_def,mark]

private theorem face_if_same {W : Type} (M : Map W) {a b c x y z : W}
    (h : M.face a b c) (dx : x≠y) (dy : y≠z) (dz : x≠z)
    (cx : corners a b c x) (cy : corners a b c y) (cz : corners a b c z) : M.face x y z := by
  have h₂ := M.rot h
  have h₃ := M.rot h₂
  have h₄ := M.flip h
  have h₅ := M.flip h₂
  have h₆ := M.flip h₃
  simp only [corners] at cx cy cz
  grind

private theorem recover {p U : List Nat} {t : Nat} (size : 4≤p.length)
    (total : p.sum+12=6*p.length) (low : ∀ d∈p, 3≤d) (nd : U.Nodup)
    (bounded : ∀ i∈U, i<p.length) (len : U.length=3*t) (R : Model (lift p U t)) :
    ∃ S : Model p, Nonempty (FaceSelection S U) := by
  classical
  let n := p.length
  let P : Peeling R.map := {
    fresh v := n ≤ R.label v
    cubic v hv := (cubic_iff_degree R.vertices v).mpr ((R.value v).trans (new_value hv (bound R v)))
    fourOld x y z := by
      obtain ⟨i,hi,hx,hy,hz⟩ := choose_old n (R.label x) (R.label y) (R.label z) size
      obtain ⟨w,hw⟩ := (R.hits i).mp (by rw [size_lift]; omega)
      exact ⟨w,by grind⟩ }
  let target := fun x : R.V => p[R.label x]?.getD 0
  let bit := fun x : R.V => (U.contains (R.label x)).toNat
  have deg (a : P.Old) : degree (M := R.map) R.vertices a.val + bit a.val = 2 * target a.val := by
    have ha : R.label a.val < n := Nat.lt_of_not_ge a.property
    have positive := low _ (List.getElem_mem (l := p) ha)
    have val := (R.value a.val).trans (old_value ha)
    simp only [List.getElem?_eq_getElem ha,Option.getD_some] at val
    simp only [target,List.getElem?_eq_getElem ha,Option.getD_some,bit]
    have := Bool.toNat_le (U.contains (R.label a.val))
    omega
  have cost : mass R.vertices.vertices target = p.sum := by
    rw [show mass R.vertices.vertices target = _ from label_sum R (fun i => p[i]?.getD 0),size_lift]
    exact mass_get _ _
  have selected : mass R.vertices.vertices bit = 3*t := by
    change mass R.vertices.vertices (fun x => (U.contains (R.label x)).toNat) = _
    rw [label_sum R (fun i => (U.contains i).toNat),size_lift]
    exact (selected_mass U nd _ (fun i h => (bounded i h).trans_le (Nat.le_add_right ..))).trans len
  have tagged : P.newCount R.vertices = 2*n-4-t := by
    change mass R.vertices.vertices (fun x => mark (n≤R.label x)) = _
    rw [label_sum R (fun i => mark (n ≤ i)),size_lift]
    exact extra_mass _ _
  have sz := nd.length_le_of_subset (l₂ := List.range n) (fun _ h => List.mem_range.mpr (bounded _ h))
  rw [len,List.length_range] at sz
  have budget : mass R.vertices.vertices target = 3*P.newCount R.vertices + mass R.vertices.vertices bit := by
    rw [cost,tagged,selected]
    change p.sum+12=6*n at total
    change 4≤n at size
    omega
  have none (v : R.V) (hv : P.fresh v) : target v = 0 ∧ bit v = 0 := by
    have ge : n ≤ R.label v := hv
    have out : R.label v ∉ U := fun h => Nat.not_lt_of_ge ge (bounded _ h)
    simp [target,bit,List.getElem?_eq_none hv,out]
  have inv := inverse_layer P R.vertices target bit (fun _ => Bool.toNat_le _)
    none (fun a h => deg ⟨a,h⟩) budget
  let base : Model p := {
    V := P.Old
    map := P.map
    vertices := P.enumeration R.vertices
    label := fun x => R.label x.val
    inj := fun x y h => Subtype.ext (R.inj x.val y.val h)
    hits := fun i => by
      constructor
      · intro hi
        obtain ⟨x,lab⟩ := (R.hits i).mp (by rw [size_lift];omega)
        exact ⟨⟨x,by change ¬n≤R.label x;rw [lab];exact Nat.not_le_of_lt hi⟩,lab⟩
      · rintro ⟨x,lab⟩
        exact lab ▸ Nat.lt_of_not_ge x.property
    value := fun x => (degree_of_peeled_map P R.vertices x).trans (inv x).1 }
  let fill : Choice P.Old := fun K => ¬∃ a b c : P.Old,
    R.map.face a.val b.val c.val ∧ K=corners a b c
  have vacant_eq (a b c : P.Old) : vacant P.map fill a b c ↔ R.map.face a.val b.val c.val := by
    constructor
    · rintro ⟨f,v⟩
      obtain ⟨x,y,z,h,k⟩ := Classical.not_not.mp v
      have dx := P.map.distinct f
      have dy := P.map.distinct (P.map.rot f)
      have dz := P.map.distinct (P.map.flip (P.map.rot (P.map.rot f)))
      have incl (w) (hw : corners a b c w) : corners x.val y.val z.val w.val := by
        rw [k] at hw
        rcases hw with rfl|rfl|rfl <;> simp [corners]
      exact face_if_same R.map h (fun e => dx (Subtype.ext e)) (fun e => dy (Subtype.ext e))
        (fun e => dz (Subtype.ext e)) (incl a (Or.inl rfl)) (incl b (Or.inr (Or.inl rfl)))
        (incl c (Or.inr (Or.inr rfl)))
    · intro h
      exact ⟨Or.inl h,fun v => v ⟨a,b,c,h,rfl⟩⟩
  refine ⟨base,⟨⟨fill,?_,?_⟩⟩⟩
  · intro a
    change R.label a.val ∈ U ↔ ∃ b c : P.Old, vacant P.map fill a b c
    simp_rw [vacant_eq]
    simpa [bit,List.contains_iff_mem] using (inv a).2.2.1
  · intro a b c d e f g
    exact (inv a).2.2.2 b c d e ((vacant_eq ..).mp f) ((vacant_eq ..).mp g)

private theorem four_corners {p : List Nat} (R : Model p) (size : 4≤p.length) (x y z : R.V) :
    ∃ w, w≠x ∧ w≠y ∧ w≠z := by
  obtain ⟨i,hi,a,b,c⟩ := choose_old p.length (R.label x) (R.label y) (R.label z) size
  obtain ⟨w,hw⟩ := (R.hits i).mp hi
  exact ⟨w,by grind⟩

private theorem filled_count {p U : List Nat} {t : Nat} (size : 4≤p.length)
    (total : p.sum+12=6*p.length) (nd : U.Nodup) (bounded : ∀ i∈U, i<p.length)
    (len : U.length=3*t) (R : Model p) (O : FaceSelection R U) :
    (starEnumeration R.map O.fill R.vertices).vertices.length+t+4 = 2*p.length := by
  classical
  let marked := fun a : R.V => U.contains (R.label a)
  have hit (a : R.V) : marked a = true ↔ ∃ b c, vacant R.map O.fill a b c := by
    simpa [marked,List.contains_iff_mem] using O.covers a
  have sizeR := (label_perm R).length_eq
  simp only [List.length_map,List.length_range] at sizeR
  have euler : mass R.vertices.vertices (degree (M := R.map) R.vertices) + 12 =
      6*R.vertices.vertices.length := by
    have eq : mass R.vertices.vertices (degree (M := R.map) R.vertices) = p.sum := by
      unfold mass
      rw [List.map_congr_left (fun a _ => R.value a)]
      change mass R.vertices.vertices (fun a => p[R.label a]?.getD 0) = p.sum
      rw [label_sum R (fun i => p[i]?.getD 0)]
      exact mass_get _ 0
    rw [eq,sizeR,total]
  have bits : mass R.vertices.vertices (fun a => if marked a then 1 else 0) = 3*t := by
    have eq (a : R.V) : (if marked a then 1 else 0) = (marked a).toNat := by cases marked a <;> rfl
    unfold mass
    rw [List.map_congr_left (fun a _ => eq a)]
    change mass R.vertices.vertices (fun a => (U.contains (R.label a)).toNat) = _
    rw [label_sum R (fun i => (U.contains i).toNat),selected_mass _ nd _ bounded,len]
  simpa only [sizeR] using forward_length R.map O.fill (four_corners R size) R.vertices
    marked hit O.disjoint t bits euler

private theorem extend {p U : List Nat} {t : Nat} (size : 4≤p.length)
    (total : p.sum+12=6*p.length) (nd : U.Nodup) (bounded : ∀ i∈U, i<p.length)
    (len : U.length=3*t) (R : Model p) (O : FaceSelection R U) :
    Nonempty (Model (lift p U t)) := by
  classical
  let S := starEnumeration R.map O.fill R.vertices
  let n := p.length
  have four := four_corners R size
  let marked := fun a : R.V => U.contains (R.label a)
  have hit (a : R.V) : marked a = true ↔ ∃ b c, vacant R.map O.fill a b c := by
    simpa [marked,List.contains_iff_mem] using O.covers a
  have count := filled_count size total nd bounded len R O
  have freshCount : S.vertices.length=2*n-4-t := by
    change S.vertices.length+t+4=2*n at count
    omega
  have lenTotal : (lift p U t).length = n+S.vertices.length := by rw [size_lift,freshCount]
  have small (s : Star R.map O.fill) : S.vertices.idxOf s < S.vertices.length :=
    List.idxOf_lt_length_of_mem (S.complete s)
  refine ⟨{
    V := Vertex R.map O.fill
    map := stack R.map O.fill
    vertices := enumeration R.map O.fill R.vertices
    label := Sum.elim R.label (fun s => n+S.vertices.idxOf s)
    inj := ?_
    hits := ?_
    value := ?_ }⟩
  · intro x y e
    cases x with
    | inl a =>
      cases y with
      | inl b => exact congrArg Sum.inl (R.inj _ _ e)
      | inr b =>
        change R.label a = n+S.vertices.idxOf b at e
        have h : R.label a < n := bound R a
        omega
    | inr a =>
      cases y with
      | inl b =>
        change n+S.vertices.idxOf a = R.label b at e
        have h : R.label b < n := bound R b
        omega
      | inr b =>
        change n+S.vertices.idxOf a = n+S.vertices.idxOf b at e
        have same := Nat.add_left_cancel e
        have h₁ := List.getElem_idxOf (xs := S.vertices) (x := a) (small a)
        have h₂ := List.getElem_idxOf (xs := S.vertices) (x := b) (small b)
        exact congrArg Sum.inr (by grind)
  · intro i
    constructor
    · intro hi
      by_cases h : i < n
      · obtain ⟨a,ha⟩ := (R.hits i).mp h
        exact ⟨.inl a,ha⟩
      · have b : i-n < S.vertices.length := by omega
        have iz := S.unique.idxOf_getElem (i := i-n) b
        refine ⟨.inr (S.vertices[i-n]),?_⟩
        change n+S.vertices.idxOf S.vertices[i-n] = i
        omega
    · rintro ⟨x,e⟩
      cases x with
      | inl x =>
        have h : R.label x < n := bound R x
        change R.label x = i at e
        omega
      | inr x =>
        change n+S.vertices.idxOf x = i at e
        have := small x
        omega
  · intro x
    cases x with
    | inl a =>
      have h := forward_layer R.map O.fill four R.vertices marked hit O.disjoint a
      have old := R.value a
      have hmark : (if marked a then 1 else 0) = (U.contains (R.label a)).toNat := by
        change (if marked a then 1 else 0) = (marked a).toNat
        cases marked a <;> rfl
      rw [hmark] at h
      change degree (M := stack R.map O.fill) _ _ = (lift p U t)[R.label a]?.getD 0
      rw [old_value (bound R a)]
      omega
    | inr s =>
      rw [new_degree]
      apply Eq.symm
      apply new_value
      · exact Nat.le_add_right ..
      · change n+S.vertices.idxOf s < _
        have := small s
        omega

private noncomputable def allSelected {p : List Nat} (R : Model p) : FaceSelection R [] where
  fill _ := True
  covers _ := by simp [vacant]
  disjoint _ _ _ _ _ h := False.elim (h.2 trivial)

private noncomputable def splitFaces {V : Type} (M : Map V) (fill : Choice V) :
    Star M (fun _ => True) ≃ Star M fill ⊕ Star M (fun f => ¬fill f) := by
  classical
  exact {
    toFun := fun f => if yes : fill f.val then .inl ⟨_,f.property.1,yes⟩
                      else .inr ⟨_,f.property.1,yes⟩
    invFun := fun s => s.elim (fun f => ⟨_,f.property.1,trivial⟩) (fun f => ⟨_,f.property.1,trivial⟩)
    left_inv := fun f => by by_cases h : fill f.val <;> simp [h,Sum.elim] <;> rfl
    right_inv := fun s => by cases s with
                             | inl f => simp [Sum.elim,f.property.2]; rfl
                             | inr f => simp [Sum.elim,f.property.2]; rfl }

private theorem enum_card {V : Type} (E : Enumeration V) :
    Nat.card V = E.vertices.length := by
  classical
  let : Fintype V := Fintype.ofList E.vertices E.complete
  have full : E.vertices.toFinset = Finset.univ := by ext; simp [E.complete]
  rw [Nat.card_eq_fintype_card,←Finset.card_univ,←full,List.toFinset_card_of_nodup E.unique]

/-- The unfilled faces as unordered triples, each counted exactly once. -/
theorem selection_count {p U : List Nat} {t : Nat} (size : 4≤p.length)
    (total : p.sum+12=6*p.length) (nd : U.Nodup) (bounded : ∀ i∈U, i<p.length)
    (len : U.length=3*t) (R : Model p) (O : FaceSelection R U) :
    Nat.card (Star R.map (fun key => ¬O.fill key)) = t := by
  classical
  let filled := starEnumeration R.map O.fill R.vertices
  let emptyFaces := starEnumeration R.map (fun key => ¬O.fill key) R.vertices
  let := Fintype.ofList filled.vertices filled.complete
  let := Fintype.ofList emptyFaces.vertices emptyFaces.complete
  have all := filled_count (t:=0) size total (by simp) (by simp) (by simp) R (allSelected R)
  have a := filled_count size total nd bounded len R O
  have eq := Nat.card_congr (splitFaces R.map O.fill)
  rw [Nat.card_sum,enum_card filled,enum_card (starEnumeration R.map (fun _ => True) R.vertices)] at eq
  change (starEnumeration R.map (fun _ => True) R.vertices).vertices.length+0+4=2*p.length at all
  change filled.vertices.length+t+4=2*p.length at a
  omega

private theorem base_planar {p : List Nat} (total : p.sum+12=6*p.length)
    (low : ∀ x∈p, 3≤x) (R : Model p) : (Transfer.graph R).Planar := by
  by_cases five : 5 ≤ p.length
  · exact EliminationResult.model_planar R
      (valid_of_graphic ⟨five,total,low⟩ ⟨_,Transfer.graph_realizes R⟩)
  · apply Graph.planar_of_five_with_three
    all_goals
      apply (List.length_filter_le ..).trans
      simp
      omega

/-- A planar realization of the raised list exists precisely when a spherical
triangular model of the old list has disjoint unfilled faces covering U.
Each member of U lies on exactly one such face and each face has three
distinct corners, so the given length of U fixes their number. -/
theorem planaric_iff (p U : List Nat) (t : Nat) (size : 4≤p.length)
    (total : p.sum+12=6*p.length) (low : ∀ d∈p, 3≤d) (nd : U.Nodup)
    (bounded : ∀ i∈U, i<p.length) (len : U.length=3*t) :
    Planaric (lift p U t) ↔
      ∃ R : Model p, (Transfer.graph R).Planar ∧ Nonempty (FaceSelection R U) := by
  have nums := numeric size total low nd bounded len
  constructor
  · rintro ⟨G,deg,plan⟩
    have good := valid_of_graphic nums ⟨G,deg⟩
    obtain ⟨R,_⟩ := Wagner.tight_embedding _ G good deg plan
    obtain ⟨S,chosen⟩ := recover size total low nd bounded len R
    exact ⟨S,base_planar total low S,chosen⟩
  · rintro ⟨S,_,⟨chosen⟩⟩
    obtain ⟨R⟩ := extend size total nd bounded len S chosen
    exact ⟨Transfer.graph R,Transfer.graph_realizes R,
      EliminationResult.model_planar R (valid_of_graphic nums ⟨_,Transfer.graph_realizes R⟩)⟩

/-- Explicit cardinal form of the characterization, comparing the actual
planarity language with labelled triangular realizations having exactly t
pairwise disjoint vacant faces with the given union of corners. -/
theorem planaric_iff_exact (p U : List Nat) (t : Nat) (size : 4≤p.length)
    (total : p.sum+12=6*p.length) (low : ∀ d∈p, 3≤d) (nd : U.Nodup)
    (bounded : ∀ i∈U, i<p.length) (len : U.length=3*t) :
    Planaric (lift p U t) ↔ ∃ (R : Model p) (O : FaceSelection R U),
      (Transfer.graph R).Planar ∧ Nat.card (Star R.map (fun key => ¬O.fill key)) = t := by
  rw [planaric_iff p U t size total low nd bounded len]
  constructor
  · rintro ⟨R,flat,⟨O⟩⟩
    exact ⟨R,O,flat,selection_count size total nd bounded len R O⟩
  · rintro ⟨R,O,flat,_⟩
    exact ⟨R,flat,⟨O⟩⟩

end Recognition.StellationResult
