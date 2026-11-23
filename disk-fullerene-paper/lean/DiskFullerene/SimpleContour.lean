import DiskFullerene.InteriorTriangles

namespace DiskFullerene.Dual

/-- List the end vertex of each step of the interior contour, retaining
repeated visits and the cyclic block order from the apex link. -/
noncomputable def contourWord {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (hc : ¬HasChord G) : List (Face M) :=
  (dualRow G (apex M)).attach.flatMap fun x =>
    let A := boundaryArc G hh hc x.val x.property
    (List.range A.steps).map fun j => A.node (j+1)

theorem contour_card {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G) :
    (contourWord G hh hc).length = contourLength G := by
  unfold contourWord contourLength
  rw [List.length_flatMap]
  simp only [List.length_map,List.length_range]
  let C := dualRow G (apex M)
  have mapped : C.attach.map (fun x => (boundaryArc G hh hc x.val x.property).steps) =
      C.map (fun x => (dualRow G x).length-4) := by
    have eq := List.map_congr_left (l := C.attach) (f := (fun x => (boundaryArc G hh hc x.val x.property).steps))
      (g := fun x => (dualRow G x.val).length-4) (by
        intro x _
        have := (boundaryArc G hh hc x.val x.property).length_eq
        omega)
    exact eq.trans (by simp)
  exact congrArg List.sum mapped

theorem contour_inside {M : MapData} {u : Face M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    (m : u ∈ contourWord G hh hc) : u ∈ diskInterior G ∧
      ∃ x, IsBoundary G x ∧ x ∈ dualRow G u := by
  obtain ⟨x,_,step⟩ := List.mem_flatMap.mp m
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp step
  let A := boundaryArc G hh hc x.val x.property
  have lt : k<A.steps := List.mem_range.mp hk
  refine ⟨A.inside _ (by omega),x.val,x.property,(dual_adj_symmetric G _ _).1 ?_⟩
  have t := A.stepSide k lt
  obtain ⟨i,hi,ei⟩ := List.mem_iff_getElem.mp t
  rw [sides_size] at hi; rw [side_at _ i hi] at ei
  exact (Prod.mk.inj ei).2 ▸ List.getElem_mem (next_bound hi)

private theorem distinct_blocks {α β} (xs : List α) (f : α → List β) (nd : (xs.flatMap f).Nodup)
    {x y : α} {z : β} (xm : x∈xs) (ym : y∈xs) (first : z∈f x) (second : z∈f y) : x=y := by
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp xm
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp ym
  have pw := List.pairwise_iff_getElem.mp (List.pairwise_flatMap.mp nd).2
  by_cases lt : i<j
  · exact False.elim (pw i j hi hj lt _ first _ second rfl)
  by_cases gt : j<i
  · exact False.elim (pw j i hj hi gt _ second _ first rfl)
  have eq : i=j := by omega
  simp [eq]

/-- Distinct transitions from the boundary into the interior around the
same core vertex cause distinct visits by the contour. -/
theorem contour_switch_unique {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (hc : ¬HasChord G) (simple : (contourWord G hh hc).Nodup)
    {u x y a b : Face M} (ui : u ∈ diskInterior G) (xi : IsBoundary G x) (yi : IsBoundary G y)
    (ai : a ∈ diskInterior G) (bi : b ∈ diskInterior G)
    (xa : (x,a)∈sides (dualRow G u)) (yb : (y,b)∈sides (dualRow G u)) : x=y := by
  let C := dualRow G (apex M)
  let piece (z : {v // v∈C}) := (List.range (boundaryArc G hh hc z.val z.property).steps).map
    (fun k => (boundaryArc G hh hc z.val z.property).node (k+1))
  have hit {z t : Face M} (zc : IsBoundary G z) (ti : t ∈ diskInterior G)
      (e : (z,t) ∈ sides (dualRow G u)) : u ∈ piece ⟨z,zc⟩ := by
    let A := boundaryArc G hh hc z zc
    obtain ⟨k,lt,_,last⟩ := (contour_side_iff G hh A).2 ⟨(turn_triangle G e).1,ti,ui⟩
    exact List.mem_map.mpr ⟨k,List.mem_range.mpr lt,last⟩
  exact congrArg Subtype.val (distinct_blocks C.attach piece simple (List.mem_attach _ ⟨x,xi⟩)
    (List.mem_attach _ ⟨y,yi⟩) (hit xi ai xa) (hit yi bi yb))

private def Switch (n : Nat) (f : Nat → Bool) (i : Nat) : Prop := f i = true ∧ f (next n i) = false

private def ThreeB (n : Nat) (f : Nat → Bool) (i : Nat) : Prop :=
  f i = true ∧ f (next n i) = true ∧ f (next n (next n i)) = true

private def TwoI (n : Nat) (f : Nat → Bool) (i : Nat) : Prop :=
  f i = true ∧ f (next n i) = false ∧ f (next n (next n i)) = false ∧
    f (next n (next n (next n i))) = true

private def WordLawAt (n : Nat) (f : Nat → Bool) : Prop :=
  (∀ i : Fin n, ¬ThreeB n f i) →
  (∀ i j : Fin n, Switch n f i → Switch n f j → i=j) →
  (∃ i : Fin n, f i = false ∧ f (next n i) = false) ∧
  ∀ i : Fin n, ¬TwoI n f i

private def WordLaw (xs : List Bool) := WordLawAt xs.length (fun i => xs.getD i false)

private instance (xs : List Bool) : Decidable (WordLaw xs) := by
  unfold WordLaw WordLawAt ThreeB Switch TwoI; infer_instance

private theorem finite_laws (xs : List Bool) (sz : xs.length=5 ∨ xs.length=6) : WordLaw xs := by
  have law5 : ∀ a b c d e : Bool, WordLaw [a,b,c,d,e] := by decide +kernel
  have law6 : ∀ a b c d e f : Bool, WordLaw [a,b,c,d,e,f] := by decide +kernel
  rcases xs with _|⟨a,_|⟨b,_|⟨c,_|⟨d,_|⟨e,_|⟨f,rest⟩⟩⟩⟩⟩⟩ <;> simp at sz
  · exact law5 a b c d e
  · subst rest; exact law6 a b c d e f

private theorem linkLaw {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (hc : ¬HasChord G) (simple : (contourWord G hh hc).Nodup)
    {u : Face M} (ui : u ∈ diskInterior G) :
    (∃ b c, (b,c) ∈ sides (dualRow G u) ∧ b ∈ diskInterior G ∧ c ∈ diskInterior G) ∧
    ∀ a b c d : Face M, IsBoundary G a → IsBoundary G d →
      b ∈ diskInterior G → c ∈ diskInterior G → (a,b) ∈ sides (dualRow G u) →
      (b,c) ∈ sides (dualRow G u) → (c,d) ∈ sides (dualRow G u) → False := by
  let R := dualRow G u
  let C := dualRow G (apex M)
  let sign (k : Nat) := (R.map C.contains).getD k false
  have uOther := (mem_diskInterior G _).1 ui
  have deg := inner_degree G uOther.1
  change R.length=5 ∨ R.length=6 at deg
  have law := finite_laws (R.map C.contains) (by simpa only [List.length_map] using deg)
  change WordLawAt (R.map C.contains).length sign at law
  rw [List.length_map] at law
  unfold WordLawAt at law
  have lab (k : Nat) (hk : k < R.length) : sign k = C.contains R[k] := by
    simp [sign, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  have yes {k} (hk : k<R.length) : sign k = true ↔ IsBoundary G R[k] := by
    rw [lab k hk]; exact List.contains_iff_mem
  have no {k} (hk : k<R.length) : sign k = false ↔ R[k] ∈ diskInterior G := by
    rw [lab k hk,mem_diskInterior]
    have ne : R[k] ≠ apex M := fun e => uOther.2 ((dual_adj_symmetric G u _).1 (e ▸ List.getElem_mem hk))
    simp [C,ne]
  have link {k} (hk : k<R.length) :
      (R[k],R[next R.length k]'(next_bound hk))∈sides R := List.mem_iff_getElem.mpr
    ⟨k,by simpa [sides_size] using hk,side_at R k hk⟩
  have nd := row_nodup G (noRepeatOnSphere G hh) u
  have good : ∀ k : Fin R.length, ¬ThreeB R.length sign k := by
    rintro ⟨k,hk⟩ ⟨a,b,c⟩
    have ne : R[k] ≠ R[next R.length (next R.length k)]'(next_bound (next_bound hk)) := by
      intro eq; have z := index_eq nd hk (next_bound (next_bound hk)) eq
      change k=next R.length (next R.length k) at z
      simp only [next] at z; split at z <;> split at z <;> omega
    exact no_three_on_boundary G hh hc ui ((yes hk).1 a) ((yes (next_bound hk)).1 b)
      ((yes (next_bound (next_bound hk))).1 c) ne (link hk) (link (next_bound hk))
  have unique : ∀ i j : Fin R.length, Switch R.length sign i → Switch R.length sign j → i=j := by
    intro i j si sj
    exact Fin.ext (index_eq nd i.isLt j.isLt (contour_switch_unique G hh hc simple ui
      ((yes i.isLt).1 si.1) ((yes j.isLt).1 sj.1) ((no (next_bound i.isLt)).1 si.2)
      ((no (next_bound j.isLt)).1 sj.2) (link i.isLt) (link j.isLt)))
  obtain ⟨⟨k,b,c⟩, forbid⟩ := law good unique
  refine ⟨⟨_,_,link k.isLt,(no k.isLt).1 b,(no (next_bound k.isLt)).1 c⟩,?_⟩
  intro a b c d aC dC bI cI ab bc cd
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp ab
  rw [sides_size] at hi; rw [side_at _ i hi] at eq
  have vals := Prod.mk.inj eq
  have eqC := (same_next_word nd (vals.2 ▸ link (next_bound hi)) bc)
  have eqD := (same_next_word nd (eqC ▸ link (next_bound (next_bound hi))) cd)
  exact forbid ⟨i,hi⟩ ⟨(yes hi).2 (vals.1 ▸ aC),(no (next_bound hi)).2 (vals.2 ▸ bI),
    (no (next_bound (next_bound hi))).2 (eqC ▸ cI),
    (yes (next_bound (next_bound (next_bound hi)))).2 (eqD ▸ dC)⟩

private theorem pure_of_sector {M : MapData} (G : IsDiskFullerene M h) {u b c : Face M}
    (ui : u ∈ diskInterior G) (bi : b ∈ diskInterior G) (ci : c ∈ diskInterior G)
    (s : (b,c) ∈ sides (dualRow G u)) : ∃ v : Fin M.ord, Pure G v.val := by
  let ds := sides M.faces[u.val]
  obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp s
  rw [sides_size] at hk; rw [side_at _ k hk] at eq
  have hp : k < ds.length := by simpa [dualRow,ds] using hk
  let m := next ds.length k
  have hm : m<ds.length := next_bound hp
  have pair : (ds[k],ds[m]) ∈ sides ds := List.mem_iff_getElem.mpr
    ⟨k,by simpa [sides_size] using hp,side_at ds k hp⟩
  have ok := List.all_eq_true.mp G.faceOrbits _ (List.getElem_mem u.isLt)
  have good := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 _ pair
  obtain ⟨p,v,ea⟩ : ∃ p v, ds[k] = (p,v) := ⟨_,_,rfl⟩
  obtain ⟨v',q,eb⟩ : ∃ v' q, ds[m] = (v',q) := ⟨_,_,rfl⟩
  have tt : M.turn (p,v) = (v',q) := by simpa [ea,eb] using good
  have eqv : v=v' := congrArg Prod.fst tt
  subst v'
  have a : incident M u (p,v) := ea ▸ List.getElem_mem hp
  simp only [dualRow,List.length_map,List.getElem_map] at eq
  change (owner G ds[k].swap, owner G ds[m].swap) = _ at eq
  simp [ea,eb] at eq
  rcases eq with ⟨rfl,rfl⟩
  exact ⟨⟨v,(dart_endpoints G (incident_dart G a)).2.1⟩,(pure_iff G a tt).2 ⟨ui,bi,ci⟩⟩

/-- A simple core contour encloses a vertex with no neighbor on the disk
boundary. The proof extracts a leaf from the dual forest of inner
triangles and uses the actual cyclic face incidences at that leaf. -/
theorem simple_contour_buries_vertex {M : MapData} (G : IsDiskFullerene M h)
    (hh : 3≤h) (hc : ¬HasChord G) (simple : (contourWord G hh hc).Nodup) :
    ∃ u ∈ diskInterior G, ∀ b, IsBoundary G b → b ∉ dualRow G u := by
  classical
  apply Classical.byContradiction
  intro none
  have exposed : ∀ u ∈ diskInterior G, ∃ b, IsBoundary G b ∧ b ∈ dualRow G u := by
    intro u ui; apply Classical.byContradiction
    intro no; exact none ⟨u,ui,fun b hb hx => no ⟨b,hb,hx⟩⟩
  have sz := interior_count G hh
  obtain ⟨u,ui⟩ : ∃ u, u ∈ diskInterior G := ⟨_,List.getElem_mem (l := diskInterior G) (n := 0) (by omega)⟩
  obtain ⟨b,c,edge,bi,ci⟩ := (linkLaw G hh hc simple ui).1
  have pure := pure_of_sector G ui bi ci edge
  obtain ⟨u,a,b,c,d,ui,ba,bd,bi,ci,ab,bc,cd⟩ := exposed_two_run G hh exposed pure
  exact (linkLaw G hh hc simple ui).2 _ _ _ _ ba bd bi ci ab bc cd

/-- The whole single-cycle case of the chordless obstruction in Lemma 3,
on actual cubic maps. Thus any counterexample to the general chord lemma
would have a core contour that revisits a vertex. -/
theorem chordless_repeats {M : MapData} (G : IsDiskFullerene M h)
    (hh : 12≤h) (hc : ¬HasChord G) (six : M.hexagons≤6) :
    ¬(contourWord G (by omega) hc).Nodup := by
  intro simple
  have h3 : 3≤h := by omega
  let W := contourWord G h3 hc
  obtain ⟨u,ui,buried⟩ := simple_contour_buries_vertex G h3 hc simple
  have missing : u ∉ W := by
    intro hit
    obtain ⟨_,x,xc,xu⟩ := contour_inside G h3 hc hit
    exact buried x xc xu
  have nd : (u::W).Nodup := List.nodup_cons.mpr ⟨missing,simple⟩
  have sub : u::W ⊆ diskInterior G := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hit
    · exact ui
    · exact (contour_inside G h3 hc hit).1
  have size := nd.length_le_of_subset sub
  have count := interior_count G h3
  have contour := (contour_card G h3 hc).trans (contour_length_eq G h3)
  change W.length = _ at contour
  simp only [List.length_cons] at size
  omega

end DiskFullerene.Dual
