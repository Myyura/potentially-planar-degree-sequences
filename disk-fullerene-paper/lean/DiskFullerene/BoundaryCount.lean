import DiskFullerene.DualCore

namespace DiskFullerene.Dual

private def tally (xs : List α) (f : α → Nat) := (xs.map f).sum

private theorem constant (xs : List α) (c : Nat) : tally xs (fun _ => c) = c * xs.length := by
  induction xs with
  | nil => simp [tally]
  | cons a xs ih =>
    change c + tally xs _ = c * (xs.length+1)
    rw [ih,Nat.mul_add]; omega

private theorem tallyAdd (xs : List α) (f g : α → Nat) :
    tally xs (fun x => f x + g x) = tally xs f + tally xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [tally] at ih ⊢; omega

private theorem exchange (xs : List α) (ys : List β) (f : α → β → Nat) :
    tally xs (fun x => tally ys (f x)) = tally ys (fun y => tally xs (fun x => f x y)) := by
  induction xs with
  | nil =>
    change 0 = tally ys (fun _ => 0)
    simp [constant]
  | cons x xs ih =>
    change tally ys (f x) + tally xs _ = tally ys (fun y => f x y + tally xs _)
    rw [tallyAdd,ih]

private theorem tallyCong (xs : List α) {f g : α → Nat} (eq : ∀ x ∈ xs, f x = g x) :
    tally xs f = tally xs g := by
  exact congrArg List.sum (List.map_congr_left eq)

private theorem indicators (xs : List α) (p : α → Bool) :
    tally xs (fun x => if p x then 1 else 0) = (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases e : p x <;> simp_all [tally, Nat.add_comm]

private theorem sumIneq (xs : List α) (f g : α → Nat) (c : Nat)
    (per : ∀ x ∈ xs, f x + c ≤ g x) :
    tally xs f + c * xs.length ≤ tally xs g := by
  induction xs with
  | nil => simp [tally]
  | cons x xs ih =>
    have one := per x (by simp)
    have tail := ih (fun a ha => per a (by simp [ha]))
    simp only [tally,List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ] at *
    omega

private theorem common (xs ys : List α) [DecidableEq α] (xnd : xs.Nodup) (ynd : ys.Nodup) :
    (xs.filter ys.contains).length = (ys.filter xs.contains).length := by
  have p := (List.perm_ext_iff_of_nodup (xnd.sublist List.filter_sublist)
    (ynd.sublist List.filter_sublist)).mpr (show ∀ a,
      a ∈ xs.filter ys.contains ↔ a ∈ ys.filter xs.contains from by simp [and_comm])
  exact p.length_eq

private theorem crossSides {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (xs ys : List (Face M)) (nx : xs.Nodup) (ny : ys.Nodup) :
    tally xs (fun x => ((dualRow G x).filter ys.contains).length) =
      tally ys (fun y => ((dualRow G y).filter xs.contains).length) := by
  have convert (l : List (Face M)) (nl : l.Nodup) (x : Face M) :
      ((dualRow G x).filter l.contains).length =
        tally l (fun y => if (dualRow G x).contains y then 1 else 0) := by
    rw [indicators, common _ _ (row_nodup G (noRepeatOnSphere G hh) _) nl]
  rw [tallyCong xs (fun x _ => convert ys ny x),exchange]
  apply tallyCong
  intro y _
  rw [convert xs nx y]
  apply tallyCong
  intro x _
  by_cases H : y ∈ dualRow G x
  · simp [H,(dual_adj_symmetric G x y).mp H]
  · have z : x ∉ dualRow G y := fun a => H ((dual_adj_symmetric G x y).mpr a)
    simp [H,z]

private theorem disjointFilters (xs : List α) (p q : α → Bool) (apart : ∀ x, p x → q x → False) :
    (xs.filter p).length + (xs.filter q).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h := apart x
    cases hp : p x <;> cases hq : q x <;> simp_all <;> omega

private theorem sixFaceCount {M : MapData} (G : IsDiskFullerene M h) (hh : 7≤h) :
    ((List.finRange M.faces.length).filter (fun i => (dualRow G i).length == 6)).length = M.hexagons := by
  let sizes := (List.finRange M.faces.length).map (fun i => (dualRow G i).length)
  have eq : sizes = M.faces.map List.length := by
    apply List.ext_getElem
    · simp [sizes]
    · intro i hi _
      simp [sizes,row_length]
  have eqc := congrArg (List.count 6) eq
  change (List.count 6 ((List.finRange _).map _)) = _ at eqc
  have countMap (xs : List (Face M)) :
      (xs.map (fun i => (dualRow G i).length)).count 6 =
        (xs.filter (fun i => (dualRow G i).length == 6)).length := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      by_cases q : (dualRow G x).length = 6 <;> simp [q,ih]
  rw [countMap] at eqc
  exact eqc.trans (by
    have neq : h ≠ 6 := by omega
    simp [MapData.faces, MapData.hexagons, G.outerSize, neq])

/-- An incidence bound on every chordless dual disk. The parameter d is a
lower bound on degree in the interior induced graph; d=0 is unconditional. -/
theorem chordless_budget {M : MapData} (G : IsDiskFullerene M h) (hh : 7≤h)
    (hc : ¬ HasChord G) (d : Nat)
    (inside : ∀ y ∈ diskInterior G, d ≤ ((dualRow G y).filter (diskInterior G).contains).length) :
    2*h + d*(6+M.hexagons) ≤ 5*(6+M.hexagons) + M.hexagons := by
  let C := dualRow G (apex M)
  let I := diskInterior G
  let cross := fun x : Face M => ((dualRow G x).filter I.contains).length
  let back := fun y : Face M => ((dualRow G y).filter C.contains).length
  let flag := fun y : Face M => (dualRow G y).length == 6
  have h3 : 3≤h := by omega
  obtain ⟨nc,lc,li⟩ := dual_disk_counts G h3 (noRepeatOnSphere G h3)
  have ni : I.Nodup := (List.nodup_finRange _).sublist List.filter_sublist
  have balanced : tally C cross = tally I back := crossSides G h3 C I nc ni
  have lo := sumIneq C (fun _ => 0) cross 2 (by
    intro x hx
    have nx : x ≠ apex M := fun eq => row_no_loop G h3 _ (eq ▸ hx)
    have hd := inner_degree G nx
    have hf := chordless_fan G h3 hc x hx
    change (0 + 2) ≤ ((dualRow G x).filter I.contains).length
    dsimp only [I]
    omega)
  have hi := sumIneq I back (fun y => 5 + if flag y then 1 else 0) d (by
    intro y hy
    have ny := (mem_diskInterior G y).mp hy
    have deg := inner_degree G ny.1
    have remain := inside y hy
    have sum := disjointFilters (dualRow G y) C.contains I.contains (by
      intro x a b
      exact (mem_diskInterior G x).mp (List.contains_iff_mem.mp b) |>.2 (List.contains_iff_mem.mp a))
    change ((dualRow G y).filter C.contains).length + d ≤ _
    change d ≤ ((dualRow G y).filter I.contains).length at remain
    rcases deg with q|q <;> simp [flag,q] at * <;> omega)
  have cap : (I.filter flag).length ≤ M.hexagons := by
    rw [← sixFaceCount G hh]
    exact List.Sublist.length_le (List.Sublist.filter flag List.filter_sublist)
  rw [tallyAdd,constant,indicators] at hi
  have z : tally C (fun _ => 0) = 0 := by simp [constant]
  change C.length = h at lc
  change I.length = 6 + M.hexagons at li
  rw [li] at hi
  omega

theorem chord_of_large_boundary {M : MapData} (G : IsDiskFullerene M h)
    (large : 15+3*M.hexagons < h) : HasChord G := by
  apply Classical.byContradiction
  intro hc
  have := chordless_budget G (by omega) hc 0 (fun _ _ => Nat.zero_le _)
  omega

/-- The min-degree-two lemma strengthens the incidence bound. In
particular, for six or fewer hexagons this settles chord existence on the
entire range h ≥ 22 outside the earlier published enumeration. -/
theorem chordless_boundary_bound {M : MapData} (G : IsDiskFullerene M h) (hh : 7≤h)
    (hc : ¬HasChord G) : h ≤ 9 + 2*M.hexagons := by
  have := chordless_budget G hh hc 2 (fun _ hi => interior_min_two G (by omega) hc hi)
  omega

theorem chord_above_twenty_one {M : MapData} (G : IsDiskFullerene M h) (hh : 22≤h)
    (s : M.hexagons≤6) : HasChord G := by
  apply Classical.byContradiction
  intro hc
  have := chordless_boundary_bound G (by omega) hc
  omega


private theorem sum_deficit (xs : List α) (f : α → Nat) (max : ∀ y∈xs, f y≤2)
    (buried : ∃ y∈xs, f y=0) : tally xs f + 2 ≤ 2*xs.length := by
  induction xs with
  | nil => simp at buried
  | cons x xs ih =>
    have rest (y) (hy : y∈xs) := max y (by simp [hy])
    have upper := sumIneq xs f (fun _ => 2) 0 (by intro y hy; simpa using rest y hy)
    rw [constant] at upper
    obtain ⟨q,hq,off⟩ := buried
    have hx := max x (by simp)
    simp only [tally,List.map_cons,List.sum_cons,List.length_cons] at *
    rcases List.mem_cons.mp hq with rfl|t
    · omega
    · have := ih rest ⟨q,t,off⟩; omega

/-- Every boundary vertex has at least two neighbors inside. If each
interior vertex has at most two boundary neighbors and a buried vertex
has none, the interior must contain at least h+1 vertices. -/
theorem chordless_incidence_defect {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (hc : ¬HasChord G)
    (max : ∀ y∈diskInterior G, ((dualRow G y).filter (dualRow G (apex M)).contains).length ≤ 2)
    (buried : ∃ y∈diskInterior G, ((dualRow G y).filter (dualRow G (apex M)).contains).length = 0) :
    h+1 ≤ (diskInterior G).length := by
  let C := dualRow G (apex M)
  let I := diskInterior G
  let back := fun y : Face M => ((dualRow G y).filter C.contains).length
  let cross := fun x : Face M => ((dualRow G x).filter I.contains).length
  have nc := (boundary_cycle G hh).1
  have ni : I.Nodup := (List.nodup_finRange _).filter _
  have count : tally C cross = tally I back := crossSides G hh C I nc ni
  have lo := sumIneq C (fun _ => 0) cross 2 (by
    intro x hx
    have deg := inner_degree G (show x≠apex M from fun eq => row_no_loop G hh _ (eq ▸ hx))
    have fan := chordless_fan G hh hc x hx
    change 0+2≤((dualRow G x).filter (diskInterior G).contains).length
    omega)
  have hi := sum_deficit I back max buried
  rw [constant] at lo
  have len : C.length=h := (boundary_cycle G hh).2.1
  change h+1≤I.length
  omega

end DiskFullerene.Dual
