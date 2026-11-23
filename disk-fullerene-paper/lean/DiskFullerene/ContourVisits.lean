import DiskFullerene.CoreArms

namespace DiskFullerene.Dual
open Separation EndEuler

/-- Each visit supplies a neighbor in a different component of the
punctured core. The indexing set has exactly the multiplicity in the
actual contour word. -/
theorem visit_components {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G) (u : Face M) :
    ∃ f : Fin ((contourWord G hh hc).count u) → Face M,
      (∀ i, u∈diskInterior G ∧ f i∈diskInterior G ∧ f i∈dualRow G u) ∧
      ∀ i j, i≠j → ¬Walk (CoreAvoid G u) (f i) (f j) := by
  classical
  let C := (dualRow G (apex M)).attach
  let piece := contourPiece G hh hc
  let occurs := fun z => (piece z).contains u
  let B := C.filter occurs
  have count (xs : List {x // IsBoundary G x}) : (xs.flatMap piece).count u=(xs.filter occurs).length := by
    induction xs with
    | nil => simp
    | cons z zs ih =>
      have unique := (contourPiece_nodup G hh hc z).count (a:=u)
      change (piece z).count u = _ at unique
      by_cases yes : u∈piece z <;> simp [piece] at yes <;>
        simp [List.flatMap_cons,List.count_append,occurs,piece,yes,unique,ih,Nat.add_comm]
  have len : (contourWord G hh hc).count u=B.length := count C
  have nd : B.Nodup := (attached_nodup (row_nodup G (noRepeatOnSphere G hh) (apex M))).filter _
  let r (i : Fin ((contourWord G hh hc).count u)) := B[i.val]'(by rw [←len];exact i.isLt)
  have hit (i) : u∈piece (r i) := List.contains_iff_mem.mp (List.mem_filter.mp (List.getElem_mem (l:=B) (n:=i.val) (by rw [←len]; exact i.isLt))).2
  let f := fun i => (contourPiece_switch G hh hc (hit i)).2.choose
  have data (i) : f i∈diskInterior G ∧ ((r i).val,f i)∈sides (dualRow G u) :=
    (contourPiece_switch G hh hc (hit i)).2.choose_spec
  have ui (i) := (contourPiece_switch G hh hc (hit i)).1
  refine ⟨f,fun i => ⟨ui i,(data i).1,(endsOfWordSide (data i).2).2⟩,?_⟩
  intro i j ne
  apply switches_separate G hh (ui i) _ (r i).property (r j).property (data i).1 (data j).1 (data i).2 (data j).2
  intro eq
  have e : r i=r j := Subtype.ext eq
  exact ne (Fin.ext (index_eq nd (by rw [←len];exact i.isLt) (by rw [←len];exact j.isLt) e))

theorem cut_of_visits {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G) {u : Face M}
    (twice : 2 ≤ (contourWord G hh hc).count u) :
    ∃ a b, u∈diskInterior G ∧ a∈diskInterior G ∧ b∈diskInterior G ∧ a∈dualRow G u ∧ b∈dualRow G u ∧
      ¬Walk (CoreAvoid G u) a b := by
  obtain ⟨f,inside,separate⟩ := visit_components G hh hc u
  let i : Fin ((contourWord G hh hc).count u) := ⟨0,by omega⟩
  let j : Fin ((contourWord G hh hc).count u) := ⟨1,by omega⟩
  exact ⟨f i,f j,(inside i).1,(inside i).2.1,(inside j).2.1,(inside i).2.2,(inside j).2.2,
    separate i j (by simp [i,j])⟩

theorem CoreAvoid.symm {M} (G : IsDiskFullerene M h) {u x y} (s : CoreAvoid G u x y) : CoreAvoid G u y x :=
  ⟨s.2.1,s.1,InteriorAdj.symm G _ _ s.2.2⟩

theorem arms_meet_only_root {M} {G : IsDiskFullerene M h} {u a b f}
    (apart : ¬Walk (CoreAvoid G u) a b) (left : arm G u a f=true) (right : arm G u b f=true) : f=u := by
  rcases in_arm.mp left with eq|p
  · exact eq
  rcases in_arm.mp right with eq|q
  · exact eq
  exact False.elim (apart (p.trans (q.symm (fun _ _ => CoreAvoid.symm G))))

private theorem count_three {α} (ls : List α) (a b c u : α→Bool)
    (one : ∀ z, a z=true → b z=false ∧ c z=false) (two : ∀ z, b z=true → c z=false)
    (sub : ∀ z, a z=true ∨ b z=true ∨ c z=true → u z=true) :
    ls.countP a+ls.countP b+ls.countP c ≤ ls.countP u := by
  induction ls with
  | nil => simp
  | cons x xs ih =>
    have h1 := one x; have h2 := two x; have h3 := sub x
    cases ea : a x <;> cases eb : b x <;> cases ec : c x <;> cases eu : u x <;>
      simp_all <;> omega

private theorem strip_root {n} (r : Fin n) (A : Fin n→Bool) (ar : A r=true) :
    num A = num (fun z => A z && (z != r)) + 1 := by
  have count (xs : List (Fin n)) :
      xs.countP A = xs.countP (fun z => A z && (z != r)) + xs.count r := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      by_cases eq : x=r
      · subst x; simp [ar, ih,Nat.add_assoc]
      · cases ax : A x <;> simp [eq,ax,ih] <;> omega
  have singleton := (List.nodup_finRange n).count (a:=r)
  simpa using (count (List.finRange n)).trans (by rw [singleton];simp)

theorem visits_le_two {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    (small : M.hexagons≤6) (u : Face M) : (contourWord G hh hc).count u≤2 := by
  by_cases low : (contourWord G hh hc).count u≤2
  · exact low
  obtain ⟨f,inside,separate⟩ := visit_components G hh hc u
  let label (i : Fin 3) : Fin ((contourWord G hh hc).count u) := ⟨i.val,by omega⟩
  let A (i : Fin 3) := arm G u (f (label i))
  let B (i : Fin 3) (x : Face M) := A i x && (x != u)
  have many (i) : 5≤num (B i) := by
    have dat := inside (label i)
    have high := arm_six G hh hc dat.1 dat.2.1 dat.2.2
    have eq := strip_root u (A i) (in_arm.mpr (Or.inl rfl))
    change 6≤num (A i) at high; change num (A i)=num (B i)+1 at eq; omega
  have separateB (i j : Fin 3) (d : i≠j) (x : Face M) (p : B i x=true) : B j x=false := by
    cases q : B j x with
    | false => rfl
    | true =>
      obtain ⟨l,n⟩ := Bool.and_eq_true_iff.mp p
      have r := (Bool.and_eq_true_iff.mp q).1
      have ne : x ≠ u := by simpa using n
      have sep := separate (label i) (label j) (fun eq => d (Fin.ext (show i.val=j.val from congrArg (fun x : Fin ((contourWord G hh hc).count u) => x.val) eq)))
      exact False.elim (ne (arms_meet_only_root sep l r))
  let I := fun z => (diskInterior G).contains z
  have inc (i) (x : Face M) (p : B i x=true) : I x=true := by
    have dat := inside (label i)
    exact List.contains_iff_mem.mpr (arm_stays_inside dat.1 dat.2.1 (Bool.and_eq_true_iff.mp p).1)
  have ub := count_three (List.finRange M.faces.length) (B 0) (B 1) (B 2) I
    (fun x p => ⟨separateB 0 1 (by decide) x p,separateB 0 2 (by decide) x p⟩)
    (separateB 1 2 (by decide)) (fun x hx => hx.elim (inc 0 x) (fun p => p.elim (inc 1 x) (inc 2 x)))
  have size : num I=(diskInterior G).length := by
    rw [num,List.countP_eq_length_filter]
    apply List.Perm.length_eq
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) ((List.nodup_finRange _).filter _)).2
    intro x; simp [I,mem_diskInterior]
  have x := many 0; have y := many 1; have z := many 2
  change num (B 0)+num (B 1)+num (B 2)≤num I at ub
  rw [size,interior_count G hh] at ub
  omega

end DiskFullerene.Dual
