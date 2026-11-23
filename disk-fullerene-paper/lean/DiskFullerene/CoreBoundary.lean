import DiskFullerene.ArmDegree
import DiskFullerene.BoundaryCount

namespace DiskFullerene.Dual
open Separation

private def Good (b : List Bool) : Prop :=
    (∀ i : Fin b.length, ¬(b.getD i.val false ∧ b.getD (next b.length i) false ∧ b.getD (next b.length (next b.length i)) false)) →
    (∀ i j : Fin b.length, b.getD i false → b.getD (next b.length i) false=false → b.getD j false →
      b.getD (next b.length j) false=false → i=j) → (b.filter id).length≤2
private instance (b) : Decidable (Good b) := by unfold Good;infer_instance

private theorem bit_bound (r : List Bool) (degree : r.length=5 ∨ r.length=6)
    (short : ∀ i : Fin r.length, ¬(r.getD i.val false ∧ r.getD (next r.length i) false ∧
      r.getD (next r.length (next r.length i)) false))
    (one : ∀ i j : Fin r.length, r.getD i false → r.getD (next r.length i) false = false →
      r.getD j false → r.getD (next r.length j) false=false → i=j) : (r.filter id).length≤2 := by
  have five : ∀ a b c d e, Good [a,b,c,d,e] := by decide +kernel
  have six : ∀ a b c d e f, Good [a,b,c,d,e,f] := by decide +kernel
  rcases r with _|⟨a,_|⟨b,_|⟨c,_|⟨d,_|⟨e,_|⟨f,tail⟩⟩⟩⟩⟩⟩ <;> simp at degree
  · exact five a b c d e short one
  · subst tail; exact six a b c d e f short one

theorem noncut_boundary_at_most_two {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    {u} (ui : u∈diskInterior G) (notCut : ¬IsCoreCut G u) :
    ((dualRow G u).filter (dualRow G (apex M)).contains).length≤2 := by
  let R := dualRow G u
  let C := dualRow G (apex M)
  let r := R.map C.contains
  have sz : r.length=R.length := by simp [r]
  have deg := inner_degree G ((mem_diskInterior G _).1 ui).1
  change R.length=5 ∨ R.length=6 at deg
  have desc (k : Nat) (hk : k<R.length) : r.getD k false=C.contains R[k] := by
    simp [r,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk]
  have yes {k} (hk : k<R.length) : r.getD k false=true ↔ IsBoundary G R[k] := by rw [desc k hk];exact List.contains_iff_mem
  have no {k} (hk : k<R.length) : r.getD k false=false ↔ R[k]∈diskInterior G := by
    rw [desc k hk,mem_diskInterior]
    have ne : R[k]≠apex M := fun e => ((mem_diskInterior G _).1 ui).2 ((dual_adj_symmetric G u _).1 (e ▸ List.getElem_mem hk))
    simp [C,ne]
  have step {k} (hk : k<R.length) : (R[k],R[next R.length k]'(next_bound hk))∈sides R :=
    List.mem_iff_getElem.mpr ⟨k,by simpa [sides_size] using hk,side_at R k hk⟩
  have nd := row_nodup G (noRepeatOnSphere G hh) u
  have bound := bit_bound r (by rw [sz];exact deg)
  rw [sz] at bound
  have ans := bound (by
    rintro ⟨k,hk⟩ ⟨a,b,c⟩
    have ne : R[k] ≠ R[next R.length (next R.length k)]'(next_bound (next_bound hk)) := by
      intro eq; have z := index_eq nd hk (next_bound (next_bound hk)) eq
      change k=next R.length (next R.length k) at z
      simp only [next] at z; split at z <;> split at z <;> omega
    exact no_three_on_boundary G hh hc ui ((yes hk).1 a) ((yes (next_bound hk)).1 b)
      ((yes (next_bound (next_bound hk))).1 c) ne (step hk) (step (next_bound hk))) (by
    intro i j p q y z
    apply Classical.byContradiction; intro neq
    have distinct : R[i.val]≠R[j.val] := fun e => neq (Fin.ext (index_eq nd i.isLt j.isLt e))
    have ai := (no (next_bound i.isLt)).1 q; have bi := (no (next_bound j.isLt)).1 z
    exact notCut ⟨ui,_,_,ai,bi,List.getElem_mem _,List.getElem_mem _,switches_separate G hh ui distinct
      ((yes i.isLt).1 p) ((yes j.isLt).1 y) ai bi (step i.isLt) (step j.isLt)⟩)
  have filt (L : List (Face M)) : ((L.map C.contains).filter id).length=(L.filter C.contains).length := by
    induction L with
    | nil => simp
    | cons a as ih => by_cases q : C.contains a <;> simp_all
  exact (filt R) ▸ ans

private theorem wheel_cut {M} (G : IsDiskFullerene M h) (hh : 3≤h) {u a b}
    (ui : u∈diskInterior G) (ai : a∈diskInterior G) (bi : b∈diskInterior G)
    (ar : a∈dualRow G u) (br : b∈dualRow G u) (apart : ¬Walk (CoreAvoid G u) a b)
    (W : ArmWheel G (⟨u,a,ui,ai,ar⟩ : Branch G)) :
    ((dualRow G u).filter (dualRow G (apex M)).contains).length≤2 ∧
      ∃ z∈diskInterior G, ∀ f, IsBoundary G f → f∉dualRow G z := by
  let D : Branch G := ⟨u,a,ui,ai,ar⟩
  have nb : b≠u := fun eq => row_no_loop G hh _ (eq ▸ br)
  have noB : arm G u a b≠true := fun e => (in_arm.mp e).elim nb apart
  have center : W.center∈D.members := W.inside
  have active : arm G u a W.center=true := in_arm.mpr (.inr ((D.mem_iff _).1 center))
  have ne : W.center≠u := fun eq => D.out hh (show u∈D.members from eq ▸ center)
  have rootRim := ((W.allFaces u).1 (in_arm.mpr (.inl rfl))).resolve_left ne.symm
  obtain ⟨p,q,pc,cq,pr,qr,pq,_⟩ := W.rim_three hh rootRim
  have safe (k : Face M) (s : arm G u a k=true) : k∈diskInterior G := arm_stays_inside ui ai s
  have acP := W.closed p pr; have acQ := W.closed q qr
  let R := dualRow G u
  let C := dualRow G (apex M)
  have degree := inner_degree G ((mem_diskInterior G u).1 ui).1
  have cRow : W.center∈R := (endsOfWordSide pc).2
  have pRow : p∈R := (endsOfWordSide pc).1
  have qRow : q∈R := (endsOfWordSide cq).2
  have nonRim (k : Face M) (s : k∈diskInterior G) : C.contains k=false := by
    by_cases h : k∈C
    · exact False.elim (((mem_diskInterior G _).1 s).2 h)
    · simpa using h
  have listed : [b,p,W.center,q].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_false_eq_true,and_true,not_or]
    have cp : p≠W.center := fun e => row_no_loop G hh _ (e ▸ pr)
    have cq' : W.center≠q := fun e => row_no_loop G hh _ (e.symm ▸ qr)
    exact ⟨⟨fun e => noB (e ▸ acP),fun e => noB (e ▸ active),fun e => noB (e ▸ acQ)⟩,⟨cp,pq⟩,cq'⟩
  have sub : [b,p,W.center,q] ⊆ R.filter (fun k => !C.contains k) := by
    intro k hk
    rcases List.mem_cons.mp hk with rfl|hk
    · exact List.mem_filter.mpr ⟨br,by rw [nonRim _ bi];rfl⟩
    rcases List.mem_cons.mp hk with rfl|hk
    · exact List.mem_filter.mpr ⟨pRow,by rw [nonRim _ (safe _ acP)];rfl⟩
    rcases List.mem_cons.mp hk with rfl|hk
    · exact List.mem_filter.mpr ⟨cRow,by rw [nonRim _ (safe _ active)];rfl⟩
    have eq := List.mem_singleton.mp hk; subst k
    exact List.mem_filter.mpr ⟨qRow,by rw [nonRim _ (safe _ acQ)];rfl⟩
  have four := listed.length_le_of_subset sub
  change 4≤_ at four
  have split : (R.filter C.contains).length + (R.filter (fun k => !C.contains k)).length=R.length := by
    simpa [List.countP_eq_length_filter] using (List.length_eq_countP_add_countP (l:=R) C.contains).symm
  change R.length=5 ∨ R.length=6 at degree
  exact ⟨by change (R.filter C.contains).length≤2;omega,W.center,safe _ active,
    fun f bf nb => ((mem_diskInterior G f).1 (safe _ (W.closed f nb))).2 bf⟩

theorem cut_boundary_of_table (table : ∀ L, SixTable.test L=true) {M}
    (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G) {u}
    (cut : IsCoreCut G u) (small : (diskInterior G).length≤12) :
    ((dualRow G u).filter (dualRow G (apex M)).contains).length≤2 ∧
      ∃ z∈diskInterior G, ∀ f, IsBoundary G f → f∉dualRow G z := by
  obtain ⟨ui,a,b,ai,bi,av,bv,apart⟩ := cut
  let D : Branch G := ⟨u,a,ui,ai,av⟩
  let E : Branch G := ⟨u,b,ui,bi,bv⟩
  have disj {x} (xd : x∈D.members) : x∉E.members := by
    intro xe
    exact apart (((D.mem_iff _).mp xd).trans (((E.mem_iff _).mp xe).symm (fun _ _ => CoreAvoid.symm G)))
  have nd : (diskInterior G).Nodup := (List.nodup_finRange _).filter _
  have pair := List.nodup_append.mpr (⟨(nd.filter _ : D.members.Nodup), (nd.filter _ : E.members.Nodup),
    fun x hx y hy eq => disj hx (eq ▸ hy)⟩)
  have root : u ∉ D.members++E.members := fun h => (List.mem_append.mp h).elim (D.out hh) (E.out hh)
  have all := List.nodup_cons.mpr ⟨root,pair⟩
  have sub : u::(D.members++E.members)⊆diskInterior G := List.cons_subset.mpr
    ⟨ui,List.append_subset.mpr ⟨fun _ m=>(List.mem_filter.mp m).1, fun _ m=>(List.mem_filter.mp m).1⟩⟩
  have budget := all.length_le_of_subset sub
  simp only [List.length_cons,List.length_append] at budget
  have lowerD := D.five hh hc; have lowerE := E.five hh hc
  by_cases first : D.members.length=5
  · obtain ⟨W⟩ := closed_arm_wheel_of_table table G hh hc D first (by omega)
    exact wheel_cut G hh ui ai bi av bv apart W
  · obtain ⟨W⟩ := closed_arm_wheel_of_table table G hh hc E (by omega) (by omega)
    exact wheel_cut G hh ui bi ai bv av (fun path => apart (path.symm (fun _ _ => CoreAvoid.symm G))) W

/-- Every actual map with at most six hexagons and outer degree at least
twelve has a chord in its outside neighbor cycle. -/
theorem chord_small_of_table (table : ∀ L, SixTable.test L=true) {M} (G : IsDiskFullerene M h)
    (hh : 12≤h) (s : M.hexagons≤6) : HasChord G := by
  apply Classical.byContradiction;intro hc
  have h3 : 3≤h := by omega
  have count := interior_count G h3
  have t : (diskInterior G).length≤12 := by omega
  obtain ⟨u,a,b,ui,ai,bi,au,bu,far⟩ := chordless_cut_vertex G hh hc s
  have cuts : IsCoreCut G u := ⟨ui,a,b,ai,bi,au,bu,far⟩
  obtain ⟨z,zi,buried⟩ := (cut_boundary_of_table table G h3 hc cuts t).2
  have uniform (v) (vi : v∈diskInterior G) :
      ((dualRow G v).filter (dualRow G (apex M)).contains).length≤2 := by
    by_cases cv : IsCoreCut G v
    · exact (cut_boundary_of_table table G h3 hc cv t).1
    · exact noncut_boundary_at_most_two G h3 hc vi cv
  have zero : ((dualRow G z).filter (dualRow G (apex M)).contains).length=0 := by
    apply List.length_eq_zero_iff.mpr
    exact List.filter_eq_nil_iff.mpr (fun f fin => by
      cases bf : (dualRow G (apex M)).contains f with
      | false => simp
      | true => exact False.elim (buried f (List.contains_iff_mem.mp bf) fin))
  have bound := chordless_incidence_defect G h3 hc uniform ⟨z,zi,zero⟩
  omega

end DiskFullerene.Dual
