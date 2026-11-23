import DiskFullerene.ActualEnds

namespace DiskFullerene.Dual
open Dissection Separation

/-- These half-sets consist of primal vertices. Both orientations of
every actual chord are included; the definition does not presume an end. -/
def ChordHalf {M} (G : IsDiskFullerene M h) (p : Fin M.ord → Bool) : Prop :=
  ∃ c ∈ chords G, ∃ i j : Fin M.faces[(apex M).val].length,
    c.l=i.val ∧ c.r=j.val ∧ ∃ S : TriangleSide G (apex M) (atSide G (apex M) i) (atSide G (apex M) j),
    ∃ b : Bool, ∀ v, p v = b ↔ S.part.left v

theorem ChordHalf.complement {M} {G : IsDiskFullerene M h} {p} (c : ChordHalf G p) :
    ChordHalf G (fun v => !p v) := by
  obtain ⟨e,me,i,j,ei,ej,S,b,C⟩ := c
  refine ⟨e,me,i,j,ei,ej,S,!b,fun v => ?_⟩
  simpa using C v

theorem initial_half {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : HasChord G) :
    ∃ p, ChordHalf G p := by
  classical
  obtain ⟨c,hc⟩ := chords_nonempty G hh hc
  obtain ⟨i,j,ei,ej,_,edge⟩ := (mem_chords G _).mp hc
  have adj (k) : atSide G (apex M) k ∈ dualRow G (apex M) := by
    rw [atSide_eq]; exact List.getElem_mem _
  obtain ⟨S⟩ := hasSides G hh (adj i) edge ((dual_adj_symmetric G _ _).mp (adj j))
  exact ⟨fun v => decide (S.part.left v),c,hc,i,j,ei,ej,S,true,fun _ => by simp⟩

private theorem endsDistinct {M} {G : IsDiskFullerene M h} (hh : 3≤h) {w x y}
    (S : TriangleSide G w x y) : S.wx ≠ S.xy ∧ S.wx ≠ S.yw ∧ S.xy ≠ S.yw := by
  have nl (e : Edge M) := left_ne_right G hh e
  have diff {a b : Face M} {e : Edge M} (H : Across (dual G) e a b) : a≠b := by
    have h := nl e
    rcases H with eq|eq <;> rw [eq] at h <;> simp_all [ne_comm]
  have n₁ := diff S.first
  have n₂ := diff S.middle
  have n₃ := diff S.last
  have distinct {e f : Edge M} {a b c : Face M} (H : Across (dual G) e a b)
      (J : Across (dual G) f b c) (na : a≠b) (nb : a≠c) : e≠f := by
    rintro rfl
    rcases H with he|he <;> rcases J with hf|hf <;> rw [he] at hf <;> simp_all
  exact ⟨distinct S.first S.middle n₁ (Ne.symm n₃),
    Ne.symm (distinct S.last S.first n₃ (Ne.symm n₂)),distinct S.middle S.last n₂ (Ne.symm n₁)⟩

private theorem cut_three {M} {G : IsDiskFullerene M h} (hh : 3≤h) {p}
    (H : ChordHalf G p) : ((List.finRange _).filter (CutFamily.crosses p (primal G))).length=3 := by
  obtain ⟨_,_,_,_,_,_,S,b,C⟩ := H
  have ⟨ab,ac,bc⟩ := endsDistinct hh S
  let ls := (List.finRange _).filter (CutFamily.crosses p (primal G))
  have inList (e : Edge M) : e∈ls ↔ ThreeEdges S.wx S.xy S.yw e := by
    rw [S.part.crosses]
    simp only [ls,List.mem_filter,List.mem_finRange,true_and,CutFamily.crosses,bne_iff_ne]
    have l := C (primal G e).1
    have r := C (primal G e).2
    cases hl : p (primal G e).1 <;> cases hr : p (primal G e).2 <;> cases b <;> simp_all
  have perm : ls.Perm [S.wx,S.xy,S.yw] := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) (by simp [ab,ac,bc])).mpr
    intro e; change e∈ls ↔ _
    rw [inList]; simp [ThreeEdges]
  exact perm.length_eq

theorem half_laminar {M} {G : IsDiskFullerene M h} (hh : 3≤h) {p q}
    (P : ChordHalf G p) (Q : ChordHalf G q) : ∃ pattern : Bool × Bool, ∀ v, (p v,q v)≠pattern := by
  have C := cut_three hh P
  obtain ⟨_,_,_,_,_,_,S,_⟩ := P
  exact CutFamily.laminar S.wx (primal G) (primalResilient G) p q C (cut_three hh Q)

private def inside {n : Nat} (p q : Fin n → Bool) : Prop := ∀ v, p v=true → q v=true
private def area {n : Nat} (p : Fin n → Bool) := ((List.finRange n).filter p).length

private theorem strictly_smaller {n} {p q : Fin n → Bool} (sub : inside p q) (strict : ¬inside q p) :
    area p < area q := by
  let xs := List.finRange n
  have eq : (xs.filter q).filter p = xs.filter p := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro x _
    have := sub x
    cases hp : p x <;> cases hq : q x <;> simp_all
  have sl : (xs.filter p).Sublist (xs.filter q) := eq ▸ List.filter_sublist
  have le := sl.length_le
  change (xs.filter p).length < (xs.filter q).length
  apply Classical.byContradiction; intro h
  have same := sl.eq_of_length (by omega)
  apply strict
  intro x qx
  have mem : x∈xs.filter q := List.mem_filter.mpr ⟨List.mem_finRange _,qx⟩
  rw [← same] at mem
  exact (List.mem_filter.mp mem).2

private theorem deepest {M} {G : IsDiskFullerene M h} (p : Fin M.ord → Bool) (P : ChordHalf G p) :
    ∃ q, ChordHalf G q ∧ inside q p ∧ ∀ r, ChordHalf G r → inside r q → inside q r := by
  classical
  generalize size : area p = k
  induction k using Nat.strongRecOn generalizing p with
  | ind k ih =>
    by_cases minimal : ∀ r, ChordHalf G r → inside r p → inside p r
    · exact ⟨p,P,fun _ h => h,minimal⟩
    · have ⟨r,R,sp,pr⟩ : ∃ r, ChordHalf G r ∧ inside r p ∧ ¬inside p r := by
        apply Classical.byContradiction; intro none
        exact minimal (fun r R inc => Classical.byContradiction (fun dec => none ⟨r,R,inc,dec⟩))
      have lt := strictly_smaller sp pr
      obtain ⟨q,Q,sr,m⟩ := ih (area r) (by omega) r R rfl
      exact ⟨q,Q,fun v hv => sp v (sr v hv),m⟩

/-- Every chord cut puts the whole terminal half on one side. -/
def TerminalHalf {M} (G : IsDiskFullerene M h) (p : Fin M.ord → Bool) : Prop :=
  ChordHalf G p ∧ ∀ q, ChordHalf G q → ∃ b : Bool, ∀ v, p v=true → q v=b

private theorem min_terminal {M} {G : IsDiskFullerene M h} (hh : 3≤h) {p} (P : ChordHalf G p)
    (min : ∀ r, ChordHalf G r → inside r p → inside p r) : TerminalHalf G p := by
  refine ⟨P,fun q Q => ?_⟩
  obtain ⟨⟨a,b⟩,absent⟩ := half_laminar hh P Q
  cases a <;> cases b
  · have incl : inside (fun v => !q v) p := by
      intro v hv; have := absent v; cases hq : q v <;> cases hp : p v <;> simp_all
    have rev := min _ Q.complement incl
    exact ⟨false,fun v hp => by have := rev v hp; simpa using this⟩
  · have incl : inside q p := by
      intro v hv; have := absent v; cases hp : p v <;> simp_all
    exact ⟨true,min q Q incl⟩
  · exact ⟨true,fun v hv => by have := absent v; cases hq : q v <;> simp_all⟩
  · exact ⟨false,fun v hv => by have := absent v; cases hq : q v <;> simp_all⟩

/-- Every chosen side of every chord contains a terminal side. -/
theorem ChordHalf.contains_terminal {M} {G : IsDiskFullerene M h} (hh : 3≤h) {p}
    (P : ChordHalf G p) : ∃ q, TerminalHalf G q ∧ ∀ v, q v=true → p v=true := by
  obtain ⟨q,Q,sub,small⟩ := deepest p P
  exact ⟨q,min_terminal hh Q small,sub⟩

theorem ChordHalf.some_vertex {M} {G : IsDiskFullerene M h} {p} (P : ChordHalf G p) :
    ∃ v, p v=true := by
  obtain ⟨_,_,_,_,_,_,S,b,C⟩ := P
  cases b with
  | true => obtain ⟨v,hv⟩ := S.part.inhabitedLeft; exact ⟨v,(C v).mpr hv⟩
  | false =>
    obtain ⟨v,hv⟩ := S.part.inhabitedRight
    exact ⟨v,by have := C v; cases hp : p v <;> simp_all⟩

theorem TerminalHalf.eq_of_overlap {M} {G : IsDiskFullerene M h} {p q} (P : TerminalHalf G p)
    (Q : TerminalHalf G q) {t} (pt : p t=true) (qt : q t=true) : p=q := by
  obtain ⟨b,allp⟩ := P.2 q Q.1
  obtain ⟨a,allq⟩ := Q.2 p P.1
  have qb := allp t pt; have pa := allq t qt
  funext v
  cases pv : p v <;> cases qv : q v <;> grind

/-- A chord in the outer link of an arbitrary input map gives two actual
disjoint chord halves, each left intact by every other chord cut. -/
theorem two_terminal_ends {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : HasChord G) :
    ∃ p q, TerminalHalf G p ∧ TerminalHalf G q ∧ ∀ v, ¬(p v=true ∧ q v=true) := by
  obtain ⟨f,F⟩ := initial_half G hh hc
  obtain ⟨p,P,sp,mp⟩ := deepest f F
  obtain ⟨q,Q,sq,mq⟩ := deepest _ F.complement
  refine ⟨p,q,min_terminal hh P mp,min_terminal hh Q mq,?_⟩
  rintro v ⟨pv,qv⟩
  have a := sp v pv
  have b := sq v qv
  simp [a] at b

end DiskFullerene.Dual
