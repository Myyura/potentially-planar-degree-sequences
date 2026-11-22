import FullBlocks
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import TraceCheck

/-! Histogram and per-face invariants on the permanent-name recurrence. -/
namespace Recognition.FullDegrees
open QuotientDP PlanarDegrees.Frontier PlanarDegrees.Topology Recognition.Witness Finset

private def retired (U : Finset (Name n)) (s : State n) := U \ liveSet s

private theorem corners (a : Triangle n) (k : Fin 3) : a.v k∈vertices a :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

private theorem unchanged (s : State n) (a : Triangle n) (x : Name n) (outside : x∉vertices a) :
    active (opened s a) x=active s.pending x ∧ value s a x=s.current x := by
  have miss (y : Name n) : on a (x,y)=false := by
    cases h : on a (x,y)
    · rfl
    · obtain ⟨k,e|e⟩ := of_decide_eq_true h
      · have eq : a.v k = x := congrArg Prod.fst e
        exact (outside (eq ▸ corners a k)).elim
      · have eq : a.v (k+1) = x := congrArg Prod.fst e
        exact (outside (eq ▸ corners a (k+1))).elim
  have off (k : Fin 3) : contributing s a x k=false := by
    have l : a.v k≠x := fun e => outside (e ▸ corners a k)
    have r : a.v (k+1)≠x := fun e => outside (e ▸ corners a (k+1))
    simp [contributing,l,r]
  constructor
  · apply Bool.eq_iff_iff.mpr
    simp [active,opened,miss]
  · simp [value,tally,off]

private theorem release_list (s : State n) (a : Triangle n) (inj : Function.Injective a.v) :
    released s a = ((vertices a \ liveSet (fullNext s a)).val.map (value s a)) := by
  let ks := (List.finRange 3).filter fun k => !(active (opened s a) (a.v k))
  let vs := ks.map a.v
  have nd : vs.Nodup := ((List.nodup_finRange 3).filter _).map inj
  have setEq : vs.toFinset = vertices a \ liveSet (fullNext s a) := by
    ext x
    simp only [vs,List.mem_toFinset,List.mem_map,ks,List.mem_filter,List.mem_finRange,true_and,
      Bool.not_eq_true',Finset.mem_sdiff,vertices,Finset.mem_image,Finset.mem_univ,liveSet,Finset.mem_filter]
    change (∃ k, active (opened s a) (a.v k)=false ∧ a.v k=x) ↔
      (∃k, a.v k=x) ∧ ¬ active (opened s a) x=true
    constructor
    · rintro ⟨k,no,rfl⟩; exact ⟨⟨k,rfl⟩,by simp [no]⟩
    · rintro ⟨⟨k,rfl⟩,no⟩; exact ⟨k,by simpa using no,rfl⟩
  rw [←setEq,List.toFinset_val,List.dedup_eq_self.mpr nd,Multiset.map_coe]
  simp [vs,ks,released,List.map_map,Function.comp_def]

private theorem retired_step {U : Finset (Name n)} (s : State n) (a : Triangle n)
    (eligible : ∀k, a.v k∈U → active s.pending (a.v k)) :
    retired (U∪vertices a) (fullNext s a) =
    (retired U s) ∪ (vertices a \ liveSet (fullNext s a)) ∧
    Disjoint (retired U s) (vertices a \ liveSet (fullNext s a)) := by
  have sep {x} (ret : x∈retired U s) : x∉vertices a := by
    intro mem
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp mem
    obtain ⟨old,notLive⟩ := Finset.mem_sdiff.mp ret
    exact notLive (Finset.mem_filter.mpr ⟨Finset.mem_univ _, eligible k old⟩)
  constructor
  · ext x
    by_cases inside : x∈vertices a
    · have notR : x∉retired U s := fun h => sep h inside
      simp [retired,inside] at notR ⊢
      grind
    · have no := (unchanged s a x inside).1
      simp only [retired,Finset.mem_sdiff,Finset.mem_union,inside,false_and,or_false,liveSet,
        Finset.mem_filter,Finset.mem_univ,true_and]
      change (_ ∧ ¬active (opened s a) x=true) ↔ _
      rw [no]
  · exact Finset.disjoint_left.mpr (fun _ h q => sep h (Finset.mem_sdiff.mp q).1)

theorem histogram {fs : List (Triangle n)} {s : State n}
    (run : FullRun bound target fs U s) :
    s.remaining + (retired U s).val.map s.current = target := by
  induction run with
  | init => simp [retired,start,liveSet]
  | @step past U s t prev a eligible ok ih =>
    unfold fullAdvance at ok
    split at ok <;> rename_i good
    · obtain rfl := Option.some.inj ok
      have g := of_decide_eq_true good
      obtain ⟨eq,dis⟩ := retired_step s a eligible
      rw [eq,←Finset.disjUnion_eq_union _ _ dis,Finset.disjUnion_val,Multiset.map_add]
      change (s.remaining - released s a) + ((retired U s).val.map (value s a) +
        (vertices a \ liveSet (fullNext s a)).val.map (value s a)) = target
      have unchangedMap : (retired U s).val.map (value s a) = (retired U s).val.map s.current := by
        apply Multiset.map_congr rfl
        intro x mem
        apply (unchanged s a x ?_).2
        intro inA
        obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp inA
        obtain ⟨old,no⟩ := Finset.mem_sdiff.mp mem
        exact no (Finset.mem_filter.mpr ⟨Finset.mem_univ _,eligible k old⟩)
      rw [unchangedMap,←release_list s a g.1,add_left_comm _ _ (released s a),
        Multiset.sub_add_cancel g.2.2.2.2.1,add_comm]
      exact ih
    · contradiction

structure Facts {n} (fs : List (Triangle n)) (U : Finset (Name n)) (s : State n) : Prop where
  live : liveSet s⊆U
  used : s.used=U.card
  faces : s.faces=fs.length
  inj : ∀a∈fs, Function.Injective a.v
  present : ∀x∈U, ∃a∈fs,x∈vertices a

theorem facts (h : FullRun bound target fs U s) : Facts fs U s := by
  induction h with
  | init => constructor <;> simp [start,liveSet,active]
  | @step past U s t prev a eligible ok ih =>
    unfold fullAdvance at ok; split at ok <;> rename_i g
    · obtain rfl := Option.some.inj ok
      have inj := (of_decide_eq_true g).1
      refine ⟨?_,used_next s U a eligible ih.live inj ih.used,by simp [fullNext,nextState,ih.faces],?_,?_⟩
      · intro x hx
        rcases next_live s a x (Finset.mem_filter.mp hx).2 with old|new
        · exact Finset.mem_union_left _ (ih.live (Finset.mem_filter.mpr ⟨Finset.mem_univ _,old⟩))
        · exact Finset.mem_union_right _ new
      · intro b hb; rcases List.mem_cons.mp hb with rfl|mem
        · exact inj
        · exact ih.inj b mem
      · intro x hx; rcases Finset.mem_union.mp hx with old|new
        · obtain ⟨b,bh,bx⟩ := ih.present x old
          exact ⟨b,List.mem_cons_of_mem _ bh,bx⟩
        · exact ⟨a,List.mem_cons_self,new⟩
    · contradiction

private def sortedEdge (x y : Nat) (hne : x≠y) : Edge :=
  if h : x<y then ⟨x,y,h⟩ else ⟨y,x,by omega⟩

private theorem sorted_match (x y : Nat) (ne : x≠y) (e : Edge) :
    sortedEdge x y ne=e ↔ (x=e.lo ∧ y=e.hi) ∨ (x=e.hi ∧ y=e.lo) := by
  cases e with | mk l h lt =>
    by_cases eq : x<y <;> simp [sortedEdge,eq,Edge.mk.injEq] <;> omega

def eventAt (a : Triangle n) (hi : Function.Injective a.v) (k : Fin 3) : Event :=
  ⟨sortedEdge (a.v k).val (a.v (k+1)).val (fun eq => (by decide : ∀ k : Fin 3,k≠k+1) k (hi (Fin.ext eq))),a.color k⟩

private def normalized (a : Triangle n) (h : Function.Injective a.v) :
    {F : Face // F.sides.Perm ((List.finRange 3).map (eventAt a h)) ∧
      (cornerNames F).Perm [(a.v 0).val,(a.v 1).val,(a.v 2).val]} := by
  let x := (a.v 0).val
  let y := (a.v 1).val
  let z := (a.v 2).val
  have xy : x≠y := fun t => (by decide : (0:Fin 3)≠1) (h (Fin.ext t))
  have yz : y≠z := fun t => (by decide : (1:Fin 3)≠2) (h (Fin.ext t))
  have zx : z≠x := fun t => (by decide : (2:Fin 3)≠0) (h (Fin.ext t))
  let p := a.color 0
  let q := a.color 1
  let r := a.color 2
  change {F : Face // F.sides.Perm
    [⟨sortedEdge x y xy,p⟩,⟨sortedEdge y z yz,q⟩,⟨sortedEdge z x zx,r⟩] ∧
    (cornerNames F).Perm [x,y,z]}
  by_cases hxy : x<y
  · by_cases hyz : y<z
    · refine ⟨⟨x,y,z,hxy,hyz,p,r,q⟩,?_,.refl _⟩
      apply Multiset.coe_eq_coe.mp
      simp only [Face.sides,sortedEdge,hxy,hyz,show ¬z<x by omega,↓reduceDIte, ←Multiset.cons_coe, Multiset.coe_nil, ←Multiset.singleton_add]; ac_rfl
    · have hzy : z<y := by omega
      by_cases hzx : z<x
      · refine ⟨⟨z,x,y,hzx,hxy,r,q,p⟩,?_,?_⟩ <;> apply Multiset.coe_eq_coe.mp <;>
          simp only [Face.sides,cornerNames,sortedEdge,hxy,hzx,show ¬y<z by omega,↓reduceDIte, ←Multiset.cons_coe, Multiset.coe_nil, ←Multiset.singleton_add] <;> ac_rfl
      · have hxz : x<z := by omega
        refine ⟨⟨x,z,y,hxz,hzy,r,p,q⟩,?_,?_⟩ <;> apply Multiset.coe_eq_coe.mp <;>
          simp only [Face.sides,cornerNames,sortedEdge,hxy,show ¬z<x by omega,show ¬y<z by omega,↓reduceDIte, ←Multiset.cons_coe, Multiset.coe_nil, ←Multiset.singleton_add] <;> ac_rfl
  · have hyx : y<x := by omega
    by_cases hzx : z<x
    · by_cases hyz : y<z
      · refine ⟨⟨y,z,x,hyz,hzx,q,p,r⟩,?_,?_⟩ <;> apply Multiset.coe_eq_coe.mp <;>
          simp only [Face.sides,cornerNames,sortedEdge,hyz,hzx,show ¬x<y by omega,↓reduceDIte, ←Multiset.cons_coe, Multiset.coe_nil, ←Multiset.singleton_add] <;> ac_rfl
      · have hzy : z<y := by omega
        refine ⟨⟨z,y,x,hzy,hyx,q,r,p⟩,?_,?_⟩ <;> apply Multiset.coe_eq_coe.mp <;>
          simp only [Face.sides,cornerNames,sortedEdge,hzx,show ¬y<z by omega,show ¬x<y by omega,↓reduceDIte, ←Multiset.cons_coe, Multiset.coe_nil, ←Multiset.singleton_add] <;> ac_rfl
    · have hxz : x<z := by omega
      refine ⟨⟨y,x,z,hyx,hxz,p,q,r⟩,?_,?_⟩ <;> apply Multiset.coe_eq_coe.mp <;>
        simp only [Face.sides,cornerNames,sortedEdge,show ¬x<y by omega,show y<z by omega,show ¬z<x by omega,↓reduceDIte, ←Multiset.cons_coe, Multiset.coe_nil, ←Multiset.singleton_add]; ac_rfl

def row (a : Triangle n) : Face :=
  if h : Function.Injective a.v then (normalized a h).val else ⟨0,1,2,by decide,by decide,false,false,false⟩

theorem row_spec (a : Triangle n) (h : Function.Injective a.v) :
    (row a).sides.Perm ((List.finRange 3).map (eventAt a h)) ∧
      (cornerNames (row a)).Perm [(a.v 0).val,(a.v 1).val,(a.v 2).val] := by
  rw [row,dite_eq_left h]
  exact (normalized a h).property

theorem row_corner (a : Triangle n) (h : Function.Injective a.v) (x : Fin n) :
    x.val∈cornerNames (row a) ↔ x∈vertices a := by
  rw [(row_spec a h).2.mem_iff]
  simp only [List.mem_cons,List.not_mem_nil,or_false,vertices,Finset.mem_image,Finset.mem_univ,true_and,Fin.val_inj]
  constructor
  · rintro (rfl|rfl|rfl) <;> exact ⟨_,rfl⟩
  · rintro ⟨k,rfl⟩; fin_cases k <;> simp

theorem row_bound (a : Triangle n) (h : Function.Injective a.v) : (row a).z<n := by
  have m : (row a).z∈cornerNames (row a) := by simp [cornerNames]
  have mem := (row_spec a h).2.mem_iff.mp m
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with eq|eq|eq <;> rw [eq] <;> exact Fin.isLt _

def rows (fs : List (Triangle n)) := fs.flatMap fun a => (row a).sides

def Represents (p : Side n) (e : Edge) : Prop :=
  (p.1.val=e.lo ∧ p.2.val=e.hi) ∨ (p.1.val=e.hi ∧ p.2.val=e.lo)

theorem represented_slot (a : Triangle n) (inj : Function.Injective a.v) (k : Fin 3) (e : Edge) :
    (eventAt a inj k).edge=e ↔ Represents (side a k) e := sorted_match _ _ (fun eq => (by decide : ∀ k : Fin 3,k≠k+1) k (inj (Fin.ext eq))) _

private theorem same_pair {p q : Side n} {e : Edge} (h : Represents p e) :
    Represents q e ↔ q=p ∨ q.swap=p := by
  obtain ⟨u,v⟩ := p
  obtain ⟨x,y⟩ := q
  simp only [Represents,Prod.ext_iff,Prod.swap,Fin.ext_iff] at *
  grind

theorem row_side (a : Triangle n) (inj : Function.Injective a.v) {p : Side n} {e : Edge}
    (h : Represents p e) : e∈sideNames (row a) ↔ on a p=true := by
  unfold sideNames
  rw [((row_spec a inj).1.map Event.edge).mem_iff]
  simp only [List.mem_map,List.mem_finRange,true_and,on,decide_eq_true_eq]
  constructor
  · rintro ⟨_,⟨k,rfl⟩,eq⟩
    exact ⟨k,(same_pair h).mp ((represented_slot a inj k e).mp eq)⟩
  · rintro ⟨k,hk⟩
    exact ⟨_,⟨k,rfl⟩,(represented_slot a inj k e).mpr ((same_pair h).mpr hk)⟩

theorem count_rows (fs : List (Triangle n)) (proper : ∀a∈fs,Function.Injective a.v)
    {p : Side n} {e : Edge} (h : Represents p e) :
    occurrences (rows fs) e = FullBlocks.occurrences fs p := by
  induction fs with
  | nil => simp [rows,occurrences,FullBlocks.occurrences]
  | cons a fs ih =>
    have inj := proper a List.mem_cons_self
    have tail := ih (fun b hb => proper b (List.mem_cons_of_mem _ hb))
    have nd : (sideNames (row a)).Nodup := (row a).distinct_sides
    rw [show rows (a::fs)=(row a).sides++rows fs from rfl]
    simp only [occurrences,List.map_append,List.count_append]
    change (sideNames (row a)).count e+occurrences (rows fs) e=_
    rw [tail,nd.count]
    by_cases hp : on a p=true <;> simp [FullBlocks.occurrences,hp,(row_side a inj h).mpr, row_side a inj h,add_comm]

private theorem represented_bound (h : Represents (p : Side n) e) : e.hi<n := by
  rcases h with ⟨_,q⟩|⟨q,_⟩ <;> exact q ▸ Fin.isLt _

theorem outside_rows (fs : List (Triangle n)) (proper : ∀a∈fs,Function.Injective a.v)
    {e : Edge} (out : ¬e.hi<n) : occurrences (rows fs) e = 0 := by
  apply List.count_eq_zero.mpr
  intro mem
  obtain ⟨ev,hm,eq⟩ := List.mem_map.mp mem
  obtain ⟨a,ha,evm⟩ := List.mem_flatMap.mp hm
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp ((row_spec a (proper a ha)).1.mem_iff.mp evm)
  exact out (represented_bound ((represented_slot a (proper a ha) k e).mp eq))

private def bump (past : List Event) (x : Nat) (a : Event) : Bool :=
  decide (occurrences past a.edge=0) && a.red && touches a.edge x

private theorem unique_bumps (xs past : List Event) (x : Nat) (nd : (xs.map Event.edge).Nodup) :
    simpleDegree (reds (xs++past)) x = simpleDegree (reds past) x + xs.countP (bump past x) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨absent,rest⟩ := List.nodup_cons.mp nd
    have count : occurrences (xs++past) a.edge = occurrences past a.edge := by
      simp [occurrences,List.count_eq_zero.mpr absent]
    have tail := ih rest
    rw [List.cons_append,reds,count]
    by_cases fresh : occurrences past a.edge=0 <;> cases red : a.red <;> cases touch : touches a.edge x <;>
      simp [fresh,red,touch,bump,simpleDegree] at tail ⊢ <;> omega

private theorem slot_touch (a : Triangle n) (inj : Function.Injective a.v) (k : Fin 3) (x : Fin n) :
    touches (eventAt a inj k).edge x.val=(a.v k==x || a.v (k+1)==x) := by
  have h := (represented_slot a inj k _).mp rfl
  apply Bool.eq_iff_iff.mpr
  simp only [touches,Bool.or_eq_true,beq_iff_eq,Fin.ext_iff,Represents,side] at *
  grind

theorem degrees {fs : List (Triangle n)} {s : State n} (run : FullRun bound target fs U s) (x : Fin n) :
    s.current x = simpleDegree (reds (rows fs)) x.val := by
  induction run with
  | init => simp [start,rows,reds,simpleDegree]
  | @step past U s t prev a eligible ok ih =>
    unfold fullAdvance at ok; split at ok <;> rename_i good
    · obtain rfl := Option.some.inj ok
      have g := of_decide_eq_true good
      have inj := g.1
      have inv := FullBlocks.inventory_exact prev
      have atSlot (k) : bump (rows past) x.val (eventAt a inj k)=contributing s a x k := by
        have hs := g.2.2.2.1 k
        have cap := inv.cap (side a k)
        have op := inv.open_ (side a k)
        have cl := inv.close (side a k)
        have cnt := count_rows past (facts prev).inj ((represented_slot a inj k _).mp rfl)
        have eq : decide (occurrences (rows past) (eventAt a inj k).edge=0) = !(s.pending (side a k)) := by
          rw [cnt]; cases pend : s.pending (side a k) <;> simp_all; omega
        simp only [bump,contributing,eq,slot_touch]
        rfl
      change s.current x+tally (contributing s a x)=simpleDegree (reds ((row a).sides++rows past)) x.val
      rw [unique_bumps _ _ _ (row a).distinct_sides,ih,((row_spec a inj).1).countP_eq]
      congr 1
      rw [List.countP_map]
      simp only [Function.comp_def,atSlot,tally,List.countP_eq_length_filter]
    · contradiction

theorem terminal_histogram {fs : List (Triangle n)} {s : State n} (run : FullRun bound target fs U s)
    (done : finished bound s) :
    target = (Finset.univ : Finset (Fin n)).val.map (fun x => simpleDegree (reds (rows fs)) x.val) := by
  obtain ⟨_,used,remaining,pending⟩ := of_decide_eq_true done
  have allUsed : U=univ := Finset.eq_univ_of_card _ (by simpa [←(facts run).used] using used)
  have no : liveSet s=∅ := by ext x; simp [liveSet,active,pending]
  have h := histogram run
  simp only [retired,allUsed,no,Finset.sdiff_empty,remaining,zero_add] at h
  rw [←h]
  exact Multiset.map_congr rfl (fun x _ => degrees run x)


private theorem terminal_paired {fs : List (Triangle n)} {s : State n}
    (run : FullRun bound target fs U s) (done : finished bound s) :
    ∀ e, occurrences (rows fs) e=0 ∨ occurrences (rows fs) e=2 := by
  intro e
  by_cases small : e.hi<n
  · let p : Side n := (⟨e.lo,Nat.lt_trans e.increasing small⟩,⟨e.hi,small⟩)
    have rep : Represents p e := Or.inl ⟨rfl,rfl⟩
    rw [count_rows fs (facts run).inj rep]
    have cap := (FullBlocks.inventory_exact run).cap p
    have no := (FullBlocks.inventory_exact run).open_ p
    have pend := (of_decide_eq_true done).2.2.2 p
    simp [pend] at no
    omega
  · exact Or.inl (outside_rows fs (facts run).inj small)

theorem exists_edge {a : Triangle n} (inj : Function.Injective a.v) {p : Side n}
    (used : on a p=true) : ∃e, Represents p e := by
  obtain ⟨k,eq⟩ := of_decide_eq_true used
  let e := (eventAt a inj k).edge
  have rep : Represents (side a k) e := (represented_slot a inj k _).mp rfl
  refine ⟨e,(same_pair rep).mpr ?_⟩
  rcases eq with h|h
  · exact Or.inl h.symm
  · exact Or.inr (by simp [←h])

/-- Restore the original face order and use the input colors at their first occurrence. -/
theorem terminal_trace {f v : Nat} {fs : List (Triangle (v+1))} {s : State (v+1)} {U : Finset (Fin (v+1))}
    (run : FullRun (f+1) target fs U s) (done : finished (f+1) s) :
    ∃ C : ClosedTrace v f, (List.finRange (f+1)).map C.faces=fs.map row ∧
      sideTrace C.faces=rows fs := by
  have fact := facts run
  obtain ⟨fNum,vNum,_,_⟩ := of_decide_eq_true done
  have len := fact.faces.symm.trans fNum
  let Q := (FullBlocks.indexEquiv fs).trans (finCongr len)
  let F (i : Fin (f+1)) := row (fs[i.val]'(by rw [len];exact i.isLt))
  have faceEq (i : FullBlocks.Index fs) : F (Q i)=row (FullBlocks.faceAt fs i) := by
    rw [FullBlocks.faceAt_get]; rfl
  have bounded (i : Fin (f+1)) : (F i).z<v+1 := row_bound _ (fact.inj _ (List.getElem_mem _))
  have allUsed : U=univ := Finset.eq_univ_of_card _ (by simpa [←fact.used] using vNum)
  have used (x : Fin (v+1)) : ∃i,x.val∈cornerNames (F i) := by
    obtain ⟨a,mem,present⟩ := fact.present x (allUsed ▸ Finset.mem_univ x)
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp mem
    exact ⟨⟨j,len ▸ hj⟩,(row_corner _ (fact.inj _ (List.getElem_mem _)) x).mpr present⟩
  have liftStep {i j : FullBlocks.Index fs} (step : FullBlocks.Dual fs i j) : shared F (Q i) (Q j) := by
    obtain ⟨different,p,left,right⟩ := (FullBlocks.dual_iff fs i j).mp step
    have inj (u : FullBlocks.Index fs) : Function.Injective (FullBlocks.faceAt fs u).v :=
      fact.inj _ (by rw [FullBlocks.faceAt_get]; exact List.getElem_mem _)
    obtain ⟨e,rep⟩ := exists_edge (inj i) left
    exact ⟨fun eq => different (Q.injective eq),e,faceEq i ▸ (row_side _ (inj i) rep).mpr left,
      faceEq j ▸ (row_side _ (inj j) rep).mpr right⟩
  have lift {i j : FullBlocks.Index fs} (w : Walk (FullBlocks.Dual fs) i j) : Walk (shared F) (Q i) (Q j) := by
    induction w with
    | refl => exact .refl
    | step _ step ih => exact .step ih (liftStep step)
  have conn (i : Fin (f+1)) : Walk (shared F) 0 i := by
    simpa using lift (FullBlocks.terminal_connected run done (Q.symm 0) (Q.symm i))
  have FList : (List.finRange (f+1)).map F=fs.map row := by
    apply List.ext_getElem
    · simp [len]
    · intro i h₁ h₂; simp [F]
  have trace : sideTrace F=rows fs := by
    unfold sideTrace rows
    simp only [←List.flatMap_map] at *
    exact congrArg (List.flatMap Face.sides) FList
  obtain ⟨ledger,accept,closed⟩ := paired_iff_closed.mp (terminal_paired run done)
  exact ⟨⟨F,bounded,used,conn,ledger,trace ▸ accept,closed⟩,FList,trace⟩

/-- A permanent-name run that passes the final numerical tests produces
an accepting bounded certificate with precisely the advertised degrees. -/
theorem full_certificate {v f : Nat} (ds : List Nat) {fs : List (Triangle (v+1))} {s : State (v+1)} {U : Finset (Fin (v+1))}
    (run : FullRun (f+1) (ds : Multiset Nat) fs U s) (done : finished (f+1) s)
    (four : 4≤v+1) (euler : (f+1)+4=2*(v+1)) :
    ∃ r : TraceCheck.Records v f, TraceCheck.verify ds r := by
  obtain ⟨C,_,trace⟩ := terminal_trace run done
  have degree (x : Fin (v+1)) : C.ledger.redDegree x.val = simpleDegree (reds (rows fs)) x.val :=
    trace ▸ (replay_accurate C.accepted).redDegree x.val
  have names : (List.finRange (v+1)).map Fin.val = List.range (v+1) := by
    apply List.ext_getElem <;> simp
  have perm : (witnessDegrees C).Perm ds := by
    apply Multiset.coe_eq_coe.mp
    rw [terminal_histogram run done]
    change ((List.map C.ledger.redDegree (List.range (v+1)) : List Nat) : Multiset Nat)=_
    rw [←names,List.map_map,←Multiset.map_coe]
    have every : ((List.finRange (v+1) : List (Fin (v+1))) : Multiset _)=(Finset.univ : Finset (Fin (v+1))).val := by
      have eq : (List.finRange (v+1)).toFinset=Finset.univ := by ext; simp
      rw [←eq,List.toFinset_val,List.dedup_eq_self.mpr (List.nodup_finRange _)]
    rw [every]; exact Multiset.map_congr rfl (fun x _ => degree x)
  exact ⟨TraceCheck.recordsOf C,TraceCheck.verify_complete ds C four euler perm⟩


/-- The inverse normalization puts the corners in increasing cyclic order. -/
def fromFace (F : Face) (bound : F.z<n) : Triangle n where
  v := ![⟨F.x,lt_trans F.xy (lt_trans F.yz bound)⟩,⟨F.y,lt_trans F.yz bound⟩,⟨F.z,bound⟩]
  color := ![F.redXY,F.redYZ,F.redXZ]

theorem fromFace_injective (F : Face) (bound : F.z<n) : Function.Injective (fromFace F bound).v := by
  intro i j eq
  have h := congrArg Fin.val eq
  have xy := F.xy
  have yz := F.yz
  fin_cases i <;> fin_cases j <;> simp [fromFace] at h ⊢ <;> omega

private theorem face_unique {F G : Face} (corners : (cornerNames F).Perm (cornerNames G))
    (events : F.sides.Perm G.sides) : F=G := by
  obtain ⟨x,y,z,xy,yz,p,q,r⟩ := F
  obtain ⟨u,v,w,uv,vw,l,m,n⟩ := G
  have same (i : Nat) : i∈cornerNames _ ↔ i∈cornerNames _ := corners.mem_iff
  simp only [cornerNames,List.mem_cons,List.not_mem_nil,or_false] at same
  have hx := same x
  have hy := same y
  have hz := same z
  have xu : x=u := by omega
  have yv : y=v := by omega
  have zw : z=w := by omega
  subst u; subst v; subst w
  have event (E : Event) : E∈Face.sides _ ↔ E∈Face.sides _ := events.mem_iff
  have color₁ := event ⟨⟨x,y,xy⟩,p⟩
  have color₂ := event ⟨⟨x,z,lt_trans xy yz⟩,q⟩
  have color₃ := event ⟨⟨y,z,yz⟩,r⟩
  simp [Face.sides,Event.mk.injEq,Edge.mk.injEq,ne_of_lt xy,ne_of_lt yz,
    ne_of_gt xy,ne_of_gt yz] at color₁ color₂ color₃
  grind

theorem row_fromFace (F : Face) (bound : F.z<n) : row (fromFace F bound)=F := by
  obtain ⟨x,y,z,xy,yz,p,q,r⟩ := F
  have S := row_spec _ (fromFace_injective _ bound)
  apply face_unique S.2
  apply S.1.trans
  change ([⟨sortedEdge x y _,p⟩,⟨sortedEdge y z _,r⟩,⟨sortedEdge z x _,q⟩] : List Event).Perm _
  simp only [Face.sides,sortedEdge,xy,yz,show ¬z<x by omega,↓reduceDIte]
  exact .cons _ (.swap ..)

theorem fromFace_vertex (F : Face) (bound : F.z<n) (u : Fin n) :
    u∈vertices (fromFace F bound) ↔ u.val∈cornerNames F := by
  simpa only [row_fromFace] using (row_corner _ (fromFace_injective F bound) u).symm

theorem fromFace_side (F : Face) (bound : F.z<n) (p : Side n) :
    on (fromFace F bound) p=true ↔ ∃d∈sideNames F, Witness.joins d p.1.val p.2.val=true := by
  have characterized (d) : Represents p d ↔ Witness.joins d p.1.val p.2.val=true := by
    simp [Represents,Witness.joins]; grind
  have inj := fromFace_injective F bound
  constructor
  · intro on
    obtain ⟨d,rep⟩ := exists_edge inj on
    exact ⟨d,row_fromFace F bound ▸ (row_side _ inj rep).mpr on,(characterized d).mp rep⟩
  · rintro ⟨d,hd,j⟩
    apply (row_side _ inj ((characterized d).mpr j)).mp
    simpa only [row_fromFace] using hd

end Recognition.FullDegrees
