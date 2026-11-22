import FullDegrees
import Overlay

/-! Identify every coordinate of a concrete compact state with the frontier
inventory and dual patch relation used to encode its planar overlay. -/
namespace Recognition.PrefixModel
open Recognition.QuotientDP Recognition.FullBlocks Recognition.FullDegrees
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep PlanarDegrees.Topology

structure Match (fs : List (QuotientDP.Triangle n)) (s : PlanarDegrees.Frontier.Inventory) (t : State n) : Prop where
  pending : ∀ a b, t.pending (a,b) ↔ ∃ e∈s.pending, Represents (a,b) e
  sealed : ∀ a b, t.sealed (a,b) ↔ ∃ e∈retain (live s) s, Represents (a,b) e
  blocks : ∀ a b c d, t.blocks (a,b) (c,d) ↔ ∃ e∈s.pending, ∃ f∈s.pending,
    Represents (a,b) e ∧ Represents (c,d) f ∧ Overlay.sameBlock (fs.map FullDegrees.row) e f
  current : ∀ a, t.current a=if live s a.val then s.redDegree a.val else 0

private theorem bound_edge {a : QuotientDP.Triangle n} {d : Edge} (ha : Function.Injective a.v) (hd : d∈sideNames (FullDegrees.row a)) : d.hi<n := by
  have max := row_bound a ha
  have yz := (FullDegrees.row a).yz
  simp [sideNames,Face.sides] at hd
  rcases hd with rfl|rfl|rfl
  · exact lt_trans yz max
  · exact max
  · exact max

private def rank (fs : List (QuotientDP.Triangle n)) : Index fs ≃ Overlay.Id (fs.map FullDegrees.row) :=
  (indexEquiv fs).trans (finCongr (by simp))

private theorem flags (fs : List (QuotientDP.Triangle n)) (i : Index fs) :
    Overlay.flags (fs.map FullDegrees.row) (rank fs i)=sideNames (FullDegrees.row (faceAt fs i)) := by
  rw [faceAt_get]; simp [Overlay.flags,rank,sideNames]

private theorem block_walk {fs : List (QuotientDP.Triangle n)} (proper : ∀ a∈fs,Function.Injective a.v)
    (i j : Index fs) : PlanarDegrees.Frontier.Walk (Dual fs) i j ↔
    PlanarDegrees.Frontier.Walk (Overlay.adjacency (fs.map FullDegrees.row) (fun _ => True)) (rank fs i) (rank fs j) := by
  have inject (i) := proper (faceAt fs i) (by rw [faceAt_get]; exact List.getElem_mem _)
  have imp (i j) (h : Dual fs i j) : Overlay.adjacency (fs.map FullDegrees.row) (fun _ => True) (rank fs i) (rank fs j) := by
    obtain ⟨_,p,hi,hj⟩ := (dual_iff fs i j).mp h
    obtain ⟨d,rep⟩ := exists_edge (inject i) hi
    exact ⟨d,(flags fs i).symm ▸ (row_side _ (inject i) rep).mpr hi,
      (flags fs j).symm ▸ (row_side _ (inject j) rep).mpr hj,trivial⟩
  refine ⟨fun w => w.map (rank fs) imp,?_⟩
  have back {a b} (w : PlanarDegrees.Frontier.Walk (Overlay.adjacency (fs.map FullDegrees.row) (fun _ => True)) a b) :
      PlanarDegrees.Frontier.Walk (Dual fs) ((rank fs).symm a) ((rank fs).symm b) := by
    induction w with
    | refl => exact .refl
    | @step l r _ h ih =>
      obtain ⟨x,rfl⟩ := (rank fs).surjective l
      obtain ⟨y,rfl⟩ := (rank fs).surjective r
      simp only [Equiv.symm_apply_apply] at ih ⊢
      by_cases ne : x=y
      · exact ne ▸ ih
      · obtain ⟨d,hd,jd,_⟩ := h
        rw [flags] at hd jd
        have limit := bound_edge (inject _) hd
        let p : Side n := (⟨d.lo,lt_trans d.increasing limit⟩,⟨d.hi,limit⟩)
        have rep : Represents p d := .inl ⟨rfl,rfl⟩
        exact ih.step ((dual_iff fs x y).mpr ⟨ne,p,(row_side _ (inject _) rep).mp hd,(row_side _ (inject _) rep).mp jd⟩)
  intro w; simpa using back w

private theorem shared (fs : List (QuotientDP.Triangle n)) (valid : ∀ a∈fs,Function.Injective a.v)
    {p q : Side n} {e d : Edge} (rep : Represents p e) (rep' : Represents q d) :
    (∃ i j : Index fs, inc fs i p ∧ inc fs j q ∧ PlanarDegrees.Frontier.Walk (Dual fs) i j) ↔ Overlay.sameBlock (fs.map FullDegrees.row) e d := by
  have inj (i) := valid (faceAt fs i) (by rw [faceAt_get]; exact List.getElem_mem _)
  constructor
  · rintro ⟨i,j,hi,hj,w⟩
    exact ⟨rank fs i,rank fs j,(flags fs i).symm ▸ (row_side _ (inj i) rep).mpr hi,
      (flags fs j).symm ▸ (row_side _ (inj j) rep').mpr hj,(block_walk valid i j).mp w⟩
  · rintro ⟨u,v,hu,hv,w⟩
    obtain ⟨i,rfl⟩ := (rank fs).surjective u
    obtain ⟨j,rfl⟩ := (rank fs).surjective v
    rw [flags] at hu hv
    exact ⟨i,j,(row_side _ (inj _) rep).mp hu,(row_side _ (inj _) rep').mp hv,(block_walk valid _ _).mpr w⟩

/-- The permanent face recurrence and the original endpoint-key replay
produce the same active edge sets, partition blocks and live red counters. -/
theorem correspondence {bound target fs U} {t : State n} (run : FullRun bound target fs U t) :
    ∃ s, replay (rows fs)=some s ∧ Match fs s (prune t) := by
  have valid := (facts run).inj
  have inv := inventory_exact run
  have limit (e : Edge) : PlanarDegrees.Frontier.occurrences (rows fs) e≤2 := by
    by_cases h : e.hi<n
    · let p : Side n := (⟨e.lo,lt_trans e.increasing h⟩,⟨e.hi,h⟩)
      rw [count_rows fs valid (show Represents p e from .inl ⟨rfl,rfl⟩)]; exact inv.cap p
    · rw [outside_rows fs valid h]; omega
  obtain ⟨s,hs⟩ := (replay_succeeds_iff _).mpr limit
  have acc := replay_accurate hs
  have bound (e) (h : e∈s.pending) : e.hi<n := by
    by_contra no; have zero := outside_rows fs valid no; have one := (acc.pending _).mp h; omega
  have forPos (p : Side n) (h : 0<FullBlocks.occurrences fs p) : ∃ e, Represents p e := by
    obtain ⟨i,hi⟩ := (occ_pos fs p).mp h
    exact exists_edge (valid _ (by rw [faceAt_get]; exact List.getElem_mem _)) hi
  have pending (p : Side n) : t.pending p ↔ ∃e∈s.pending,Represents p e := by
    rw [inv.open_]
    constructor
    · intro one; obtain ⟨e,rep⟩ := forPos p (by omega)
      exact ⟨e,(acc.pending _).mpr ((count_rows fs valid rep).trans one),rep⟩
    · rintro ⟨e,h,rep⟩; rw [←count_rows fs valid rep]; exact (acc.pending _).mp h
  have sealed (p : Side n) : t.sealed p ↔ ∃e∈s.sealed,Represents p e := by
    rw [inv.close]
    constructor
    · intro two; obtain ⟨e,rep⟩ := forPos p (by omega)
      exact ⟨e,(acc.sealed _).mpr ((count_rows fs valid rep).trans two),rep⟩
    · rintro ⟨e,h,rep⟩; rw [←count_rows fs valid rep]; exact (acc.sealed _).mp h
  have activeEq (v : Fin n) : active t.pending v=live s v.val := by
    apply Bool.eq_iff_iff.mpr; constructor
    · intro h; obtain ⟨w,hw⟩ := of_decide_eq_true h
      obtain ⟨e,op,rep⟩ := (pending (v,w)).mp hw
      exact List.any_eq_true.mpr ⟨e,op,by simp only [touches,Bool.or_eq_true,beq_iff_eq]; exact rep.elim (fun h => .inl h.1) (fun h => .inr h.1)⟩
    · intro hit; obtain ⟨e,op,vhit⟩ := List.any_eq_true.mp hit
      have hi := bound _ op; have lo := lt_trans e.increasing hi
      simp only [touches,Bool.or_eq_true,beq_iff_eq] at vhit
      rcases vhit with left|right
      · exact decide_eq_true ⟨⟨e.hi,hi⟩,(pending _).mpr ⟨e,op,.inl ⟨left,rfl⟩⟩⟩
      · exact decide_eq_true ⟨⟨e.lo,lo⟩,(pending _).mpr ⟨e,op,.inr ⟨right,rfl⟩⟩⟩
  refine ⟨s,hs,⟨fun a b => pending _,?_,?_,?_⟩⟩
  · intro a b
    change (livePair t.pending (a,b) && t.sealed (a,b))=true ↔ _
    simp only [livePair,activeEq,Bool.and_eq_true,sealed,retain,List.mem_filter]
    constructor
    · rintro ⟨⟨ha,hb⟩,e,hd,rep⟩
      exact ⟨e,⟨hd,by rcases rep with ⟨x,y⟩|⟨x,y⟩ <;> simp_all⟩,rep⟩
    · rintro ⟨e,⟨hd,lo,hi⟩,rep⟩
      exact ⟨(by rcases rep with ⟨x,y⟩|⟨x,y⟩ <;> simp_all),e,hd,rep⟩
  · intro a b c d
    rw [show (prune t).blocks (a,b) (c,d)=t.blocks (a,b) (c,d) from rfl,(blocks_exact run)]
    constructor
    · rintro ⟨p,q,w⟩
      obtain ⟨e,he,rep⟩ := (pending _).mp p; obtain ⟨f,hf,rep'⟩ := (pending _).mp q
      exact ⟨e,he,f,hf,rep,rep',(shared fs valid rep rep').mp w⟩
    · rintro ⟨e,he,f,hf,rep,rep',w⟩
      exact ⟨(pending _).mpr ⟨e,he,rep⟩,(pending _).mpr ⟨f,hf,rep'⟩,(shared fs valid rep rep').mpr w⟩
  · intro a
    have counter := degrees run a
    rw [← acc.redDegree a.val] at counter
    simp [prune,activeEq,counter]

end Recognition.PrefixModel
