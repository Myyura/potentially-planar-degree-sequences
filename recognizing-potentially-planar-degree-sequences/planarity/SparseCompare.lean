import StateIncidence
import FullBlocks
import BagHom
import Mathlib.Logic.Equiv.Fin.Basic

/-! Factor the relation on side nodes through its distinct nonempty rows.
For an equivalence relation each connected block contributes one centre
and two incidences per member, independently of the size of the block. -/
namespace Recognition.SparseCompare
open StateIso Finset

def low (A : Colored n) (i : Fin n) := decide (A.color i<4)

def row (A : Colored n) (i : Fin n) : Finset (Fin n) :=
  univ.filter fun j => low A i && low A j && A.edge i j

def blocks (A : Colored n) : List (Finset (Fin n)) :=
  (((List.finRange n).map (row A)).filter (· != ∅)).dedup

theorem block_mem (A : Colored n) (S : Finset (Fin n)) :
    S∈blocks A ↔ S≠∅ ∧ ∃i,row A i=S := by
  simp [blocks,and_comm]

private def oldArc (A : Colored n) (i j : Fin n) := !(low A i && low A j) && A.edge i j

abbrev Node (A : Colored n) := Fin n ⊕ Fin (blocks A).length

def color (A : Colored n) : Node A → Nat
  | .inl i => A.color i+1
  | .inr _ => 0

def arc (A : Colored n) : Node A → Node A → Bool
  | .inl i,.inl j => oldArc A i j
  | .inl i,.inr b => decide (row A i=(blocks A).get b)
  | .inr b,.inl j => decide (j∈(blocks A).get b)
  | .inr _,.inr _ => false

def graph (A : Colored n) : Colored (n+(blocks A).length) where
  color i := color A (finSumFinEquiv.symm i)
  edge i j := arc A (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

private def NIso (A : Colored n) (B : Colored m) :=
  ∃e : Node A≃Node B,(∀i,color A i=color B (e i)) ∧ ∀i j,arc A i j=arc B (e i) (e j)

private theorem node_iff (A : Colored n) (B : Colored m) : Iso (graph A) (graph B) ↔ NIso A B := by
  constructor
  · rintro ⟨e,c,a⟩
    refine ⟨finSumFinEquiv.trans (e.trans finSumFinEquiv.symm),fun i => ?_,fun i j => ?_⟩
    · simpa [graph] using c (finSumFinEquiv i)
    · simpa [graph] using a (finSumFinEquiv i) (finSumFinEquiv j)
  · rintro ⟨e,c,a⟩
    refine ⟨finSumFinEquiv.symm.trans (e.trans finSumFinEquiv),fun i => ?_,fun i j => ?_⟩
    · simpa [graph] using c (finSumFinEquiv.symm i)
    · simpa [graph] using a (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)

private noncomputable def blockNames (A : Colored n) : Fin (blocks A).length ≃ {b // b∈blocks A} :=
  Equiv.ofBijective (fun i => ⟨(blocks A).get i,List.get_mem ..⟩) (by
    constructor
    · intro i j eq; exact (List.nodup_iff_injective_get.mp (List.nodup_dedup _)) (congrArg Subtype.val eq)
    · rintro ⟨x,mem⟩; obtain ⟨i,hi,h⟩ := List.getElem_of_mem mem; exact ⟨⟨i,hi⟩,Subtype.ext h⟩)

private theorem forward {A : Colored n} {B : Colored m} (iso : Iso A B) : NIso A B := by
  obtain ⟨p,col,edge⟩ := iso
  have lowMap (x) : low A x=low B (p x) := by simp [low,col]
  have rowMap (x) : (row A x).map p.toEmbedding=row B (p x) := by
    ext y
    obtain ⟨y,rfl⟩ := p.surjective y
    simp [row,lowMap,edge]
  let q := p.finsetCongr
  have qr (x) : q (row A x)=row B (p x) := rowMap x
  have member (S) : S∈blocks A ↔ q S∈blocks B := by
    rw [block_mem,block_mem]
    have nonempty : q S≠∅ ↔ S≠∅ := by change (Finset.map p.toEmbedding S≠∅ ↔ S≠∅);simp
    rw [nonempty]
    constructor
    · rintro ⟨nz,x,rfl⟩;exact ⟨nz,p x,(qr x).symm⟩
    · rintro ⟨nz,y,h⟩; obtain ⟨x,rfl⟩:=p.surjective y; exact ⟨nz,x,q.injective ((qr x).trans h)⟩
  let r := (blockNames A).trans ((q.subtypeEquiv (p := fun s => s∈blocks A)
    (q := fun s => s∈blocks B) member).trans (blockNames B).symm)
  have image (i) : (blocks B).get (r i)=q ((blocks A).get i) := by
    have h := @Equiv.apply_symm_apply _ _ (blockNames B)
      ((q.subtypeEquiv (p := fun s => s∈blocks A) (q := fun s => s∈blocks B) member) ((blockNames A) i))
    exact congrArg Subtype.val h
  refine ⟨p.sumCongr r,?_,?_⟩
  · intro i; cases i <;> simp [color,col]
  · intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [arc,oldArc,lowMap,edge]
      | inr j =>
        change decide (_=(blocks A).get j) = decide (row B (p i)=(blocks B).get (r j))
        rw [image,←qr];simp
    | inr i =>
      cases j with
      | inl j =>
        change decide (j∈(blocks A).get i) = decide (p j∈(blocks B).get (r i))
        rw [image];simp [q]
      | inr j => rfl

private theorem recover (A : Colored n) (i j : Fin n) :
    A.edge i j=true ↔ arc A (.inl i) (.inl j)=true ∨
      ∃b,arc A (.inl i) (.inr b)=true ∧ arc A (.inr b) (.inl j)=true := by
  by_cases h : (low A i && low A j)=true
  · simp only [arc,oldArc,h,Bool.not_true,Bool.false_and,Bool.false_eq_true,false_or,decide_eq_true_eq]
    have inside : j∈row A i ↔ A.edge i j=true := by
      obtain ⟨l,r⟩:=Bool.and_eq_true_iff.mp h; simp [row,l,r]
    constructor
    · intro edge
      have mem := inside.mpr edge
      have entry := (block_mem A _).mpr ⟨Finset.ne_empty_of_mem mem,i,rfl⟩
      obtain ⟨b,hb,eq⟩:=List.getElem_of_mem entry
      exact ⟨⟨b,hb⟩,eq.symm,by change j∈(blocks A)[b]; rwa [eq]⟩
    · rintro ⟨b,eq,mem⟩; exact inside.mp (eq ▸ mem)
  · have zero := Bool.eq_false_iff.mpr h
    simp only [arc,oldArc,zero,Bool.not_false,Bool.true_and,decide_eq_true_eq]
    constructor
    · exact Or.inl
    · rintro (edge|⟨b,eq,mem⟩)
      · exact edge
      · have inRow : j∈row A i := eq ▸ mem
        exact ((Finset.mem_filter.mp inRow).2 |> Bool.and_eq_true_iff.mp).2

private theorem backward {A : Colored n} {B : Colored m} (iso : NIso A B) : Iso A B := by
  obtain ⟨q,col,edge⟩ := iso
  have left (i : Fin n) : ∃j,q (.inl i)=.inl j := by
    cases eq : q (.inl i) with
    | inl j => exact ⟨j,rfl⟩
    | inr b => have c := col (.inl i);simp [eq,color] at c
  have right (i : Fin (blocks A).length) : ∃j,q (.inr i)=.inr j := by
    cases eq : q (.inr i) with
    | inl j => have c:=col (.inr i);simp [eq,color] at c
    | inr j => exact ⟨j,rfl⟩
  let f (i : Fin n) := (left i).choose
  let g (i : Fin (blocks A).length) := (right i).choose
  have fl (i) : q (.inl i)=.inl (f i) := (left i).choose_spec
  have gr (i) : q (.inr i)=.inr (g i) := (right i).choose_spec
  have onto (j : Fin m) : ∃i,f i=j := by
    obtain ⟨i,eq⟩:=q.surjective (.inl j)
    cases i with
    | inl i => exact ⟨i,Sum.inl.inj ((fl i).symm.trans eq)⟩
    | inr i => rw [gr] at eq;cases eq
  have ontoR (b : Fin (blocks B).length) : ∃i,g i=b := by
    obtain ⟨i,eq⟩:=q.surjective (.inr b)
    cases i with
    | inr i => exact ⟨i,Sum.inr.inj ((gr i).symm.trans eq)⟩
    | inl i => rw [fl] at eq;cases eq
  let p := Equiv.ofBijective f ⟨fun i j eq => Sum.inl.inj (q.injective (by rw [fl,fl,eq])),onto⟩
  refine ⟨p,?_,?_⟩
  · intro i; have c:=col (.inl i);rw [fl] at c;exact Nat.add_right_cancel c
  · intro i j
    apply Bool.eq_iff_iff.mpr
    rw [recover,recover]
    change (_ ∨ _) ↔ arc B (.inl (f i)) (.inl (f j))=true ∨ _
    have base := edge (.inl i) (.inl j);rw [fl,fl] at base
    rw [base]; apply or_congr_right
    change (∃ b, _ ∧ _) ↔ ∃ b, arc B (.inl (f i)) (.inr b)=true ∧ arc B (.inr b) (.inl (f j))=true
    constructor
    · rintro ⟨b,l,r⟩
      exact ⟨g b,by rwa [←fl,←gr,←edge],by rwa [←fl,←gr,←edge]⟩
    · rintro ⟨b,l,r⟩
      obtain ⟨a,rfl⟩ := ontoR b
      exact ⟨a,by simpa only [←fl,←gr,←edge] using l,by simpa only [←fl,←gr,←edge] using r⟩

theorem graph_iff (A : Colored n) (B : Colored m) : Iso (graph A) (graph B) ↔ Iso A B :=
  (node_iff A B).trans ⟨backward,forward⟩

open QuotientDP in
def compare (s t : State n) := decide (s.remaining=t.remaining ∧ s.used=t.used ∧ s.faces=t.faces) &&
  BagHom.compare (graph (StateIncidence.graph s)) (graph (StateIncidence.graph t)) (List.finRange _)

open QuotientDP in
theorem compare_correct (s t : State n) : compare s t=true ↔ Same s t := by
  rw [StateIncidence.same_iff]
  simp only [compare,Bool.and_eq_true,decide_eq_true_eq,BagHom.compare_correct _ _ (List.Perm.refl _),graph_iff]
  tauto

theorem blocks_length (A : Colored n) : (blocks A).length≤n := by
  calc
    _ ≤ (((List.finRange n).map (row A)).filter (· != ∅)).length :=
      (List.dedup_sublist _).length_le
    _ ≤ ((List.finRange n).map (row A)).length := List.length_filter_le ..
    _ = n := by simp

theorem factor_size (A : Colored n) : n+(blocks A).length≤2*n := by
  have h:=blocks_length A;omega

/-- When each pair of nonempty rows is equal or disjoint, a node has
at most one outgoing and one incoming incidence involving a block centre. -/
theorem one_block (A : Colored n)
    (classes : ∀i j, row A i=row A j ∨ Disjoint (row A i) (row A j)) (i : Fin n) :
    (∀ b c, arc A (.inl i) (.inr b)=true → arc A (.inl i) (.inr c)=true → b=c) ∧
    (∀ b c, arc A (.inr b) (.inl i)=true → arc A (.inr c) (.inl i)=true → b=c) := by
  have unique := List.nodup_iff_injective_get.mp (List.nodup_dedup
    (((List.finRange n).map (row A)).filter (· != ∅)))
  constructor
  · intro b c hb hc;exact unique ((of_decide_eq_true hb).symm.trans (of_decide_eq_true hc))
  · intro b c hb hc
    obtain ⟨_,x,hx⟩ := (block_mem A _).mp (List.get_mem (blocks A) b)
    obtain ⟨_,y,hy⟩ := (block_mem A _).mp (List.get_mem (blocks A) c)
    rcases classes x y with eq|away
    · exact unique (hx.symm.trans (eq.trans hy))
    · exact False.elim ((Finset.disjoint_left.mp away) (hx ▸ of_decide_eq_true hb) (hy ▸ of_decide_eq_true hc))

/-- Dense component rows of an actual face prefix are equivalence blocks. -/
private theorem prefix_rectangular {s : QuotientDP.State n} (run : QuotientDP.FullRun bound target fs U s)
    (a b j k : QuotientDP.Side n) (aj : s.blocks a j) (bj : s.blocks b j) (ak : s.blocks a k) : s.blocks b k := by
  have blk := FullBlocks.blocks_exact run
  obtain ⟨_,_,x,y,hx,hy,xy⟩ := (blk a j).mp aj
  obtain ⟨op,_,u,v,hu,hv,uv⟩ := (blk b j).mp bj
  obtain ⟨_,kp,t,z,ht,hz,tz⟩ := (blk a k).mp ak
  have symm (x y) (h : FullBlocks.Dual fs x y) : FullBlocks.Dual fs y x := by
    obtain ⟨ne,e,xx,yy⟩:=(FullBlocks.dual_iff ..).mp h
    exact (FullBlocks.dual_iff ..).mpr ⟨ne.symm,e,yy,xx⟩
  have join {x y e} (xx : FullBlocks.inc fs x e) (yy : FullBlocks.inc fs y e) :
      PlanarDegrees.Frontier.Walk (FullBlocks.Dual fs) x y := by
    by_cases eq : x=y
    · subst y; exact .refl
    · exact .step .refl ((FullBlocks.dual_iff ..).mpr ⟨eq,e,xx,yy⟩)
  exact (blk b k).mpr ⟨op,kp,u,z,hu,hz,(((uv.trans (join hv hy)).trans (xy.symm symm)).trans (join hx ht)).trans tz⟩

theorem state_row {s : QuotientDP.State n} (i j : Fin (StateIncidence.names s).length) :
    j∈row (StateIncidence.graph s) i ↔ ∃a b, (StateIncidence.names s).get i=.inr a ∧
      (StateIncidence.names s).get j=.inr b ∧ s.blocks a b=true := by
  have cap (x : QuotientDP.Side n) : 2*(s.pending x).toNat+(s.sealed x).toNat<4 := by
    cases s.pending x <;> cases s.sealed x <;> decide
  cases eq : (StateIncidence.names s).get i with
  | inl x => simp [-List.get_eq_getElem,row,low,StateIncidence.graph,eq,StateIncidence.tint]
  | inr a =>
    cases h : (StateIncidence.names s).get j with
    | inl x => simp [-List.get_eq_getElem,row,low,StateIncidence.graph,eq,h,StateIncidence.tint]
    | inr b => simp [-List.get_eq_getElem,row,low,StateIncidence.graph,eq,h,StateIncidence.tint,StateIncidence.arc,cap]

theorem prefix_rows {s : QuotientDP.State n} (run : QuotientDP.FullRun bound target fs U s) :
    let A := StateIncidence.graph (QuotientDP.prune s)
    ∀ i j, row A i=row A j ∨ Disjoint (row A i) (row A j) := by
  let S := QuotientDP.prune s
  let A := StateIncidence.graph S
  have rect (i j u v) (iu : u∈row A i) (ju : u∈row A j) (iv : v∈row A i) : v∈row A j := by
    obtain ⟨a,b,ai,bu,ab⟩ := (state_row i u).mp iu
    obtain ⟨c,b',cj,bu',cb⟩ := (state_row j u).mp ju
    obtain ⟨a',d,ai',dv,ad⟩ := (state_row i v).mp iv
    obtain rfl := Sum.inr.inj (bu.symm.trans bu')
    obtain rfl := Sum.inr.inj (ai.symm.trans ai')
    exact (state_row j v).mpr ⟨c,d,cj,dv,prefix_rectangular run a c b d ab cb ad⟩
  change ∀i j,row A i=row A j ∨ Disjoint (row A i) (row A j)
  intro i j
  by_cases dis : Disjoint (row A i) (row A j)
  · exact Or.inr dis
  · obtain ⟨u,iu,ju⟩ := Finset.not_disjoint_iff.mp dis
    exact Or.inl (Finset.ext fun v => ⟨rect i j u v iu ju,rect j i u v ju iu⟩)

end Recognition.SparseCompare
