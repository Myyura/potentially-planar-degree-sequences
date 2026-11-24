import QuotientDP
import Mathlib.Logic.Equiv.Fin.Basic

/-! Interpreting the block and edge fields of a full face run using the
actual dual graph on its face instances. The newest face has index `none`. -/
namespace Recognition.FullBlocks
open PlanarDegrees.Frontier Recognition.QuotientDP

def Index : List (Triangle n) → Type
  | [] => Empty
  | _::fs => Option (Index fs)

def faceAt : (fs : List (Triangle n)) → Index fs → Triangle n
  | [],i => nomatch i
  | a::_,none => a
  | _::fs,some i => faceAt fs i

def inc (fs : List (Triangle n)) (i : Index fs) (e : Side n) : Prop := on (faceAt fs i) e

def contact (fs : List (Triangle n)) (a : Triangle n) (i : Index fs) := ∃ k, inc fs i (side a k)

def Dual : (fs : List (Triangle n)) → Index fs → Index fs → Prop
  | [],i,_ => nomatch i
  | a::fs,i,j => enlarged (Dual fs) (contact fs a) i j

private theorem sym (fs : List (Triangle n)) {i j} (h : Dual fs i j) : Dual fs j i := by
  induction fs with
  | nil => exact nomatch i
  | cons a fs ih =>
    cases i <;> cases j <;> first | exact h | exact ih h

def occurrences (fs : List (Triangle n)) (e : Side n) := (fs.filter (on · e)).length

theorem occ_pos (fs : List (Triangle n)) (e) : 0<occurrences fs e ↔ ∃ i, inc fs i e := by
  induction fs with
  | nil => exact ⟨by simp [occurrences],fun ⟨i,_⟩ => nomatch i⟩
  | cons a fs ih =>
    by_cases h : on a e
    · exact ⟨fun _ => ⟨none,h⟩,fun _ => by simp [occurrences,h]⟩
    · have eq : occurrences (a::fs) e=occurrences fs e := by simp [occurrences,h]
      rw [eq,ih]; constructor
      · rintro ⟨i,hi⟩; exact ⟨some i,hi⟩
      · rintro ⟨i,hi⟩; cases i with
        | none => exact (h hi).elim
        | some i => exact ⟨i,hi⟩

theorem on_swap (a : Triangle n) (e : Side n) : on a e.swap=on a e := by
  apply Bool.eq_iff_iff.mpr; simp only [on,decide_eq_true_eq]
  constructor <;> rintro ⟨k,h|h⟩ <;>
    first | exact ⟨k,.inr (congrArg Prod.swap h)⟩ | exact ⟨k,.inl (congrArg Prod.swap h)⟩

theorem occ_swap (fs : List (Triangle n)) (e : Side n) : occurrences fs e.swap=occurrences fs e := by
  unfold occurrences; simp only [on_swap]

structure Inventory (fs : List (Triangle n)) (s : State n) : Prop where
  cap : ∀ e, occurrences fs e≤2
  open_ : ∀ e, s.pending e=true ↔ occurrences fs e=1
  close : ∀ e, s.sealed e=true ↔ occurrences fs e=2

private def legal (s : State n) (a : Triangle n) := ∀ k,s.sealed (side a k)=false
private theorem legal_of_allowed {s : State n} {a : Triangle n} (g : allowed bound s a) : legal s a :=
  (of_decide_eq_true g).2.2.2.1

private theorem no_seal {s : State n} {a : Triangle n} (g : legal s a)
    (inv : Inventory fs s) {e} (h : on a e) : s.sealed e=false := by
  have guard := g
  obtain ⟨k,h|h⟩ := of_decide_eq_true h
  · exact h ▸ guard k
  · subst e
    apply Bool.eq_false_iff.mpr
    intro shut
    have c := (inv.close _).mp shut
    rw [occ_swap] at c
    have was := (inv.close _).mpr c
    rw [guard] at was; contradiction

private theorem inv_step {bound} {s : State n} (a : Triangle n) (g : allowed bound s a) (h : Inventory fs s) :
    Inventory (a::fs) (fullNext s a) := by
  have per (e) : occurrences (a::fs) e = occurrences fs e + (on a e).toNat := by
    cases t : on a e <;> simp [occurrences,t]
  have local' (e) : occurrences (a::fs) e≤2 ∧
      (opened s a e=true ↔ occurrences (a::fs) e=1) ∧
      ((s.sealed e || (s.pending e && on a e))=true ↔ occurrences (a::fs) e=2) := by
    have cap := h.cap e; have op := h.open_ e; have cl := h.close e
    rw [per]; cases ha : on a e
    · simpa [opened,ha] using And.intro cap (And.intro op cl)
    · have no := no_seal (legal_of_allowed g) h ha
      simp only [no,Bool.false_eq_true,false_iff] at cl
      cases old : s.pending e <;> simp_all [opened]
      omega
  exact ⟨fun e => (local' e).1,fun e => (local' e).2.1,fun e => (local' e).2.2⟩

theorem inventory_exact {bound target fs U} {s : State n} (h : FullRun bound target fs U s) : Inventory fs s := by
  induction h with
  | init => exact ⟨by simp [occurrences],by simp [start,occurrences],by simp [start,occurrences]⟩
  | step prev a _ ok ih =>
    unfold fullAdvance at ok; split at ok <;> rename_i good
    · obtain rfl := Option.some.inj ok; exact inv_step a good ih
    · contradiction

private def linked (fs : List (Triangle n)) (e d : Side n) :=
  ∃ i j : Index fs, inc fs i e ∧ inc fs j d ∧ Walk (Dual fs) i j

def Blocks (fs : List (Triangle n)) (s : State n) : Prop :=
  ∀ e d, s.blocks e d ↔ s.pending e ∧ s.pending d ∧ linked fs e d

private theorem old_open {s : State n} {a : Triangle n} (ok : legal s a)
    (inv : Inventory fs s) {e} {i : Index fs} (hit : inc fs i e) (open_ : opened s a e) :
    s.pending e=true ∧ on a e=false := by
  have pos := (occ_pos fs e).mpr ⟨i,hit⟩
  have cap := inv.cap e
  by_cases new : on a e
  · have no := no_seal ok inv new
    have hc := inv.close e; simp [no] at hc
    have was := (inv.open_ e).mpr (by omega)
    simp [opened,new,was] at open_
  · simpa [opened,new] using open_

private theorem open_at {s : State n} {a : Triangle n} (ok : legal s a)
    (inv : Inventory fs s) {i : Index fs} {k} (hit : inc fs i (side a k)) : s.pending (side a k) := by
  have onIt : on a (side a k) := decide_eq_true ⟨k,Or.inl rfl⟩
  have no := no_seal ok inv onIt
  have cl := inv.close (side a k)
  have pos := (occ_pos fs _).mpr ⟨i,hit⟩
  have cap := inv.cap (side a k)
  apply (inv.open_ _).mpr
  simp [no] at cl; omega

private theorem walk_old {fs : List (Triangle n)} (a : Triangle n) {i j : Index fs} (w : Walk (Dual fs) i j) :
    Walk (Dual (a::fs)) (some i) (some j) := w.map some (fun _ _ z => z)

private theorem walk_merge (fs : List (Triangle n)) (a : Triangle n) (i j : Index (a::fs)) :
    Walk (Dual (a::fs)) i j ↔ merged (Dual fs) (contact fs a) i j :=
  face_component_update (R := Dual fs) (contact fs a) (fun _ _ h => sym fs h) i j

private theorem group_exact {s : State n} {a : Triangle n} (ok : legal s a)
    (inv : Inventory fs s) (blk : Blocks fs s) {e} (open_ : opened s a e) :
    group s a e ↔ ∃ i : Index (a::fs), inc (a::fs) i e ∧ Walk (Dual (a::fs)) i none := by
  constructor
  · intro g; rcases Bool.or_eq_true_iff.mp g with on_|touch
    · exact ⟨none,on_,.refl⟩
    · obtain ⟨k,_,same⟩ := of_decide_eq_true touch
      obtain ⟨_,_,i,j,ie,jk,reach⟩ := (blk _ _).mp same
      exact ⟨some i,ie,(walk_merge fs a _ _).mpr ⟨j,reach,k,jk⟩⟩
  · rintro ⟨i,ie,w⟩; apply Bool.or_eq_true_iff.mpr
    cases i with
    | none => exact .inl ie
    | some i =>
      obtain ⟨j,reach,k,jk⟩ := (walk_merge fs a _ _).mp w
      have pk := open_at ok inv jk
      exact .inr (decide_eq_true ⟨k,pk,(blk _ _).mpr ⟨(old_open ok inv ie open_).1,pk,i,j,ie,jk,reach⟩⟩)

private theorem blocks_step {bound} {s : State n} {a : Triangle n} (ok : allowed bound s a)
    (inv : Inventory fs s) (blk : Blocks fs s) : Blocks (a::fs) (fullNext s a) := by
  intro e d
  change (opened s a e && opened s a d && (s.blocks e d || (group s a e && group s a d)))=true ↔ _
  simp only [Bool.and_eq_true,Bool.or_eq_true]
  change ((opened s a e=true ∧ opened s a d=true) ∧ _) ↔
    opened s a e=true ∧ opened s a d=true ∧ linked (a::fs) e d
  constructor
  · rintro ⟨⟨oe,od⟩,old|⟨ge,gd⟩⟩
    · obtain ⟨_,_,i,j,ie,jd,w⟩ := (blk _ _).mp old
      exact ⟨oe,od,some i,some j,ie,jd,walk_old a w⟩
    · obtain ⟨i,ie,iw⟩ := (group_exact (legal_of_allowed ok) inv blk oe).mp ge
      obtain ⟨j,jd,jw⟩ := (group_exact (legal_of_allowed ok) inv blk od).mp gd
      exact ⟨oe,od,i,j,ie,jd,iw.trans (jw.symm (fun _ _ h => sym _ h))⟩
  · rintro ⟨oe,od,i,j,ie,jd,w⟩
    refine ⟨⟨oe,od⟩,?_⟩
    have via (iw : Walk (Dual (a::fs)) i none) (jw : Walk (Dual (a::fs)) j none) :
        s.blocks e d=true ∨ group s a e=true ∧ group s a d=true :=
      Or.inr ⟨(group_exact (legal_of_allowed ok) inv blk oe).mpr ⟨i,ie,iw⟩,(group_exact (legal_of_allowed ok) inv blk od).mpr ⟨j,jd,jw⟩⟩
    cases i with
    | none => exact via .refl (w.symm (fun _ _ h => sym _ h))
    | some i =>
      cases j with
      | none => exact via w .refl
      | some j =>
        obtain direct|⟨m₁,m₂⟩ := (walk_merge fs a _ _).mp w
        · exact .inl ((blk _ _).mpr ⟨(old_open (legal_of_allowed ok) inv ie oe).1,(old_open (legal_of_allowed ok) inv jd od).1,i,j,ie,jd,direct⟩)
        · exact via ((walk_merge fs a _ _).mpr m₁) ((walk_merge fs a _ _).mpr m₂)

theorem blocks_exact {bound target fs U} {s : State n} (run : FullRun bound target fs U s) : Blocks fs s := by
  induction run with
  | init => intro e d; simp [start]
  | step prev a _ ok ih =>
    unfold fullAdvance at ok; split at ok <;> rename_i good
    · obtain rfl := Option.some.inj ok; exact blocks_step good (inventory_exact prev) ih
    · contradiction

private def Exposed (fs : List (Triangle n)) (s : State n) :=
  ∀ i : Index fs, ∃ e, s.pending e=true ∧ ∃ j : Index fs, inc fs j e ∧ Walk (Dual fs) i j

private theorem connected_new {fs : List (Triangle n)} {a : Triangle n} {i j : Index fs} {e}
    (ie : Walk (Dual fs) i j) (hit : inc fs j e) (inNew : on a e) : Walk (Dual (a::fs)) (some i) none := by
  obtain ⟨k,h|h⟩ := of_decide_eq_true inNew
  · exact (walk_merge fs a _ _).mpr ⟨j,ie,k,h ▸ hit⟩
  · subst e
    change on (faceAt fs j) (side a k).swap=true at hit
    exact (walk_merge fs a _ _).mpr ⟨j,ie,k,(show inc fs j (side a k) by simpa only [inc,on_swap] using hit)⟩

private theorem exposed_step {bound} {s : State n} {a : Triangle n} (good : allowed bound s a)
    (notDone : s.faces+1<bound) (inv : Inventory fs s) (blk : Blocks fs s) (ex : Exposed fs s) :
    Exposed (a::fs) (fullNext s a) := by
  have guard := (of_decide_eq_true good).2.2.2.2.2
  rw [ite_eq_right (by omega : ¬s.faces+1=bound)] at guard
  obtain ⟨e,oe,ge⟩ := guard
  obtain ⟨j,hit,w⟩ := (group_exact (legal_of_allowed good) inv blk oe).mp ge
  have root : Walk (Dual (a::fs)) none j := w.symm (fun _ _ h => sym _ h)
  intro i; cases i with
  | none => exact ⟨e,oe,j,hit,root⟩
  | some i =>
    obtain ⟨d,op,k,kd,reach⟩ := ex i
    by_cases cross : on a d
    · exact ⟨e,oe,j,hit,(connected_new reach kd cross).trans root⟩
    · exact ⟨d,by change opened s a d=true; simp [opened,op,cross],some k,kd,walk_old a reach⟩

private theorem exposed {bound target fs U} {s : State n} (run : FullRun bound target fs U s)
    (proper : s.faces<bound) : Exposed fs s := by
  induction run with
  | init => intro i; exact nomatch i
  | step prev a _ ok ih =>
    unfold fullAdvance at ok; split at ok <;> rename_i good
    · obtain rfl := Option.some.inj ok
      exact exposed_step good proper (inventory_exact prev) (blocks_exact prev) (ih (of_decide_eq_true good).2.2.1)
    · contradiction

/-- Upon closing the final open side, every former face component meets the
last face. As a result the original terminal dual graph is connected. -/
theorem terminal_connected {bound target fs U} {s : State n} (run : FullRun bound target fs U s)
    (accept : finished bound s) (i j : Index fs) : Walk (Dual fs) i j := by
  cases run with
  | init => exact nomatch i
  | @step past U raw last prev a eligible ok =>
    unfold fullAdvance at ok; split at ok <;> rename_i good
    · obtain rfl := Option.some.inj ok
      have done := (of_decide_eq_true accept).2.2.2
      have ex := exposed prev (of_decide_eq_true good).2.2.1
      have all (z : Index (a::past)) : Walk (Dual (a::past)) z none := by
        cases z with
        | none => exact .refl
        | some z =>
          obtain ⟨d,op,k,kd,reach⟩ := ex z
          have off : opened raw a d=false := done d
          have on_ : on a d := by simpa [opened,op] using off
          exact connected_new reach kd on_
      exact (all i).trans ((all j).symm (fun _ _ h => sym _ h))
    · contradiction

/-- The index of a face is its position in the stored face list. -/
def indexEquiv : (fs : List (Triangle n)) → Index fs ≃ Fin fs.length
  | [] => ⟨Empty.elim,Fin.elim0,fun i => Empty.elim i,fun i => Fin.elim0 i⟩
  | _::fs => (Equiv.optionCongr (indexEquiv fs)).trans (finSuccEquiv' 0).symm

theorem faceAt_get (fs : List (Triangle n)) (i : Index fs) :
    faceAt fs i=fs[(indexEquiv fs i).val] := by
  induction fs with
  | nil => exact nomatch i
  | cons a fs ih =>
    cases i with
    | none => rfl
    | some i =>
      change faceAt fs i = (a::fs)[((finSuccEquiv' 0).symm (some ((indexEquiv fs) i))).val]
      rw [finSuccEquiv'_symm_some,Fin.zero_succAbove]; exact ih i

private theorem contact_iff (fs : List (Triangle n)) (a : Triangle n) (j) :
    contact fs a j ↔ ∃ e, on a e=true ∧ inc fs j e := by
  constructor
  · rintro ⟨k,h⟩; exact ⟨side a k,decide_eq_true ⟨k,Or.inl rfl⟩,h⟩
  · rintro ⟨e,ha,hi⟩; obtain ⟨k,eq|eq⟩ := of_decide_eq_true ha
    · exact ⟨k,eq ▸ hi⟩
    · subst e; exact ⟨k,(show inc fs j (side a k) by simpa only [inc,on_swap] using hi)⟩

/-- Actual dual adjacency of two distinct face instances is precisely an
unordered side appearing in both rows. -/
theorem dual_iff (fs : List (Triangle n)) (i j : Index fs) :
    Dual fs i j ↔ i≠j ∧ ∃ e, inc fs i e ∧ inc fs j e := by
  induction fs with
  | nil => exact nomatch i
  | cons a fs ih =>
    cases i with
    | none =>
      cases j with
      | none => exact ⟨False.elim,fun h => h.1 rfl⟩
      | some j => exact ⟨fun h => ⟨(by intro eq; cases eq),(contact_iff fs a j).mp h⟩,fun h => (contact_iff fs a j).mpr h.2⟩
    | some i =>
      cases j with
      | none =>
        constructor
        · intro h; obtain ⟨e,x,y⟩ := (contact_iff fs a i).mp h; exact ⟨(by intro eq; cases eq),e,y,x⟩
        · rintro ⟨_,e,x,y⟩; exact (contact_iff fs a i).mpr ⟨e,y,x⟩
      | some j => exact ⟨fun h => ⟨fun eq => ((ih i j).mp h).1 (Option.some.inj eq),((ih i j).mp h).2⟩,
        fun h => (ih i j).mpr ⟨fun eq => h.1 (congrArg some eq),h.2⟩⟩

end Recognition.FullBlocks

namespace Recognition.FullBlocks
open PlanarDegrees.Frontier Recognition.QuotientDP

private def old (future : List (Triangle n)) {past : List (Triangle n)} (i : Index past) : Index (future++past) :=
  match future with | [] => i | _::rest => some (old rest i)
private def later (past : List (Triangle n)) : (future : List (Triangle n)) → Index future → Index (future++past)
  | _::_,none => none
  | _::rest,some i => some (later past rest i)
  | [],i => nomatch i

private theorem old_inj (future : List (Triangle n)) (past) : Function.Injective (@old n future past) := by
  induction future with
  | nil => exact Function.injective_id
  | cons a fs ih => exact Option.some_injective _ |>.comp ih
private theorem apart (future past : List (Triangle n)) (i : Index future) (j : Index past) : later past future i≠old future j := by
  induction future with
  | nil => exact nomatch i
  | cons a fs ih => cases i with
    | none => intro eq; contradiction
    | some i => intro eq; exact ih i (Option.some.inj eq)
private theorem cases_index (future past : List (Triangle n)) (i : Index (future++past)) :
    (∃ j,old future j=i) ∨ ∃ j,later past future j=i := by
  induction future with
  | nil => exact .inl ⟨i,rfl⟩
  | cons _ fs ih => cases i with
    | none => exact .inr ⟨none,rfl⟩
    | some i => rcases ih i with ⟨k,rfl⟩|⟨k,rfl⟩; exact .inl ⟨k,rfl⟩; exact .inr ⟨some k,rfl⟩
private theorem old_face (future past : List (Triangle n)) (i : Index past) : faceAt (future++past) (old future i)=faceAt past i := by
  induction future with | nil => rfl | cons _ _ ih => exact ih
private theorem later_face (future past : List (Triangle n)) (i : Index future) : faceAt (future++past) (later past future i)=faceAt future i := by
  induction future with | nil => exact nomatch i | cons _ _ ih => cases i with | none => rfl | some i => exact ih i

/-- For every proper prefix in an ordering of a connected, paired face
system, each read component has an edge of multiplicity one in that prefix. -/
theorem crossing {future past : List (Triangle n)} (unread : future≠[])
    (cap : ∀ e, occurrences (future++past) e≤2)
    (conn : ∀ x y, Walk (Dual (future++past)) x y) (i : Index past) :
    ∃ e, occurrences past e=1 ∧ ∃ j : Index past, inc past j e ∧ Walk (Dual past) i j := by
  let component (z : Index (future++past)) := ∃ j : Index past, old future j=z ∧ Walk (Dual past) i j
  have root : component (old future i) := ⟨_,rfl,.refl⟩
  have un : Nonempty (Index future) := by cases future with | nil => contradiction | cons a fs => exact ⟨none⟩
  obtain ⟨k⟩ := un
  have outside : ¬component (later past future k) := fun ⟨_,e,_⟩ => apart future past k _ e.symm
  obtain ⟨x,y,⟨j,rfl,w⟩,out,cross⟩ := connected_cut_has_side conn component root outside
  obtain ⟨diff,e,jhit,yhit⟩ := (dual_iff _ _ _).mp cross
  change on (faceAt _ _) _=true at jhit yhit
  rw [old_face] at jhit
  rcases cases_index future past y with ⟨l,rfl⟩|⟨l,rfl⟩
  · rw [old_face] at yhit
    have ne : j≠l := fun h => diff (congrArg (old future) h)
    exact False.elim (out ⟨l,rfl,w.step ((dual_iff _ _ _).mpr ⟨ne,e,jhit,yhit⟩)⟩)
  · rw [later_face] at yhit
    have pos₁ := (occ_pos past e).mpr ⟨j,jhit⟩
    have pos₂ := (occ_pos future e).mpr ⟨l,yhit⟩
    have total := cap e
    simp only [occurrences,List.filter_append,List.length_append] at total pos₁ pos₂ ⊢
    exact ⟨e,by omega,j,jhit,w⟩

/-- The component-closure guard succeeds on any proper cut of a terminal
connected face sequence; global connectivity and side pairing supply the
boundary side of the newest face's component. -/
theorem component_guard {bound target past U} {s : State n} (run : FullRun bound target past U s)
    (a : Triangle n) (future : List (Triangle n))
    (paired : ∀ e, occurrences (future++a::past) e=0 ∨ occurrences (future++a::past) e=2)
    (conn : ∀ x y, Walk (Dual (future++a::past)) x y)
    (last : s.faces+1=bound ↔ future=[]) :
    (∀ k,s.sealed (side a k)=false) ∧
    (if s.faces+1=bound then ∀ e,opened s a e=false else ∃ e,opened s a e=true ∧ group s a e=true) := by
  have cap (e) : occurrences (future++a::past) e≤2 := by rcases paired e with h|h <;> omega
  have count (e) : occurrences (a::past) e=occurrences past e+(on a e).toNat := by
    cases h : on a e <;> simp [occurrences,h]
  have bound' (e) : occurrences (a::past) e≤2 := by
    have H := cap e; simp only [occurrences,List.filter_append,List.length_append] at H ⊢; omega
  have inv := inventory_exact run
  have legal' : legal s a := by
    intro k; apply Bool.eq_false_iff.mpr; intro old
    have two := (inv.close _).mp old
    have ob : on a (side a k) := decide_eq_true ⟨k,Or.inl rfl⟩
    have h := bound' (side a k); rw [count,ob,two] at h; contradiction
  have opened_iff (e) : opened s a e ↔ occurrences (a::past) e=1 := by
    rw [count]; have p := inv.open_ e
    by_cases on_ : on a e
    · have b := bound' e; rw [count,on_] at b
      cases he : s.pending e <;> simp_all [opened]
      omega
    · simpa [opened,on_] using p
  refine ⟨legal',?_⟩
  split <;> rename_i hf
  · have := last.mp hf; subst future
    intro e; apply Bool.eq_false_iff.mpr; intro yes
    have eq := (opened_iff e).mp yes; rcases paired e with h|h <;> simp at h <;> omega
  · obtain ⟨e,single,j,hit,path⟩ := crossing (mt last.mpr hf) cap conn (none : Index (a::past))
    have op := (opened_iff e).mpr single
    exact ⟨e,op,(group_exact legal' inv (blocks_exact run) op).mpr ⟨j,hit,path.symm (fun _ _ z => sym _ z)⟩⟩

end Recognition.FullBlocks

namespace Recognition.FullBlocks
open PlanarDegrees.Frontier Recognition.QuotientDP

def Link (fs : List (Triangle n)) (x : Name n) (i j : Index fs) : Prop :=
  ∃ e : Side n, (e.1=x ∨ e.2=x) ∧ inc fs i e ∧ inc fs j e

def ConnectedLinks (fs : List (Triangle n)) : Prop := ∀ x (i j : Index fs),
  x∈vertices (faceAt fs i) → x∈vertices (faceAt fs j) → Walk (Link fs x) i j

private theorem walk_cut {R : α → α → Prop} {i j} (h : Walk R i j) (P : α → Prop) (hi : P i) (hj : ¬P j) :
    ∃ u v, P u ∧ ¬P v ∧ R u v := by
  induction h with
  | refl => contradiction
  | @step u v h edge ih => by_cases yes : P u; exact ⟨u,v,yes,hj,edge⟩; exact ih yes

/-- A corner that appears on both sides of a cut meets an open edge. -/
theorem link_crossing {future past : List (Triangle n)} (cap : ∀ e, occurrences (future++past) e≤2)
    (links : ConnectedLinks (future++past)) (x : Name n) (i : Index past) (j : Index future)
    (oldx : x∈vertices (faceAt past i)) (newx : x∈vertices (faceAt future j)) :
    ∃ e : Side n, occurrences past e=1 ∧ (e.1=x ∨ e.2=x) := by
  let P (z : Index (future++past)) := ∃ i : Index past, old future i=z
  have before : P (old future i) := ⟨i,rfl⟩
  have after : ¬P (later past future j) := fun ⟨k,eq⟩ => apart future past j k eq.symm
  have reach := links x (old future i) (later past future j) ((old_face future past i).symm ▸ oldx)
    ((later_face future past j).symm ▸ newx)
  obtain ⟨u,v,⟨k,rfl⟩,out,e,hit,one,two⟩ := walk_cut reach P before after
  rcases cases_index future past v with seen|⟨z,rfl⟩
  · exact (out seen).elim
  · change on (faceAt _ _) _=true at one two
    rw [old_face] at one; rw [later_face] at two
    have op := (occ_pos past e).mpr ⟨k,one⟩
    have later_ := (occ_pos future e).mpr ⟨z,two⟩
    have all := cap e
    simp only [occurrences,List.filter_append,List.length_append] at all op later_ ⊢
    exact ⟨e,by omega,hit⟩

theorem index_of_mem (fs : List (Triangle n)) {a} (h : a∈fs) : ∃ i : Index fs, faceAt fs i=a := by
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem h
  let k : Fin fs.length := ⟨j,hj⟩
  exact ⟨(indexEquiv fs).symm k,(faceAt_get ..).trans (congrArg fs.get ((indexEquiv fs).apply_symm_apply k))⟩

/-- A face of a terminal gluing can use every old corner that it requires:
connected vertex links make that corner live on the cut. -/
theorem corner_eligible {bound target past U} {s : State n} (run : FullRun bound target past U s)
    (a : Triangle n) (future : List (Triangle n)) (present : ∀ x∈U, ∃ b∈past,x∈vertices b)
    (cap : ∀ e,occurrences (future++a::past) e≤2) (links : ConnectedLinks (future++a::past)) :
    ∀ k, a.v k∈U → active s.pending (a.v k) := by
  intro k hu
  obtain ⟨b,mem,hit⟩ := present _ hu
  obtain ⟨i,eq⟩ := index_of_mem past mem
  let future' := future++[a]
  have eql : future'++past=future++a::past := by simp [future']
  have read : a.v k∈vertices (faceAt past i) := eq ▸ hit
  have again : a.v k∈vertices (faceAt future' (old future (past := [a]) none)) := by
    have used : a.v k∈vertices a := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
    exact (old_face future [a] (none : Index [a])).symm ▸ used
  obtain ⟨e,one,l|r⟩ := link_crossing (future := future') (past := past) (eql.symm ▸ cap) (eql.symm ▸ links)
    (a.v k) i (old future (past := [a]) none) read again
  · have yes := ((inventory_exact run).open_ _).mpr one
    exact decide_eq_true ⟨e.2,(show s.pending (a.v k,e.2) from by rw [←l]; exact yes)⟩
  · have yes := ((inventory_exact run).open_ e.swap).mpr ((occ_swap past e).trans one)
    exact decide_eq_true ⟨e.1,(show s.pending (a.v k,e.1) from by rw [←r]; exact yes)⟩

end Recognition.FullBlocks
