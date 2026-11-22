import Frontier
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic.DeriveFintype

/-! Anonymous-name face transitions. Edge keys are symmetric pairs, represented
by symmetric Boolean relations. Slots 0, 1, 2 of a proposed triangle retain
its chosen orientation and three proposed first-occurrence colors. -/
namespace Recognition.QuotientDP
open PlanarDegrees.Frontier

abbrev Name (n : Nat) := Fin n
abbrev Side (n : Nat) := Name n × Name n

structure State (n : Nat) where
  pending : Side n → Bool
  sealed : Side n → Bool
  blocks : Side n → Side n → Bool
  current : Name n → Nat
  remaining : Multiset Nat
  used : Nat
  faces : Nat
  deriving DecidableEq

structure Triangle (n : Nat) where
  v : Fin 3 → Name n
  color : Fin 3 → Bool
  deriving DecidableEq, Fintype

def side (a : Triangle n) (k : Fin 3) : Side n := (a.v k,a.v (k+1))
def on (a : Triangle n) (e : Side n) := decide (∃ k, side a k=e ∨ (side a k).swap=e)
def active (edges : Side n → Bool) (v : Name n) := decide (∃ w, edges (v,w)=true)
def opened (s : State n) (a : Triangle n) (e : Side n) := xor (s.pending e) (on a e)
def touching (s : State n) (a : Triangle n) (e : Side n) :=
  decide (∃ k, s.pending (side a k)=true ∧ s.blocks e (side a k)=true)
def group (s : State n) (a : Triangle n) (e : Side n) := on a e || touching s a e
def livePair (p : Side n → Bool) (e : Side n) := active p e.1 && active p e.2
def tally (P : Fin 3 → Bool) := ((List.finRange 3).filter P).length
def fresh (s : State n) (a : Triangle n) := tally (fun j => !(active s.pending (a.v j)))
def contributing (s : State n) (a : Triangle n) (v : Name n) (k : Fin 3) :=
  !(s.pending (side a k)) && a.color k && (a.v k == v || a.v (k+1) == v)
def value (s : State n) (a : Triangle n) (v : Name n) :=
  s.current v + tally (contributing s a v)
def released (s : State n) (a : Triangle n) :=
  (((List.finRange 3).filter (fun k => !(active (opened s a) (a.v k)))).map (fun k => value s a (a.v k)) : Multiset Nat)
def nextState (s : State n) (a : Triangle n) : State n where
  pending := opened s a
  sealed e := livePair (opened s a) e && (s.sealed e || (s.pending e && on a e))
  blocks e f := opened s a e && opened s a f && (s.blocks e f || (group s a e && group s a f))
  current v := if active (opened s a) v then value s a v else 0
  remaining := s.remaining-released s a
  used := s.used+fresh s a
  faces := s.faces+1

def allowed (bound : Nat) (s : State n) (a : Triangle n) : Bool :=
  decide (Function.Injective a.v ∧ s.used+fresh s a≤n ∧ s.faces<bound ∧
    (∀ k, s.sealed (side a k)=false) ∧ released s a≤s.remaining ∧
    (if s.faces+1=bound then ∀ e, opened s a e=false
     else ∃ e, opened s a e=true ∧ group s a e=true))

def advance (bound : Nat) (s : State n) (a : Triangle n) : Option (State n) :=
  if allowed bound s a then some (nextState s a) else none

def finished (bound : Nat) (s : State n) : Bool :=
  decide (s.faces=bound ∧ s.used=n ∧ s.remaining=0 ∧ ∀ e,s.pending e=false)

def start (target : Multiset Nat) : State n := ⟨fun _ => false,fun _ => false,fun _ _ => false,
  fun _ => 0,target,0,0⟩

def edgeMap (p : Equiv.Perm (Name n)) : Side n ≃ Side n := p.prodCongr p
def renameTriangle (p : Equiv.Perm (Name n)) (a : Triangle n) : Triangle n := ⟨p ∘ a.v,a.color⟩

structure Iso (p : Equiv.Perm (Name n)) (s t : State n) : Prop where
  pending : ∀ e, t.pending (edgeMap p e)=s.pending e
  sealed : ∀ e, t.sealed (edgeMap p e)=s.sealed e
  blocks : ∀ e f, t.blocks (edgeMap p e) (edgeMap p f)=s.blocks e f
  value : ∀ v, t.current (p v)=s.current v
  remaining : t.remaining=s.remaining
  used : t.used=s.used
  faces : t.faces=s.faces

def Same (s t : State n) := ∃ p, Iso p s t

private theorem active_map (p : Equiv.Perm (Name n)) {u v : Side n → Bool}
    (eq : ∀ e, v (edgeMap p e)=u e) (x) : active v (p x)=active u x := by
  apply Bool.eq_iff_iff.mpr; simp only [active,decide_eq_true_eq]
  constructor
  · rintro ⟨w,h⟩; obtain ⟨y,rfl⟩ := p.surjective w; exact ⟨y,(eq (x,y)) ▸ h⟩
  · rintro ⟨y,h⟩; exact ⟨p y,(eq (x,y)).symm ▸ h⟩

private theorem side_map (p : Equiv.Perm (Name n)) (a : Triangle n) (k) :
    side (renameTriangle p a) k=edgeMap p (side a k) := rfl
private theorem on_map (p : Equiv.Perm (Name n)) (a : Triangle n) (e) :
    on (renameTriangle p a) (edgeMap p e)=on a e := by
  unfold on
  have sw (d : Side n) : (edgeMap p d).swap=edgeMap p d.swap := rfl
  simp only [side_map,sw,Equiv.apply_eq_iff_eq]

private theorem open_map {p : Equiv.Perm (Name n)} {s t : State n} (h : Iso p s t) (a : Triangle n) (e) :
    opened t (renameTriangle p a) (edgeMap p e)=opened s a e := by simp [opened,h.pending,on_map]
private theorem group_map {p : Equiv.Perm (Name n)} {s t : State n} (h : Iso p s t) (a : Triangle n) (e) :
    group t (renameTriangle p a) (edgeMap p e)=group s a e := by
  simp only [group,on_map,touching,side_map,h.pending,h.blocks]
private theorem fresh_map {p : Equiv.Perm (Name n)} {s t : State n} (h : Iso p s t) (a : Triangle n) :
    fresh t (renameTriangle p a)=fresh s a := by
  simp only [fresh,renameTriangle,Function.comp_apply,active_map p h.pending]
private theorem value_map {p : Equiv.Perm (Name n)} {s t : State n} (h : Iso p s t) (a : Triangle n) (x) :
    value t (renameTriangle p a) (p x)=value s a x := by
  have eq (k) : contributing t (renameTriangle p a) (p x) k=contributing s a x k := by
    change (!t.pending (edgeMap p (side a k)) && a.color k && ((p (a.v k) == p x) || (p (a.v (k+1)) == p x))) = _
    have beq (u v : Name n) : (p u == p v) = (u == v) := by apply Bool.eq_iff_iff.mpr; simp
    simp only [h.pending,beq,contributing]
  simp only [value,h.value,funext eq]
private theorem released_map {p : Equiv.Perm (Name n)} {s t : State n} (h : Iso p s t) (a : Triangle n) :
    released t (renameTriangle p a)=released s a := by
  unfold released
  change (((List.finRange 3).filter (fun k => !(active (opened t (renameTriangle p a)) (p (a.v k))))).map
    (fun k => value t (renameTriangle p a) (p (a.v k))) : Multiset Nat)=_
  simp only [active_map p (open_map h a),value_map h]

private theorem allowed_map {p : Equiv.Perm (Name n)} {s t : State n} (h : Iso p s t)
    (bound) (a : Triangle n) : allowed bound t (renameTriangle p a)=allowed bound s a := by
  have inj : Function.Injective (renameTriangle p a).v ↔ Function.Injective a.v :=
    ⟨fun g x y eq => g (congrArg p eq),fun g => p.injective.comp g⟩
  have all : (∀ e, opened t (renameTriangle p a) e=false) ↔ ∀ e, opened s a e=false := by
    rw [←(edgeMap p).forall_congr_right]; simp only [open_map h]
  have ex : (∃ e, opened t (renameTriangle p a) e=true ∧ group t (renameTriangle p a) e=true) ↔
      ∃ e, opened s a e=true ∧ group s a e=true := by
    rw [←(edgeMap p).exists_congr_right]; simp only [open_map h,group_map h]
  simp only [allowed,inj,h.used,h.faces,fresh_map h,side_map,h.sealed,released_map h,h.remaining,all,ex]

private theorem next_iso {p : Equiv.Perm (Name n)} {s t : State n} (h : Iso p s t)
    (a : Triangle n) : Iso p (nextState s a) (nextState t (renameTriangle p a)) := by
  constructor
  · exact open_map h a
  · intro e
    change (active _ (p e.1) && active _ (p e.2) && _) = _
    simp only [nextState,livePair,active_map p (open_map h a),h.sealed,h.pending,on_map]
  · intro e f; simp only [nextState,open_map h,h.blocks,group_map h]
  · intro x; simp only [nextState,active_map p (open_map h a),value_map h]
  · simp only [nextState,h.remaining,released_map h]
  · simp only [nextState,h.used,fresh_map h]
  · simp only [nextState,h.faces]

/-- Transport an actual successful face update, including the block-closure
and histogram tests, along a permutation of the temporary vertex names. -/
theorem advance_iso {p : Equiv.Perm (Name n)} {s t u : State n} (h : Iso p s t)
    {a : Triangle n} {bound} (ok : advance bound s a=some u) :
    ∃ v, advance bound t (renameTriangle p a)=some v ∧ Iso p u v := by
  unfold advance at ok ⊢
  rw [allowed_map h]
  split at ok
  next yes => simp only [yes,ite_true,Option.some.injEq] at *; exact ⟨_,rfl,ok ▸ next_iso h a⟩
  next no => contradiction

theorem equivalence : Equivalence (@Same n) := by
  constructor
  · intro s; exact ⟨Equiv.refl _,fun _ => rfl,fun _ => rfl,fun _ _ => rfl,fun _ => rfl,rfl,rfl,rfl⟩
  · rintro s t ⟨p,h⟩; refine ⟨p.symm,?_⟩
    have back (e : Side n) : edgeMap p (edgeMap p.symm e)=e := by rcases e with ⟨x,y⟩; simp [edgeMap]
    exact ⟨fun e => by simpa [back] using (h.pending (edgeMap p.symm e)).symm,
      fun e => by simpa [back] using (h.sealed (edgeMap p.symm e)).symm,
      fun e f => by simpa [back] using (h.blocks (edgeMap p.symm e) (edgeMap p.symm f)).symm,
      fun x => by simpa using (h.value (p.symm x)).symm,h.remaining.symm,h.used.symm,h.faces.symm⟩
  · rintro s t u ⟨p,h⟩ ⟨q,j⟩
    exact ⟨p.trans q,⟨fun e => (j.pending _).trans (h.pending e),fun e => (j.sealed _).trans (h.sealed e),
      fun e f => (j.blocks _ _).trans (h.blocks e f),fun x => (j.value _).trans (h.value x),
      j.remaining.trans h.remaining,j.used.trans h.used,j.faces.trans h.faces⟩⟩

/-- Enumerate the ordered corner or color assignments in three slots. -/
private def triple (x y z : α) (i : Fin 3) := if i=0 then x else if i=1 then y else z

def triples (xs : List α) : List (Fin 3 → α) :=
  xs.flatMap fun x => xs.flatMap fun y => xs.map fun z => triple x y z

private theorem triple_mem (xs : List α) (all : ∀ x, x∈xs) (g : Fin 3 → α) : g∈triples xs := by
  unfold triples
  refine List.mem_flatMap.mpr ⟨g 0,all _,List.mem_flatMap.mpr ⟨g 1,all _,List.mem_map.mpr ⟨g 2,all _,?_⟩⟩⟩
  funext k; have cases3 : ∀ k : Fin 3,k=0 ∨ k=1 ∨ k=2 := by decide
  rcases cases3 k with rfl|rfl|rfl <;> simp [triple]

def candidates (n : Nat) : List (Triangle n) := (triples (List.finRange n)).flatMap fun v =>
  (triples [false,true]).map fun color => ⟨v,color⟩

theorem all_candidates (a : Triangle n) : a∈candidates n := by
  rcases a with ⟨v,c⟩
  exact List.mem_flatMap.mpr ⟨v,triple_mem _ List.mem_finRange v,List.mem_map.mpr
    ⟨c,triple_mem _ (fun b => by cases b <;> simp) c,rfl⟩⟩

private theorem flat_constant (xs : List α) (g : α → List β) (k) (length : ∀ x, (g x).length=k) :
    (xs.flatMap g).length=xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [length,ih,Nat.succ_mul,Nat.add_comm]

theorem candidate_count (n : Nat) : (candidates n).length=n^3*8 := by
  have size {α} (xs : List α) : (triples xs).length=xs.length^3 := by
    unfold triples
    rw [flat_constant (k := xs.length*xs.length)]
    · simp [Nat.pow_succ,Nat.mul_assoc]
    · intro x; exact flat_constant _ _ _ (fun _ => by simp)
  unfold candidates
  rw [flat_constant (k := 8),size,List.length_finRange]
  intro x; simp [size]

def successors (bound) (s : State n) := (candidates n).filterMap (advance bound s)

theorem mem_successors {bound} {s t : State n} : t∈successors bound s ↔ ∃ a, advance bound s a=some t := by
  simp [successors,List.mem_filterMap,all_candidates]

theorem table_exact [DecidableRel (@Same n)] (table : List (State n)) (seed) (bound k : Nat) :
    (∀ t ∈ Table.layer Same table (successors bound) seed k,
      ∃ s, Table.Path Same table (successors bound) seed k s ∧ Same s t) ∧
    (∀ s, Table.Path Same table (successors bound) seed k s →
      ∃ t ∈ Table.layer Same table (successors bound) seed k, Same s t) := by
  apply Table.quotient_reachability Same equivalence
  rintro s t u ⟨p,h⟩ step
  obtain ⟨a,ok⟩ := mem_successors.mp step
  obtain ⟨v,ok',eq⟩ := advance_iso h ok
  exact ⟨v,mem_successors.mpr ⟨_,ok'⟩,p,eq⟩

end Recognition.QuotientDP

namespace Recognition.QuotientDP

def liveSet (s : State n) := Finset.univ.filter (fun x => active s.pending x=true)
def slots (s : State n) (a : Triangle n) := Finset.univ.filter (fun k => active s.pending (a.v k)=false)
def vertices (a : Triangle n) := Finset.univ.image a.v

private theorem slots_card (s : State n) (a : Triangle n) : (slots s a).card=fresh s a := by
  let l := (List.finRange 3).filter (fun j => !(active s.pending (a.v j)))
  have eq : slots s a=l.toFinset := by ext j; simp [slots,l]
  have nd : l.Nodup := (List.nodup_finRange _).filter _
  rw [eq,List.toFinset_card_of_nodup nd]; rfl

private theorem allocate (s : State n) (a : Triangle n) (seen : Finset (Name n))
    (seenSize : s.used=seen.card) (seenLive : liveSet s ⊆ seen)
    (inj : Function.Injective a.v) (room : s.used+fresh s a≤n) :
    ∃ p : Equiv.Perm (Name n), (∀ x∈liveSet s,p x=x) ∧
      (∀ k∈slots s a,p (a.v k)∉seen) := by
  classical
  let L := liveSet s
  let F := slots s a
  let free := seenᶜ
  have size : Fintype.card F≤Fintype.card free := by
    simp only [Fintype.card_coe,free,Finset.card_compl,Fintype.card_fin,F,slots_card]
    omega
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le size
  let src : L ⊕ F → Name n := Sum.elim (fun x => x.val) (fun k => a.v k.val)
  let into : L ⊕ F → Name n := Sum.elim (fun x => x.val) (fun k => (g k).val)
  have hi : Function.Injective src := by
    rintro (x|k) (y|l) eq
    · exact congrArg Sum.inl (Subtype.ext eq)
    · have h := x.property; have hh := l.property
      change x.val=a.v l.val at eq
      simp only [L,liveSet,Finset.mem_filter,Finset.mem_univ,true_and,eq] at h
      simp only [F,slots,Finset.mem_filter,Finset.mem_univ,true_and,h] at hh
      contradiction
    · have h := y.property; have hh := k.property
      change a.v k.val=y.val at eq
      simp only [L,liveSet,Finset.mem_filter,Finset.mem_univ,true_and,←eq] at h
      simp only [F,slots,Finset.mem_filter,Finset.mem_univ,true_and,h] at hh
      contradiction
    · exact congrArg Sum.inr (Subtype.ext (inj eq))
  have hj : Function.Injective into := by
    rintro (x|k) (y|l) eq
    · exact congrArg Sum.inl (Subtype.ext eq)
    · change x.val=(g l).val at eq
      exact False.elim (Finset.mem_compl.mp (g l).property (eq ▸ seenLive x.property))
    · change (g k).val=y.val at eq
      exact False.elim (Finset.mem_compl.mp (g k).property (eq.symm ▸ seenLive y.property))
    · exact congrArg Sum.inr (g.injective (Subtype.ext eq))
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair src into hi hj
  exact ⟨p,fun x hx => hp (.inl ⟨x,hx⟩),fun k hk => by
    rw [show p (a.v k)=(g ⟨k,hk⟩).val from hp (.inr ⟨k,hk⟩)]
    exact Finset.mem_compl.mp (g ⟨k,hk⟩).property⟩

/-- All stored coordinates have active endpoints; open pairs are symmetric. -/
private structure Supported (s : State n) : Prop where
  symm : ∀ e, s.pending e=s.pending e.swap
  sealed : ∀ e, s.sealed e → livePair s.pending e
  blocks : ∀ e f, s.blocks e f → s.pending e ∧ s.pending f
  values : ∀ x, s.current x ≠ 0 → active s.pending x

private theorem on_swap (a : Triangle n) (e : Side n) : on a e.swap=on a e := by
  apply Bool.eq_iff_iff.mpr; simp only [on,decide_eq_true_eq]
  constructor <;> rintro ⟨k,h|h⟩
  · exact ⟨k,.inr (congrArg Prod.swap h)⟩
  · exact ⟨k,.inl (congrArg Prod.swap h)⟩
  · exact ⟨k,.inr (congrArg Prod.swap h)⟩
  · exact ⟨k,.inl (congrArg Prod.swap h)⟩

private theorem supported_next {s : State n} (h : Supported s) (a : Triangle n) : Supported (nextState s a) := by
  constructor
  · intro e; simp only [nextState,opened,on_swap,h.symm e]
  · intro e hit; exact (Bool.and_eq_true_iff.mp hit).1
  · intro e f hit; exact Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hit).1
  · intro x ne; by_contra no
    change ¬active (opened s a) x=true at no
    simp [nextState,no] at ne

private theorem fixed_iso {s : State n} (h : Supported s) (p : Equiv.Perm (Name n))
    (fixed : ∀ x∈liveSet s, p x=x) : Iso p s s := by
  have point (x) (hp : active s.pending x) : p x=x := fixed x (by simpa [liveSet] using hp)
  have back (x) (hp : active s.pending (p x)) : p x=x := p.injective (point _ hp)
  have st {e : Side n} (hp : s.pending e) : livePair s.pending e := by
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true ⟨e.2,hp⟩,decide_eq_true ⟨e.1,(h.symm e) ▸ hp⟩⟩
  have localize (P : Side n → Bool) (fit : ∀ e, P e → livePair s.pending e) (e) : P (edgeMap p e)=P e := by
    have forward (y : Side n) (v : livePair s.pending y) : edgeMap p y=y := by
      obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp v; exact Prod.ext (point _ l) (point _ r)
    apply Bool.eq_iff_iff.mpr; constructor
    · intro hit; have eq := (edgeMap p).injective (forward _ (fit _ hit)); exact eq ▸ hit
    · intro hit; rw [forward e (fit e hit)]; exact hit
  have pend := localize s.pending (fun _ hp => st hp)
  have endpoint (e) (hp : s.pending e) : edgeMap p e=e := by
    obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp (st hp); exact Prod.ext (point _ l) (point _ r)
  refine ⟨pend,localize s.sealed h.sealed,?_,?_,rfl,rfl,rfl⟩
  · intro e f; apply Bool.eq_iff_iff.mpr; constructor
    · intro hit; have ⟨a,b⟩ := h.blocks _ _ hit
      rw [pend] at a b; simpa only [endpoint e a,endpoint f b] using hit
    · intro hit; have ⟨a,b⟩ := h.blocks _ _ hit
      simpa only [endpoint e a,endpoint f b] using hit
  · intro x
    by_cases here : active s.pending x
    · rw [point _ here]
    · have no : ¬active s.pending (p x) := fun yes => here (back x yes ▸ yes)
      exact (not_ne_iff.mp (fun nz => no (h.values _ nz))).trans
        (not_ne_iff.mp (fun nz => here (h.values _ nz))).symm

end Recognition.QuotientDP

namespace Recognition.QuotientDP
open PlanarDegrees.Frontier

/-- A permanent run keeps the entire face list and all names ever introduced.
A corner seen earlier can be proposed again only while it is live. -/
inductive Permanent (bound : Nat) (target : Multiset Nat) : List (Triangle n) → Finset (Name n) → State n → Prop
  | init : Permanent bound target [] ∅ (start target)
  | step {past U s t} (h : Permanent bound target past U s) (a : Triangle n)
      (freshness : ∀ k, a.v k ∈ U → active s.pending (a.v k)) (ok : advance bound s a=some t) :
      Permanent bound target (a::past) (U ∪ vertices a) t

theorem next_live (s : State n) (a : Triangle n) (x) (h : active (opened s a) x) :
    active s.pending x ∨ x∈vertices a := by
  obtain ⟨y,hy⟩ := of_decide_eq_true h
  by_cases old : s.pending (x,y)
  · exact Or.inl (decide_eq_true ⟨y,old⟩)
  · have yes : on a (x,y) := by simpa [opened,old] using hy
    obtain ⟨k,e|e⟩ := of_decide_eq_true yes
    · exact Or.inr (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,congrArg Prod.fst e⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨k+1,Finset.mem_univ _,congrArg Prod.fst e⟩)

theorem used_next (s : State n) (U : Finset (Name n)) (a : Triangle n)
    (valid : ∀ k, a.v k∈U → active s.pending (a.v k)) (cover : liveSet s ⊆ U)
    (inj : Function.Injective a.v) (size : s.used=U.card) : (nextState s a).used=(U ∪ vertices a).card := by
  let news := (slots s a).image a.v
  have dis : Disjoint U news := by
    apply Finset.disjoint_left.mpr
    intro x old hn
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hn
    have on := valid _ old
    simp [slots,on] at hk
  have eq : U ∪ vertices a = U ∪ news := by
    ext x; simp only [vertices,news,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,slots,Finset.mem_filter]
    constructor
    · rintro (v|⟨k,rfl⟩)
      · exact Or.inl v
      · by_cases l : active s.pending (a.v k)
        · exact Or.inl (cover (by simpa [liveSet] using l))
        · exact Or.inr ⟨k,by simpa using l,rfl⟩
    · rintro (v|⟨k,_,rfl⟩); exact Or.inl v; exact Or.inr ⟨_,rfl⟩
  rw [eq,Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ inj,slots_card]
  exact congrArg (·+fresh s a) size

private theorem permanent_good {bound target fs U} {s : State n} (p : Permanent bound target fs U s) :
    Supported s ∧ liveSet s ⊆ U ∧ s.used=U.card ∧ s.faces=fs.length := by
  induction p with
  | init =>
    have emp x : ¬active (fun _ : Side n => false) x := by simp [active]
    exact ⟨⟨fun _ => rfl,fun _ no => by contradiction,fun _ _ no => by contradiction,fun _ no => by contradiction⟩,
      by simp [liveSet,start,emp],rfl,rfl⟩
  | @step past U s t prev a fresh ok ih =>
    unfold advance at ok
    split at ok <;> rename_i good
    · obtain rfl := Option.some.inj ok
      refine ⟨supported_next ih.1 a,?_,used_next s U a fresh ih.2.1 (of_decide_eq_true good).1 ih.2.2.1,by simp [nextState,ih.2.2.2]⟩
      intro x hx; have h : active (opened s a) x := (Finset.mem_filter.mp hx).2
      rcases next_live s a x h with yes|yes
      · exact Finset.mem_union_left _ (ih.2.1 (by simpa [liveSet] using yes))
      · exact Finset.mem_union_right _ yes
    · contradiction

/-- Lift each table path to a trace with a consistent permanent name at
every occurrence. The allocator fixes live vertices and maps each new corner
away from every previously used name, including all retired vertices. -/
theorem permanent_witness [DecidableRel (@Same n)] (table : List (State n)) (target : Multiset Nat)
    (bound k : Nat) (t : State n) (inTable : t∈Table.layer Same table (successors bound) (start target) k) :
    ∃ fs U s, Permanent bound target fs U s ∧ fs.length=k ∧ Same s t := by
  obtain ⟨c,path,rel⟩ := (table_exact table (start target) bound k).1 t inTable
  suffices H : ∃ fs U s, Permanent bound target fs U s ∧ fs.length=k ∧ Same c s by
    obtain ⟨fs,U,s,h,len,iso⟩ := H
    exact ⟨fs,U,s,h,len,equivalence.trans (equivalence.symm iso) rel⟩
  clear rel inTable t
  induction path with
  | start => exact ⟨[],∅,_,.init,rfl,equivalence.refl _⟩
  | @step j x y path step _ ih =>
    obtain ⟨fs,U,s,perm,len,⟨p,iso⟩⟩ := ih
    obtain ⟨a,ok⟩ := mem_successors.mp step
    obtain ⟨z,ok',iso'⟩ := advance_iso iso ok
    let b := renameTriangle p a
    have yes : allowed bound s b := by
      unfold advance at ok'; split at ok' <;> first | assumption | contradiction
    obtain ⟨fit,room,_⟩ := of_decide_eq_true yes
    obtain ⟨supported,cover,size,_⟩ := permanent_good perm
    obtain ⟨σ,fixed,unused⟩ := allocate s b U size cover fit room
    have old := fixed_iso supported σ fixed
    obtain ⟨u,ok'',iso''⟩ := advance_iso old ok'
    let c := renameTriangle σ b
    have new (k) (hu : c.v k∈U) : active s.pending (c.v k) := by
      by_cases live : active s.pending (b.v k)
      · change active s.pending (σ (b.v k)); rw [fixed _ (by simpa [liveSet] using live)]; exact live
      · exact False.elim (unused k (by simpa [slots] using live) hu)
    exact ⟨_,_,_,.step perm c new ok'',by simp [len],equivalence.trans ⟨p,iso'⟩ ⟨σ,iso''⟩⟩

end Recognition.QuotientDP

namespace Recognition.QuotientDP
open PlanarDegrees.Frontier

/-- Project the full ledger to the surviving boundary. -/
def prune (s : State n) : State n := {s with
  sealed := fun e => livePair s.pending e && s.sealed e
  current := fun x => if active s.pending x then s.current x else 0 }

/-- Keep every sealed edge and every degree counter on permanent names. -/
def fullNext (s : State n) (a : Triangle n) : State n := {nextState s a with
  sealed := fun e => s.sealed e || (s.pending e && on a e)
  current := value s a }

def fullAdvance (bound : Nat) (s : State n) (a : Triangle n) : Option (State n) :=
  if allowed bound s a then some (fullNext s a) else none

inductive FullRun (bound : Nat) (target : Multiset Nat) : List (Triangle n) → Finset (Name n) → State n → Prop
  | init : FullRun bound target [] ∅ (start target)
  | step {past U s t} (h : FullRun bound target past U s) (a : Triangle n)
      (eligible : ∀ k, a.v k∈U → active s.pending (a.v k)) (ok : fullAdvance bound s a=some t) :
      FullRun bound target (a::past) (U ∪ vertices a) t

private structure Recorded (U : Finset (Name n)) (s : State n) : Prop where
  sealed : ∀ e, s.sealed e → e.1∈U ∧ e.2∈U
  current : ∀ x, s.current x≠0 → x∈U

theorem on_vertices {a : Triangle n} {e : Side n} (h : on a e) : e.1∈vertices a ∧ e.2∈vertices a := by
  obtain ⟨k,eq|eq⟩ := of_decide_eq_true h <;> subst e <;>
    exact ⟨Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩

private theorem recorded_next {U : Finset (Name n)} {s : State n} (h : Recorded U s) (a : Triangle n) :
    Recorded (U ∪ vertices a) (fullNext s a) := by
  constructor
  · intro e he
    rcases Bool.or_eq_true_iff.mp he with old|new
    · exact ⟨Finset.mem_union_left _ (h.sealed _ old).1,Finset.mem_union_left _ (h.sealed _ old).2⟩
    · have h₁ := on_vertices (Bool.and_eq_true_iff.mp new).2
      exact ⟨Finset.mem_union_right _ h₁.1,Finset.mem_union_right _ h₁.2⟩
  · intro x ne
    by_cases here : x∈vertices a
    · exact Finset.mem_union_right _ here
    · apply Finset.mem_union_left _ (h.current x _)
      intro eq; apply ne
      have different (k : Fin 3) : a.v k≠x := fun e => here (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,e⟩)
      have zero (k) : contributing s a x k=false := by simp [contributing,different]
      change value s a x=0; simp [value,tally,eq,funext zero]

private theorem full_step {U : Finset (Name n)} {s : State n} (h : Recorded U s) (a : Triangle n)
    (eligible : ∀ k, a.v k∈U → active s.pending (a.v k)) :
    (allowed bound (prune s) a = allowed bound s a) ∧ nextState (prune s) a=prune (fullNext s a) := by
  have val {v} (ok : active s.pending v ∨ v∈vertices a) : (prune s).current v=s.current v := by
    by_cases was : active s.pending v
    · simp [prune,was]
    · have absent : v∉U := by
        obtain ⟨j,_,eq⟩ := Finset.mem_image.mp (ok.resolve_left was)
        subst v; exact fun hv => was (eligible _ hv)
      have zero : s.current v=0 := not_ne_iff.mp (fun ne => absent (h.current v ne))
      simp [prune,zero]
  have current {x} (ok : active s.pending x ∨ x∈vertices a) : value (prune s) a x=value s a x := by
    exact congrArg (·+tally (contributing s a x)) (val ok)
  have rel : released (prune s) a=released s a := by
    have eq (k) : value (prune s) a (a.v k)=value s a (a.v k) :=
      current (.inr (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩))
    unfold released; rw [funext eq]; rfl
  have stays {x} (ok : active s.pending x ∨ x∈vertices a) (mem : x∈U) : active s.pending x := by
    rcases ok with was|here
    · exact was
    · obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp here; exact eligible _ mem
  have stored (e) (l : active s.pending e.1 ∨ e.1∈vertices a)
      (r : active s.pending e.2 ∨ e.2∈vertices a) : (prune s).sealed e=s.sealed e := by
    by_cases he : s.sealed e
    · have data := h.sealed e he
      simp [prune,livePair,stays l data.1,stays r data.2,he]
    · simp [prune,he]
  have atSide (k) : (prune s).sealed (side a k)=s.sealed (side a k) :=
    stored _ (.inr (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)) (.inr (Finset.mem_image.mpr ⟨k+1,Finset.mem_univ _,rfl⟩))
  refine ⟨?_,?_⟩
  · simp only [allowed,atSide,rel]; rfl
  · have sealedEq (e : Side n) : (nextState (prune s) a).sealed e=(prune (fullNext s a)).sealed e := by
      by_cases live : livePair (opened s a) e
      · obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp live
        have same := stored e (next_live s a _ l) (next_live s a _ r)
        exact congrArg (fun old => livePair (opened s a) e && (old || (s.pending e && on a e))) same
      · change (livePair (opened s a) e && _)=(livePair (opened s a) e && _); simp [live]
    have degEq (x : Name n) : (nextState (prune s) a).current x=(prune (fullNext s a)).current x := by
      change (if active (opened s a) x then value (prune s) a x else 0)=(if active (opened s a) x then value s a x else 0)
      split <;> first | exact current (next_live s a _ (by assumption)) | rfl
    cases s; simp only [nextState,prune,fullNext,State.mk.injEq] at *
    exact ⟨rfl,funext sealedEq,rfl,funext degEq,congrArg (_-·) rel,rfl,trivial⟩

/-- The recovered trace also executes on a full ledger with every historical
edge and full red degrees. Its compact projection is the table boundary. -/
theorem full_witness [DecidableRel (@Same n)] (table : List (State n)) (target : Multiset Nat)
    (bound k : Nat) (t : State n) (hit : t∈Table.layer Same table (successors bound) (start target) k) :
    ∃ fs U s, FullRun bound target fs U s ∧ fs.length=k ∧ Same (prune s) t := by
  obtain ⟨fs,U,s,run,len,iso⟩ := permanent_witness table target bound k t hit
  suffices H : ∃ raw, FullRun bound target fs U raw ∧ Recorded U raw ∧ prune raw=s by
    obtain ⟨raw,h,_,eq⟩ := H; exact ⟨fs,U,raw,h,len,eq ▸ iso⟩
  clear len iso hit t
  induction run with
  | init =>
    exact ⟨_,.init,⟨fun _ no => by contradiction,fun _ no => by contradiction⟩,by simp [prune,start,livePair,active]⟩
  | @step past U s t prev a eligible ok ih =>
    obtain ⟨raw,run,rec,rfl⟩ := ih
    have ⟨valid,eq⟩ := full_step (bound := bound) rec a eligible
    unfold advance at ok; rw [valid] at ok
    split at ok <;> rename_i yes
    · have hraw : fullAdvance bound raw a=some (fullNext raw a) := by simp [fullAdvance,yes]
      exact ⟨_,.step run a eligible hraw,recorded_next rec a,eq.symm.trans (Option.some.inj ok)⟩
    · contradiction

end Recognition.QuotientDP

namespace Recognition.QuotientDP
open PlanarDegrees.Frontier

theorem prune_start (target : Multiset Nat) : prune (n := n) (start target)=start target := by
  simp [prune,start,livePair,active]

theorem finish_iso {p : Equiv.Perm (Name n)} {s t : State n} (h : Iso p s t) (bound) :
    finished bound t=finished bound s := by
  have zero : (∀ e,t.pending e=false) ↔ ∀ e,s.pending e=false := by
    rw [←(edgeMap p).forall_congr_right]; simp only [h.pending]
  simp only [finished,zero,h.used,h.remaining,h.faces]

/-- Completeness for any reference run whose successive representative
classes are covered. Only the concrete prefixes of the requested witness
need coverage. `past` is stored in reverse chronological order. -/
theorem cover_path [DecidableRel (@Same n)] (table : List (State n))
    {target bound fs U} {s : State n} (h : FullRun bound target fs U s)
    (coverage : ∀ tail V raw, tail.IsSuffix fs → FullRun bound target tail V raw → Table.covered Same table (prune raw)) :
    Table.Path Same table (successors bound) (start target) fs.length (prune s) := by
  suffices full : Recorded U s ∧ Table.Path Same table (successors bound) (start target) fs.length (prune s) from full.2
  induction h with
  | init =>
    have cv := coverage [] ∅ (start target) (List.suffix_refl _) .init
    rw [prune_start] at cv ⊢
    exact ⟨⟨fun _ no => by contradiction,fun _ no => by contradiction⟩,.start cv⟩
  | @step past U s t prev a eligible ok ih =>
    obtain ⟨rec,path⟩ := ih (fun tail V raw suffix h => coverage tail V raw
      (suffix.trans (List.suffix_cons ..)) h)
    have cv := coverage _ _ _ (List.suffix_refl _) (.step prev a eligible ok)
    obtain ⟨valid,eq⟩ := full_step (bound := bound) rec a eligible
    unfold fullAdvance at ok; split at ok <;> rename_i good
    · obtain rfl := Option.some.inj ok
      refine ⟨recorded_next rec a,.step path (mem_successors.mpr ⟨a,?_⟩) cv⟩
      simp [advance,valid,good,eq]
    · contradiction

/-- A representative table accepts exactly the same terminal paths as the
full finite-name ledger, provided it covers every viable witness prefix.
No correctness assumption about one-step isomorphism transport is needed. -/
theorem accepts_iff_full [DecidableRel (@Same n)] (table : List (State n))
    (target : Multiset Nat) (bound k : Nat)
    (coverage : ∀ fs U (s : State n), fs.length=k → FullRun bound target fs U s → finished bound s →
      ∀ tail V raw, tail.IsSuffix fs → FullRun bound target tail V raw → Table.covered Same table (prune raw)) :
    (∃ t∈Table.layer Same table (successors bound) (start target) k, finished bound t=true) ↔
    ∃ fs U, ∃ s : State n, FullRun bound target fs U s ∧ fs.length=k ∧ finished bound s=true := by
  constructor
  · rintro ⟨t,hit,accept⟩
    obtain ⟨fs,U,s,run,len,⟨p,iso⟩⟩ := full_witness table target bound k t hit
    exact ⟨fs,U,s,run,len,(finish_iso iso bound) ▸ accept⟩
  · rintro ⟨fs,U,s,run,rfl,finish⟩
    have path := cover_path table run (coverage _ _ _ rfl run finish)
    obtain ⟨t,hit,⟨p,iso⟩⟩ := (table_exact table _ _ _).2 _ path
    exact ⟨t,hit,(finish_iso iso bound).symm ▸ finish⟩

end Recognition.QuotientDP

namespace Recognition.QuotientDP
open PlanarDegrees.Frontier

/-- A single successful face order covered by the table suffices. Other
orders of the same witness may have larger, unrepresented frontiers. -/
theorem accepts_of_one_run [DecidableRel (@Same n)] (table : List (State n))
    {target bound fs U} {s : State n} (run : FullRun bound target fs U s) (terminal : finished bound s)
    (coverage : ∀ tail V raw, tail.IsSuffix fs → FullRun bound target tail V raw → Table.covered Same table (prune raw)) :
    ∃ t∈Table.layer Same table (successors bound) (start target) fs.length, finished bound t=true := by
  obtain ⟨t,member,⟨p,iso⟩⟩ := (table_exact table _ _ _).2 _ (cover_path table run coverage)
  exact ⟨t,member,(finish_iso iso bound).symm ▸ terminal⟩

end Recognition.QuotientDP

namespace Recognition.QuotientDP

private theorem project_full {bound target fs U} {s : State n} (path : FullRun bound target fs U s) :
    Permanent bound target fs U (prune s) ∧ Recorded U s := by
  induction path with
  | init => exact ⟨(by rw [prune_start]; exact Permanent.init),⟨fun _ dead => by contradiction, fun _ dead => by contradiction⟩⟩
  | @step past U s t prev a eligible ok ih =>
    have ⟨valid,projection⟩ := full_step (bound := bound) ih.2 a eligible
    unfold fullAdvance at ok; split at ok <;> rename_i yes
    · obtain rfl := Option.some.inj ok
      exact ⟨.step ih.1 a eligible (by simp [advance,valid,yes,projection]),recorded_next ih.2 a⟩
    · contradiction

/-- Realize a proposed move from any representative on this particular
complete history, fixing its live labels and avoiding all its retired names. -/
theorem lift_successor {bound target past U} {raw rep child : State n}
    (path : FullRun bound target past U raw) (rel : Same (prune raw) rep) (move : child∈successors bound rep) :
    ∃ a t, (∀ k, a.v k∈U → active raw.pending (a.v k)) ∧ fullAdvance bound raw a=some t ∧ Same (prune t) child := by
  obtain ⟨p,h⟩ := equivalence.symm rel
  obtain ⟨input,ok⟩ := mem_successors.mp move
  obtain ⟨z,ok',iso⟩ := advance_iso h ok
  let b := renameTriangle p input
  have yes : allowed bound (prune raw) b := by
    unfold advance at ok'; split at ok' <;> first | assumption | contradiction
  obtain ⟨inj,room,_⟩ := of_decide_eq_true yes
  obtain ⟨perm,recorded⟩ := project_full path
  obtain ⟨supported,cover,size,_⟩ := permanent_good perm
  obtain ⟨σ,fixl,unused⟩ := allocate (prune raw) b U size cover inj room
  obtain ⟨u,ok'',iso'⟩ := advance_iso (fixed_iso supported σ fixl) ok'
  let c := renameTriangle σ b
  have fresh (k) (mem : c.v k∈U) : active raw.pending (c.v k) := by
    by_cases l : active raw.pending (b.v k)
    · change active raw.pending (σ (b.v k)); rw [fixl _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,l⟩)]; exact l
    · exact False.elim (unused k (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by change active raw.pending (b.v k)=false; simpa using l⟩) mem)
  obtain ⟨legal,project⟩ := full_step (bound := bound) recorded c fresh
  change advance bound (prune raw) c=some u at ok''
  unfold advance at ok''; rw [legal] at ok''; split at ok'' <;> rename_i good
  · have hit : fullAdvance bound raw c=some (fullNext raw c) := by simp [fullAdvance,good]
    have eq := project.symm.trans (Option.some.inj ok'')
    exact ⟨c,_,fresh,hit,eq ▸ equivalence.symm (equivalence.trans ⟨p,iso⟩ ⟨σ,iso'⟩)⟩
  · contradiction

end Recognition.QuotientDP
