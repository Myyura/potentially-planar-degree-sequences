import StackedHistory
import Wire
import Mathlib.Data.Multiset.Interval
import Mathlib.Data.Multiset.Sort

/-! Reachable disk records, indexed by a binary trie. Each round examines triples of
records from the preceding round. At the shell only three disk profiles are guessed:
the fourth one is obtained by multiset subtraction. -/
namespace Recognition.StackedTable
open StackedQuota

structure Record where
  quota : Quota
  profile : Multiset Nat
  deriving DecidableEq

def key (x : Record) : List Bool :=
  Wire.unary (x.quota.a :: x.quota.b :: x.quota.c :: x.profile.sort (· ≤ ·))

theorem key_inj : Function.Injective key := by
  rintro ⟨⟨a,b,c⟩,F⟩ ⟨⟨u,v,w⟩,G⟩ h
  have eq := congrArg Wire.fields h
  simp only [key, Wire.fields_unary, Option.some.injEq, List.cons.injEq] at eq
  obtain ⟨rfl,rfl,rfl,sort⟩ := eq
  have p := congrArg (fun l : List Nat => (l : Multiset Nat)) sort
  simp only [Multiset.sort_eq] at p
  subst G
  rfl

inductive Trie where
  | empty
  | node (stored : Bool) (zero one : Trie)

def Trie.get : Trie → List Bool → Bool
  | .empty, _ => false
  | .node t _ _, [] => t
  | .node _ l _, false::k => l.get k
  | .node _ _ r, true::k => r.get k

def Trie.put (t : Trie) : List Bool → Trie
  | [] => match t with
    | .empty => .node true .empty .empty
    | .node _ l r => .node true l r
  | b::bs =>
    let (v,l,r) := match t with
      | .empty => (false,Trie.empty,Trie.empty)
      | .node v l r => (v,l,r)
    if b then .node v l (r.put bs) else .node v (l.put bs) r

theorem Trie.get_put (t : Trie) (x y : List Bool) :
    (t.put x).get y = true ↔ y=x ∨ t.get y=true := by
  induction x generalizing t y with
  | nil => cases t <;> cases y with
    | nil => simp [Trie.put,Trie.get]
    | cons b y => cases b <;> simp [Trie.put,Trie.get]
  | cons a x ih =>
    cases t <;> cases a <;> cases y with
    | nil => simp [Trie.put,Trie.get]
    | cons b y => cases b <;> simp [Trie.put,Trie.get,ih]

structure Table where
  rows : List Record
  index : Trie

def Table.Valid (t : Table) := t.rows.Nodup ∧ ∀ x, t.index.get (key x)=true ↔ x∈t.rows

def blank : Table := ⟨[],.empty⟩

def insert (t : Table) (x : Record) : Table :=
  if t.index.get (key x) then t else ⟨x::t.rows,t.index.put (key x)⟩

theorem valid_blank : blank.Valid := ⟨by simp [blank],by simp [blank,Trie.get]⟩

theorem mem_insert {t : Table} (v : t.Valid) (x y : Record) :
    y∈(insert t x).rows ↔ y=x ∨ y∈t.rows := by
  unfold insert
  by_cases h : t.index.get (key x)=true
  · simp only [h,ite_true]
    exact ⟨Or.inr,fun h' => h'.elim (fun e => e ▸ (v.2 x).mp h) id⟩
  · simp [h]

theorem valid_insert {t : Table} (v : t.Valid) (x : Record) : (insert t x).Valid := by
  unfold insert
  split
  · exact v
  next h =>
    refine ⟨List.nodup_cons.mpr ⟨fun m => h ((v.2 x).mpr m),v.1⟩, ?_⟩
    intro y
    simp only [Trie.get_put,List.mem_cons,v.2 y, key_inj.eq_iff]

def combine (x y z : Record) : Record :=
  ⟨merge x.quota y.quota z.quota,
    {3+x.quota.c+y.quota.c+z.quota.c}+x.profile+y.profile+z.profile⟩

def base : Record := ⟨⟨0,0,0⟩,0⟩

def proposals (xs : List Record) : List Record :=
  xs.flatMap fun x => xs.flatMap fun y => xs.map (combine x y)

theorem proposals_spec (xs : List Record) (w) :
    w∈proposals xs ↔ ∃ x∈xs, ∃ y∈xs, ∃ z∈xs, combine x y z=w := by simp [proposals]

def gather (d : Multiset Nat) (t : Table) : List Record → Table
  | [] => t
  | x::xs => gather d (if x.profile≤d then insert t x else t) xs

theorem gather_spec (d : Multiset Nat) (t : Table) (v : t.Valid) (xs : List Record) :
    (gather d t xs).Valid ∧ ∀ y, y∈(gather d t xs).rows ↔ y∈t.rows ∨ (y∈xs ∧ y.profile≤d) := by
  induction xs generalizing t with
  | nil => simp [gather,v]
  | cons x xs ih =>
    by_cases h : x.profile≤d
    · simp only [gather,h,ite_true]
      obtain ⟨ok,mem⟩ := ih _ (valid_insert v x)
      refine ⟨ok,fun y => ?_⟩
      rw [mem,mem_insert v,List.mem_cons]
      constructor
      · rintro ((rfl|m)|m)
        · exact Or.inr ⟨Or.inl rfl,h⟩
        · exact Or.inl m
        · exact Or.inr ⟨Or.inr m.1,m.2⟩
      · rintro (m|⟨rfl|m,l⟩)
        · exact Or.inl (Or.inr m)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨m,l⟩
    · simp only [gather,h,ite_false]
      obtain ⟨ok,mem⟩ := ih _ v
      refine ⟨ok,fun y => ?_⟩
      rw [mem,List.mem_cons]
      aesop

def table (d : Multiset Nat) : Nat → Table
  | 0 => insert blank base
  | k+1 => let t := table d k
           gather d t (proposals t.rows)

theorem table_valid (d : Multiset Nat) (k : Nat) : (table d k).Valid := by
  induction k with
  | zero => exact valid_insert valid_blank base
  | succ k ih => exact (gather_spec _ _ ih _).1

theorem step_mem (d : Multiset Nat) (k : Nat) (x : Record) :
    x∈(table d (k+1)).rows ↔ x∈(table d k).rows ∨
      ((∃ p∈(table d k).rows, ∃ q∈(table d k).rows, ∃ s∈(table d k).rows,
           combine p q s=x) ∧ x.profile≤d) := by
  change x∈(gather d _ _).rows ↔ _
  rw [(gather_spec _ _ (table_valid d k) _).2, proposals_spec]

theorem sound {d k} {x : Record} (hit : x∈(table d k).rows) :
    Rule x.quota x.profile ∧ x.profile≤d := by
  induction k generalizing x with
  | zero =>
    change x∈(insert blank base).rows at hit
    rcases (mem_insert valid_blank _ _).mp hit with rfl|bad
    · exact ⟨.empty,zero_le⟩
    · contradiction
  | succ k ih =>
    rcases (step_mem ..).mp hit with prev|⟨⟨a,ha,b,hb,c,hc,rfl⟩,fit⟩
    · exact ih prev
    · exact ⟨Rule.split (ih ha).1 (ih hb).1 (ih hc).1 rfl,fit⟩

theorem complete {d : Multiset Nat} {x : Quota} {F : Multiset Nat}
    (rule : Rule x F) (fit : F≤d) (k : Nat) (depth : F.card≤k) :
    (⟨x,F⟩ : Record)∈(table d k).rows := by
  induction k generalizing x F with
  | zero =>
    have e : F=0 := Multiset.card_eq_zero.mp (by omega)
    cases rule with
    | empty => exact (mem_insert valid_blank _ _).mpr (Or.inl rfl)
    | split hp hq hs eq => simp at e
  | succ k ih =>
    apply (step_mem ..).mpr
    cases rule with
    | empty => exact Or.inl (ih Rule.empty (zero_le) (by simp))
    | @split p q s P Q S v hp hq hs e =>
      subst v
      simp only [Multiset.card_add,Multiset.card_singleton] at depth
      have lP : P≤{3+p.c+q.c+s.c}+P+Q+S := le_trans (Multiset.le_add_left _ _) ((Multiset.le_add_right _ Q).trans (Multiset.le_add_right _ S))
      have lQ : Q≤{3+p.c+q.c+s.c}+P+Q+S := (Multiset.le_add_left _ _).trans (Multiset.le_add_right _ S)
      exact Or.inr ⟨⟨_,ih hp (lP.trans fit) (by omega),_,ih hq (lQ.trans fit) (by omega),
        _,ih hs ((Multiset.le_add_left _ _).trans fit) (by omega),rfl⟩,fit⟩

theorem quota_bound {x F} (r : Rule x F) :
    x.a ≤ F.card ∧ x.b ≤ F.card ∧ x.c ≤ F.card := by
  induction r with
  | empty => simp
  | split _ _ _ _ l m r =>
    simp only [merge,Multiset.card_add,Multiset.card_singleton]
    omega
end Recognition.StackedTable
