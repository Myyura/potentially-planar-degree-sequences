import StackedTableShell
import StackedTableBounds

/-! Costs of the disk and shell traversals. List copying, submultiset tests and
canonicalization are charged on their operand sizes. Trie probes visit one node
per bit until the first missing suffix. -/
namespace Recognition.StackedTable
open StackedQuota

private theorem length_flat {α β} (xs : List α) (f : α → List β) (k : Nat)
    (eq : ∀ x∈xs, (f x).length=k) : (xs.flatMap f).length=xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    rw [eq x (by simp),ih (fun z hz => eq z (by simp [hz]))]; omega

theorem proposals_length (xs) : (proposals xs).length=xs.length^3 := by
  unfold proposals
  rw [length_flat xs _ (xs.length*xs.length) (fun x _ => ?_)]
  swap
  · exact length_flat xs _ _ (fun y _ => by simp)
  ring

theorem quotas_length (n) : (quotas n).length=(n+1)^3 := by
  unfold quotas
  rw [length_flat _ _ ((n+1)*(n+1)) (fun x _ => ?_),List.length_range]
  · ring
  · rw [length_flat _ _ (n+1) (fun _ _ => by simp),List.length_range]

theorem table_size (ds : List Nat) (k : Nat) :
    (table ds k).rows.length ≤ profileCount ds*(ds.length+1)^3 := by
  let X := (table ds k).rows
  let B := Finset.range (ds.length+1)
  let encode := fun (x : Record) => (x.profile,x.quota.a,x.quota.b,x.quota.c)
  have inj : Function.Injective encode := by
    rintro ⟨⟨a,b,c⟩,F⟩ ⟨⟨u,v,w⟩,G⟩ eq; simp [encode] at eq ⊢; tauto
  have h := Finset.card_le_card_of_injOn (s := X.toFinset)
    (t := Finset.Iic (ds : Multiset Nat) ×ˢ (B ×ˢ (B ×ˢ B))) encode (by
      intro x hx
      have good := sound (List.mem_toFinset.mp hx : x∈(table ds k).rows)
      have l := quota_bound good.1
      have bound := Multiset.card_le_card good.2
      simp only [Multiset.coe_card] at bound
      change (x.profile,x.quota.a,x.quota.b,x.quota.c) ∈ Finset.Iic (ds : Multiset Nat) ×ˢ (B ×ˢ (B ×ˢ B))
      simp only [B,Finset.mem_product,Finset.mem_Iic,Finset.mem_range]
      exact ⟨good.2,by omega,by omega,by omega⟩) (fun _ _ _ _ eq => inj eq)
  rw [List.toFinset_card_of_nodup (table_valid ds k).1] at h
  simpa only [Finset.card_product,Finset.card_range,profileCount,X,B, pow_succ,pow_zero,one_mul,
    Nat.mul_assoc] using h

def Trie.probe : Trie → List Bool → Bool × Nat
  | .empty, _ => (false,1)
  | .node t _ _, [] => (t,1)
  | .node _ l r, b::bs =>
    let z := (if b then r else l).probe bs
    (z.1,z.2+1)

theorem Trie.probe_spec (t : Trie) (bs : List Bool) :
    (t.probe bs).1=t.get bs ∧ (t.probe bs).2≤bs.length+1 := by
  induction bs generalizing t with
  | nil => cases t <;> simp [Trie.probe,Trie.get]
  | cons b bs ih =>
    cases t with
    | empty => simp [Trie.probe,Trie.get]
    | node v l r =>
      cases b <;> simp [Trie.probe,Trie.get,(ih l).1,(ih r).1,(ih l).2,(ih r).2]

/-- A bound for sorting k entries by comparisons, emitting their unary fields
and the three corner fields. Charging k² comparisons also covers mergesort's
intermediate list copies. Each comparison is charged the unary weight of the
whole profile, which dominates the bit lengths of both operands. -/
def keyCost (x : Record) :=
  (x.profile.card+1)^2*(x.profile.sum+1)+3*((key x).length+1)

/-- Submultiset comparison and truncated difference erase at most |a| entries
from a list of length |b|. We charge |b|+1 cells for every erase, including
failure, and the combined unary weight for comparisons and copies. -/
def eraseCost (a b : Multiset Nat) :=
  (a.card+1)*(b.card+1)*(a.sum+b.sum+2)

def span (x : Record) := x.profile.card+x.profile.sum+x.quota.a+x.quota.b+x.quota.c+1

theorem key_size (x : Record) : (key x).length=span x+2 := by
  have eq := congrArg Multiset.sum (Multiset.sort_eq x.profile (·≤·))
  simp only [Multiset.sum_coe] at eq
  simp only [key,Wire.unary_length,List.sum_cons,List.length_cons,Multiset.length_sort,eq,span]
  omega

/-- The charge includes allocation of the combined profile, even if the guard
fails. For a new key it also pays for all nodes copied by persistent insertion. -/
def place (d : Multiset Nat) (t : Table) (x : Record) : Table × Nat :=
  let construction := 4*span x+eraseCost x.profile d+1
  if x.profile≤d then
    let bs := key x
    let p := t.index.probe bs
    if p.1 then (t,construction+keyCost x+p.2+1)
    else (⟨x::t.rows,t.index.put bs⟩,construction+keyCost x+p.2+bs.length+3)
  else (t,construction)

theorem place_value (d t x) :
    (place d t x).1=if x.profile≤d then insert t x else t := by
  by_cases fit : x.profile ≤ d <;> by_cases hit : t.index.get (key x)=true <;>
    simp [place,insert,fit,hit,(Trie.probe_spec ..).1]

private theorem place_cost (d t x) (n : Nat) (sc : span x≤40*(n+1))
    (sz : d.card≤n) (vol : d.sum≤6*n) :
    (place d t x).2 ≤ 1000000*(n+2)^4 := by
  have f : x.profile.card≤40*(n+1) := by unfold span at sc; omega
  have w : x.profile.sum≤40*(n+1) := by unfold span at sc; omega
  have l : (key x).length≤40*(n+1)+2 := by rw [key_size];omega
  have look := (Trie.probe_spec t.index (key x)).2
  have a : eraseCost x.profile d≤(40*(n+1)+1)*(n+1)*(46*(n+1)+2) := by
    unfold eraseCost; gcongr; omega
  have b : keyCost x≤(40*(n+1)+1)^3+3*(40*(n+1)+3) := by
    unfold keyCost
    rw [pow_succ (40*_+1) 2]
    exact Nat.add_le_add (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.succ_le_succ f) 2) (Nat.succ_le_succ w)) (Nat.mul_le_mul_left 3 (by omega))
  have cap : 4*(40*(n+1))+(40*(n+1)+1)*(n+1)*(46*(n+1)+2)+1+
      ((40*(n+1)+1)^3+3*(40*(n+1)+3))+(40*(n+1)+3)+(40*(n+1)+2)+3 ≤ 1000000*(n+2)^4 := by
    nlinarith [sq_nonneg (n:ℤ),Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4)]
  by_cases fit : x.profile≤d <;> by_cases hit : (t.index.probe (key x)).1=true <;>
    simp [place,fit,hit] <;> omega

def gatherWork (d : Multiset Nat) (t : Table) : List Record → Table × Nat
  | [] => (t,1)
  | x::xs => let (u,c) := place d t x
             let (v,e) := gatherWork d u xs
             (v,e+c+2)

theorem gather_work_spec (d t xs) (n : Nat) (sz : d.card≤n) (vol : d.sum≤6*n)
    (bounded : ∀ x∈xs,span x≤40*(n+1)) :
    (gatherWork d t xs).1=gather d t xs ∧
    (gatherWork d t xs).2≤xs.length*(1000000*(n+2)^4+2)+1 := by
  induction xs generalizing t with
  | nil => simp [gatherWork,gather]
  | cons x xs ih =>
    have tail := ih (place d t x).1 (fun z hz => bounded z (by simp [hz]))
    have cost := place_cost d t x n (bounded x (by simp)) sz vol
    rw [gatherWork,gather]
    change (gatherWork d (place d t x).1 xs).1=_ ∧ (gatherWork d (place d t x).1 xs).2+(place d t x).2+2≤_
    rw [List.length_cons,Nat.succ_mul]
    exact ⟨tail.1.trans (by rw [place_value]),by omega⟩

theorem rule_span {x : Record} (r : Rule x.quota x.profile) :
    x.profile.sum+x.quota.a+x.quota.b+x.quota.c=6*x.profile.card := (budget_rule r).1

theorem proposal_span (ds : List Nat) (k : Nat) {x : Record} (h : x∈proposals (table ds k).rows) :
    span x ≤ 40*(ds.length+1) := by
  obtain ⟨p,hp,q,hq,s,hs,rfl⟩ := (proposals_spec ..).mp h
  have P := sound hp; have Q := sound hq; have S := sound hs
  have a := rule_span P.1; have b := rule_span Q.1; have c := rule_span S.1
  have ps := Multiset.card_le_card P.2; have qs := Multiset.card_le_card Q.2; have ss := Multiset.card_le_card S.2
  simp only [Multiset.coe_card] at ps qs ss
  simp only [span,combine,merge,Multiset.card_add,Multiset.card_singleton,
    Multiset.sum_add,Multiset.sum_singleton]
  omega

end Recognition.StackedTable
