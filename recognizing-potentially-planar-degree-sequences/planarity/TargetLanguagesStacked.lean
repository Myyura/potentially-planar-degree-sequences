import StackedHistory
import ComplexityCost
import Mathlib.Tactic.Linarith

/-! A linear-size bit certificate for the four ordered subdivision trees.
Postfix parsing costs one stack operation per symbol. Once the tree is known,
the verifier counts all quotas and compares the resulting row with the input. -/
namespace Recognition.StackedCertificate
open StackedQuota ComplexityCost

private def code : Disk → List Bool
  | .empty => [false]
  | .split l m r => code r ++ code m ++ code l ++ [true]

private theorem code_length (t : Disk) : (code t).length=3*t.size+1 := by
  induction t <;> simp_all [code,Disk.size]; omega

private theorem degree_count (t : Disk) : t.degrees.length=t.size := by
  induction t <;> simp_all [Disk.degrees,Disk.size]; omega

private def step : Option (List Disk) → Bool → Option (List Disk)
  | none,_ => none
  | some ts,false => some (.empty::ts)
  | some (l::m::r::ts),true => some (.split l m r::ts)
  | _,true => none

private theorem parse_code (t : Disk) (ts : List Disk) :
    (code t).foldl step (some ts)=some (t::ts) := by
  induction t generalizing ts with
  | empty => rfl
  | split l m r L M R => simp [code,List.foldl_append,R,M,L,step]

private def mass (ts : List Disk) := (ts.map Disk.size).sum

private theorem parse_size (bs : List Bool) (ts us : List Disk)
    (ok : bs.foldl step (some ts)=some us) : mass us ≤ mass ts+bs.length := by
  have failed (xs : List Bool) : xs.foldl step none = none := by
    induction xs with
    | nil => rfl
    | cons b bs ih => cases b <;> simpa only [List.foldl_cons,step] using ih
  induction bs generalizing ts with
  | nil => simp at ok; subst us; simp
  | cons b bs ih =>
    rw [List.foldl_cons] at ok
    cases b with
    | false =>
      have h:=ih (.empty::ts) ok
      simp [mass,Disk.size] at h ⊢; omega
    | true =>
      match ts with
      | l::m::r::ss =>
        have h:=ih (.split l m r::ss) ok
        simp [mass,Disk.size] at h ⊢; omega
      | [] | [_] | [_,_] => simp [step,failed] at ok

private abbrev Profile := Quota × List Nat

/-- A bottom-up pass. Each parent copies the two left lists once for the first
append and the resulting prefix once for the second (overcharged harmlessly). -/
private def evaluate : Disk → Meter Profile
  | .empty => ⟨(⟨0,0,0⟩,[]),1⟩
  | .split l m r =>
    let a:=evaluate l
    let b:=evaluate m
    let c:=evaluate r
    let xs:=a.value.2
    let ys:=b.value.2
    let zs:=c.value.2
    ⟨(merge a.value.1 b.value.1 c.value.1,
        (3+a.value.1.c+b.value.1.c+c.value.1.c)::(xs++ys++zs)),
      a.work+b.work+c.work+2*xs.length+2*ys.length+12⟩

private theorem eval_value (t : Disk) : (evaluate t).value=(t.quota,t.degrees) := by
  induction t <;> simp [evaluate,Disk.degrees,Disk.quota, *]

private theorem eval_cost (t : Disk) : (evaluate t).work≤20*t.size^2+20*t.size+1 := by
  induction t with
  | empty => decide
  | split l m r L M R =>
    simp only [evaluate,eval_value,degree_count,Disk.size]
    nlinarith [Nat.zero_le (l.size*m.size),Nat.zero_le (l.size*r.size),Nat.zero_le (m.size*r.size)]

private def profile (s : Shell) : Meter (List Nat) :=
  let a:=evaluate s.abc
  let b:=evaluate s.abd
  let c:=evaluate s.acd
  let d:=evaluate s.bcd
  let ds:=corners a.value.1 b.value.1 c.value.1 d.value.1 ++ a.value.2 ++ b.value.2 ++ c.value.2 ++ d.value.2
  ⟨ds,a.work+b.work+c.work+d.work+4*(a.value.2.length+b.value.2.length+c.value.2.length+5)⟩

private theorem profile_value (s : Shell) : (profile s).value=s.profile := by
  simp [profile,eval_value,Shell.profile]

private def count (s : Shell) := s.abc.size+s.abd.size+s.acd.size+s.bcd.size

private theorem count_spec (s : Shell) : s.profile.length=count s+4 := by
  simp [Shell.profile,corners,degree_count,count]; omega

private theorem profile_cost (s : Shell) :
    (profile s).work ≤ 80*(count s+1)^2 + 20*(count s+1) := by
  have a := eval_cost s.abc; have b := eval_cost s.abd
  have c := eval_cost s.acd; have d := eval_cost s.bcd
  simp only [profile,eval_value,degree_count]
  have bound (i : Nat) (hi : i≤count s) :
      20*i^2+20*i+1≤20*(count s+1)^2 := by
    have H := Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 2; nlinarith
  have ha := bound s.abc.size (by unfold count; omega)
  have hb := bound s.abd.size (by unfold count; omega)
  have hc := bound s.acd.size (by unfold count; omega)
  have hd := bound s.bcd.size (by unfold count; omega)
  unfold count at *; omega

private def compareRows : List Nat → List Nat → Meter Bool
  | [], ys => ⟨ys.isEmpty,1⟩
  | x::xs, ys =>
    if ys.contains x then
      let tail:=compareRows xs (ys.erase x)
      ⟨tail.value,tail.work+2*ys.length+4⟩
    else ⟨false,ys.length+2⟩

private theorem compare_value (xs ys : List Nat) : (compareRows xs ys).value=xs.isPerm ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => by_cases h : x∈ys <;> simp [compareRows,List.isPerm,h,ih]

private theorem compare_cost (xs ys : List Nat) :
    (compareRows xs ys).work≤1+xs.length*(2*ys.length+4) := by
  induction xs generalizing ys with
  | nil => simp [compareRows]
  | cons x xs ih =>
    by_cases h : x∈ys
    · have a:=ih (ys.erase x)
      have small : (ys.erase x).length≤ys.length := List.length_erase_le ..
      have := Nat.mul_le_mul_left xs.length (show 2*(ys.erase x).length+4≤2*ys.length+4 by omega)
      simp only [compareRows,show ys.contains x=true by simpa using h,ite_true,List.length_cons]
      rw [Nat.succ_mul xs.length]; omega
    · simp [compareRows,h,Nat.succ_mul]; omega

def verify (ds : List Nat) (bs : List Bool) : Meter Bool :=
  let parsed := bs.foldl step (some [])
  match parsed with
  | some [a,b,c,d] =>
    let target := profile ⟨a,b,c,d⟩
    let test := compareRows ds target.value
    ⟨test.value,bs.length+1+target.work+test.work+5⟩
  | _ => ⟨false,bs.length+6⟩

theorem certificate (ds : List Nat) : StackedHistory.SequentialRealization (ds : Multiset Nat) ↔
    ∃ bs : List Bool, bs.length≤3*ds.length ∧ (verify ds bs).value=true := by
  rw [←StackedHistory.accepts_iff_sequential,acceptance_iff]
  constructor
  · rintro ⟨s,h⟩
    rw [shell_degrees] at h
    let bs:=code s.bcd ++ code s.acd ++ code s.abd ++ code s.abc
    have perm : ds.Perm s.profile := Quotient.exact h
    refine ⟨bs,?_,?_⟩
    · have n:=perm.length_eq
      simp only [bs,List.length_append,code_length]
      rw [count_spec] at n; unfold count at n; omega
    · simp only [verify,bs,List.foldl_append,parse_code,profile_value,compare_value]
      exact List.isPerm_iff.mpr perm
  · rintro ⟨bs,_,hit⟩
    simp only [verify] at hit; split at hit
    next a b c d ok =>
      let s : Shell := ⟨a,b,c,d⟩
      refine ⟨s,?_⟩
      rw [shell_degrees]
      change (compareRows ds (profile s).value).value=true at hit
      rw [profile_value,compare_value] at hit
      exact Quotient.sound (List.isPerm_iff.mp hit)
    · contradiction

theorem polynomial_verifier (ds : List Nat) (bs : List Bool) :
    (verify ds bs).work≤120*(ds.length+bs.length+5)^2 := by
  simp only [verify]
  split
  next a b c d ok =>
    let s : Shell := ⟨a,b,c,d⟩
    have h:=parse_size bs [] [a,b,c,d] ok
    have len : count s≤bs.length := by simpa [s,count,mass,Nat.add_assoc] using h
    have pf:=profile_cost s
    have cmp:=compare_cost ds (profile s).value
    rw [profile_value,count_spec] at cmp
    change bs.length+1+(profile s).work+(compareRows ds (profile s).value).work+5≤_
    rw [profile_value]
    have small := Nat.pow_le_pow_left (Nat.add_le_add_right len 1) 2
    have prod := Nat.mul_le_mul_left ds.length (show 2*(count s+4)+4≤2*(bs.length+4)+4 by omega)
    nlinarith [Nat.zero_le (ds.length*bs.length)]
  · dsimp; nlinarith [Nat.zero_le (ds.length*bs.length)]

end Recognition.StackedCertificate
