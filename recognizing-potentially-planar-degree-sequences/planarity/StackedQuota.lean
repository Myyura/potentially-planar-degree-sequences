import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic.Ring

/-! A stacked triangular disk has a ternary subdivision tree. The explicit
edge list below provides an independent check of all three corner quotas.
Interior names are assigned in preorder to disjoint intervals. -/
namespace Recognition.StackedQuota

inductive Disk where
  | empty
  | split (ab bc ca : Disk)

structure Quota where
  a : Nat
  b : Nat
  c : Nat
  deriving DecidableEq

def merge (p q s : Quota) : Quota :=
  ⟨1 + p.a + s.b, 1 + p.b + q.a, 1 + q.b + s.a⟩

def Disk.size : Disk → Nat
  | .empty => 0
  | .split l m r => 1 + l.size + m.size + r.size

def Disk.quota : Disk → Quota
  | .empty => ⟨0,0,0⟩
  | .split l m r => merge l.quota m.quota r.quota

def Disk.edges : Disk → Nat → Nat → Nat → Nat → List (Nat × Nat)
  | .empty, _, _, _, _ => []
  | .split l m r, a, b, c, u =>
      [(a,u),(b,u),(c,u)] ++ l.edges a b u (u+1) ++
      m.edges b c u (u+1+l.size) ++ r.edges c a u (u+1+l.size+m.size)

private def hit (x y : Nat) : Nat := if x = y then 1 else 0

def incident (es : List (Nat × Nat)) (x : Nat) : Nat :=
  (es.map (fun e => hit x e.1 + hit x e.2)).sum

@[simp] private theorem incident_append (xs ys : List (Nat × Nat)) (x : Nat) :
    incident (xs ++ ys) x = incident xs x + incident ys x := by
  simp [incident]

/-- When a queried vertex lies outside the new names, the only contribution
comes from its occurrences among the boundary corners. -/
theorem outside (t : Disk) (a b c u x : Nat)
    (out : x < u ∨ u+t.size ≤ x) :
    incident (t.edges a b c u) x =
      t.quota.a * hit x a + t.quota.b * hit x b + t.quota.c * hit x c := by
  induction t generalizing a b c u with
  | empty => simp [Disk.edges, Disk.quota, incident]
  | split l m r L M R =>
    simp only [Disk.size] at out
    have xu : x ≠ u := by omega
    simp only [Disk.edges, incident_append, Disk.quota, merge]
    rw [L _ _ _ _ (by omega), M _ _ _ _ (by omega), R _ _ _ _ (by omega)]
    have h : hit x u = 0 := by simp [hit,xu]
    simp [incident,h]
    ring

/-- The degree of every internal vertex in the quota recursion, indexed by
its permanent name (only queried inside the indicated interval). -/
def Disk.internal : Disk → Nat → Nat → Nat
  | .empty, _, _ => 0
  | .split l m r, u, x =>
      if x = u then 3 + l.quota.c + m.quota.c + r.quota.c
      else if x < u+1+l.size then l.internal (u+1) x
      else if x < u+1+l.size+m.size then m.internal (u+1+l.size) x
      else r.internal (u+1+l.size+m.size) x

/-- The recursive degree equals the number of incident ends in the actual
edge list, including every contribution from descendant disks. -/
theorem inside (t : Disk) (a b c u x : Nat) (ha : a<u) (hb : b<u) (hc : c<u)
    (lo : u≤x) (hi : x<u+t.size) :
    incident (t.edges a b c u) x = t.internal u x := by
  induction t generalizing a b c u with
  | empty => simp only [Disk.size, Nat.add_zero] at hi; omega
  | split l m r L M R =>
    simp only [Disk.size] at hi
    have A : hit x a = 0 := by simp [hit,show x≠a by omega]
    have B : hit x b = 0 := by simp [hit,show x≠b by omega]
    have C : hit x c = 0 := by simp [hit,show x≠c by omega]
    simp only [Disk.edges, incident_append, Disk.internal]
    split
    · rename_i h
      have U : hit x u = 1 := by simp [hit,h]
      rw [outside l _ _ _ _ _ (by omega), outside m _ _ _ _ _ (by omega),
          outside r _ _ _ _ _ (by omega)]
      simp [incident,A,B,C,U]
    · rename_i h
      have U : hit x u = 0 := by simp [hit,h]
      split
      · rename_i left
        rw [L _ _ _ _ (by omega) (by omega) (by omega) (by omega) left,
            outside m _ _ _ _ _ (by omega), outside r _ _ _ _ _ (by omega)]
        simp [incident,A,B,C,U]
      · rename_i afterL
        split
        · rename_i mid
          rw [outside l _ _ _ _ _ (by omega),
              M _ _ _ _ (by omega) (by omega) (by omega) (by omega) mid,
              outside r _ _ _ _ _ (by omega)]
          simp [incident,A,B,C,U]
        · rw [outside l _ _ _ _ _ (by omega), outside m _ _ _ _ _ (by omega),
              R _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]
          simp [incident,A,B,C,U]


def Disk.names : Disk → Nat → List Nat
  | .empty, _ => []
  | .split l m r, u => u :: (l.names (u+1) ++
      m.names (u+1+l.size) ++ r.names (u+1+l.size+m.size))

theorem name_bounds (t : Disk) (u x : Nat) (mem : x ∈ t.names u) :
    u ≤ x ∧ x < u + t.size := by
  induction t generalizing u with
  | empty => simp [Disk.names] at mem
  | split l m r L M R =>
    simp only [Disk.names,List.mem_cons,List.mem_append] at mem
    simp only [Disk.size]
    rcases mem with h | ((h | h) | h)
    · omega
    · have := L _ h; omega
    · have := M _ h; omega
    · have := R _ h; omega

def Disk.degrees : Disk → List Nat
  | .empty => []
  | .split l m r => (3 + l.quota.c + m.quota.c + r.quota.c) ::
      (l.degrees ++ m.degrees ++ r.degrees)

theorem internal_profile (t : Disk) (u : Nat) :
    (t.names u).map (t.internal u) = t.degrees := by
  induction t generalizing u with
  | empty => rfl
  | split l m r L M R =>
    simp only [Disk.names, List.map_cons, List.map_append, Disk.degrees]
    have A : (l.names (u+1)).map ((Disk.split l m r).internal u) = l.degrees := by
      rw [← L (u+1)]
      apply List.map_congr_left
      intro x hx
      have := name_bounds l _ _ hx
      simp [Disk.internal,show x≠u by omega,show x<u+1+l.size by omega]
    have B : (m.names (u+1+l.size)).map ((Disk.split l m r).internal u) = m.degrees := by
      rw [← M (u+1+l.size)]
      apply List.map_congr_left
      intro x hx
      have := name_bounds m _ _ hx
      simp [Disk.internal,show x≠u by omega,show ¬x<u+1+l.size by omega,
        show x<u+1+l.size+m.size by omega]
    have C : (r.names (u+1+l.size+m.size)).map ((Disk.split l m r).internal u) = r.degrees := by
      rw [← R (u+1+l.size+m.size)]
      apply List.map_congr_left
      intro x hx
      have := name_bounds r _ _ hx
      simp [Disk.internal,show x≠u by omega,show ¬x<u+1+l.size by omega,
        show ¬x<u+1+l.size+m.size by omega]
    rw [A,B,C]
    simp [Disk.internal]

theorem edge_profile (t : Disk) (a b c u : Nat) (ha : a<u) (hb : b<u) (hc : c<u) :
    (t.names u).map (incident (t.edges a b c u)) = t.degrees := by
  rw [← internal_profile t u]
  apply List.map_congr_left
  intro x mem
  have h := name_bounds _ _ _ mem
  exact inside _ _ _ _ _ _ ha hb hc h.1 h.2

/-- The multiset recurrence admits arbitrary choices of the first degree
and of the partition among the three child disks. -/
inductive Rule : Quota → Multiset Nat → Prop where
  | empty : Rule ⟨0,0,0⟩ 0
  | split {p q s : Quota} {P Q S : Multiset Nat} {k : Nat} :
      Rule p P → Rule q Q → Rule s S → k = 3+p.c+q.c+s.c →
      Rule (merge p q s) (({k} : Multiset Nat) + P + Q + S)

private theorem profile_split (l m r : Disk) :
    ((Disk.split l m r).degrees : Multiset Nat) =
      ({3+l.quota.c+m.quota.c+r.quota.c} : Multiset Nat) +
        (l.degrees : Multiset Nat) + m.degrees + r.degrees := by
  let k := 3+l.quota.c+m.quota.c+r.quota.c
  change ((k :: ((l.degrees ++ m.degrees) ++ r.degrees) : List Nat) : Multiset Nat) =
    (((([k] ++ l.degrees) ++ m.degrees) ++ r.degrees : List Nat) : Multiset Nat)
  simp

theorem rule_iff (x : Quota) (F : Multiset Nat) :
    Rule x F ↔ ∃ t : Disk, t.quota=x ∧ (t.degrees : Multiset Nat)=F := by
  constructor
  · intro h
    induction h with
    | empty => exact ⟨.empty,rfl,rfl⟩
    | split _ _ _ eq L M R =>
      obtain ⟨l,rfl,rfl⟩ := L
      obtain ⟨m,rfl,rfl⟩ := M
      obtain ⟨r,rfl,rfl⟩ := R
      subst_vars
      exact ⟨.split l m r,rfl,profile_split l m r⟩
  · rintro ⟨t,rfl,rfl⟩
    induction t with
    | empty => exact .empty
    | split l m r L M R =>
      rw [profile_split]
      exact Rule.split L M R rfl


/-- The four faces have ordered corners 012, 013, 023, and 123. -/
structure Shell where
  abc : Disk
  abd : Disk
  acd : Disk
  bcd : Disk

def Shell.edges (s : Shell) :=
  [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)] ++
  s.abc.edges 0 1 2 4 ++ s.abd.edges 0 1 3 (4+s.abc.size) ++
  s.acd.edges 0 2 3 (4+s.abc.size+s.abd.size) ++
  s.bcd.edges 1 2 3 (4+s.abc.size+s.abd.size+s.acd.size)

def corners (p q r s : Quota) : List Nat :=
  [3+p.a+q.a+r.a, 3+p.b+q.b+s.a, 3+p.c+r.b+s.b, 3+q.c+r.c+s.c]

def Shell.names (s : Shell) := [0,1,2,3] ++ s.abc.names 4 ++
  s.abd.names (4+s.abc.size) ++ s.acd.names (4+s.abc.size+s.abd.size) ++
  s.bcd.names (4+s.abc.size+s.abd.size+s.acd.size)

def Shell.profile (s : Shell) := corners s.abc.quota s.abd.quota s.acd.quota s.bcd.quota ++
  s.abc.degrees ++ s.abd.degrees ++ s.acd.degrees ++ s.bcd.degrees

private theorem root_degrees (s : Shell) :
    [0,1,2,3].map (incident s.edges) = corners s.abc.quota s.abd.quota s.acd.quota s.bcd.quota := by
  simp only [List.map_cons,List.map_nil,Shell.edges,incident_append,corners,List.cons.injEq]
  repeat' constructor
  all_goals
    repeat' rw [outside (out := Or.inl (by omega))]
    simp [incident,hit]

private theorem abc_degrees (s : Shell) :
    (s.abc.names 4).map (incident s.edges) = s.abc.degrees := by
  rw [← edge_profile s.abc 0 1 2 4 (by omega) (by omega) (by omega)]
  apply List.map_congr_left
  intro x mem
  obtain ⟨lo,hi⟩ := name_bounds s.abc _ _ mem
  simp only [Shell.edges,incident_append]
  rw [outside s.abd _ _ _ _ _ (by omega)]
  rw [outside s.acd _ _ _ _ _ (by omega)]
  rw [outside s.bcd _ _ _ _ _ (by omega)]
  have h0 : x ≠ 0 := by omega
  have h1 : x ≠ 1 := by omega
  have h2 : x ≠ 2 := by omega
  have h3 : x ≠ 3 := by omega
  simp [incident,hit,h0,h1,h2,h3]

private theorem abd_degrees (s : Shell) :
    (s.abd.names (4+s.abc.size)).map (incident s.edges) = s.abd.degrees := by
  rw [← edge_profile s.abd 0 1 3 (4+s.abc.size) (by omega) (by omega) (by omega)]
  apply List.map_congr_left
  intro x mem
  obtain ⟨lo,hi⟩ := name_bounds s.abd _ _ mem
  simp only [Shell.edges,incident_append]
  rw [outside s.abc _ _ _ _ _ (by omega)]
  rw [outside s.acd _ _ _ _ _ (by omega)]
  rw [outside s.bcd _ _ _ _ _ (by omega)]
  have h0 : x ≠ 0 := by omega
  have h1 : x ≠ 1 := by omega
  have h2 : x ≠ 2 := by omega
  have h3 : x ≠ 3 := by omega
  simp [incident,hit,h0,h1,h2,h3]

private theorem acd_degrees (s : Shell) :
    (s.acd.names (4+s.abc.size+s.abd.size)).map (incident s.edges) = s.acd.degrees := by
  rw [← edge_profile s.acd 0 2 3 (4+s.abc.size+s.abd.size) (by omega) (by omega) (by omega)]
  apply List.map_congr_left
  intro x mem
  obtain ⟨lo,hi⟩ := name_bounds s.acd _ _ mem
  simp only [Shell.edges,incident_append]
  rw [outside s.abc _ _ _ _ _ (by omega)]
  rw [outside s.abd _ _ _ _ _ (by omega)]
  rw [outside s.bcd _ _ _ _ _ (by omega)]
  have h0 : x ≠ 0 := by omega
  have h1 : x ≠ 1 := by omega
  have h2 : x ≠ 2 := by omega
  have h3 : x ≠ 3 := by omega
  simp [incident,hit,h0,h1,h2,h3]

private theorem bcd_degrees (s : Shell) :
    (s.bcd.names (4+s.abc.size+s.abd.size+s.acd.size)).map (incident s.edges) = s.bcd.degrees := by
  rw [← edge_profile s.bcd 1 2 3 (4+s.abc.size+s.abd.size+s.acd.size) (by omega) (by omega) (by omega)]
  apply List.map_congr_left
  intro x mem
  obtain ⟨lo,hi⟩ := name_bounds s.bcd _ _ mem
  simp only [Shell.edges,incident_append]
  rw [outside s.abc _ _ _ _ _ (by omega)]
  rw [outside s.abd _ _ _ _ _ (by omega)]
  rw [outside s.acd _ _ _ _ _ (by omega)]
  have h0 : x ≠ 0 := by omega
  have h1 : x ≠ 1 := by omega
  have h2 : x ≠ 2 := by omega
  have h3 : x ≠ 3 := by omega
  simp [incident,hit,h0,h1,h2,h3]


theorem shell_degrees (s : Shell) :
    s.names.map (incident s.edges) = s.profile := by
  simp only [Shell.names,Shell.profile,List.map_append,root_degrees,
    abc_degrees,abd_degrees,acd_degrees,bcd_degrees]

/-- Tetrahedral acceptance for unordered input. Each of the four
recursive tests can choose its own subdivision. -/
def Accepts (d : Multiset Nat) : Prop :=
  ∃ p q r s P Q R S, Rule p P ∧ Rule q Q ∧ Rule r R ∧ Rule s S ∧
    d = (corners p q r s : Multiset Nat) + P + Q + R + S

theorem acceptance_iff (d : Multiset Nat) :
    Accepts d ↔ ∃ s : Shell, d = (s.names.map (incident s.edges) : Multiset Nat) := by
  constructor
  · rintro ⟨p,q,r,s,P,Q,R,S,hp,hq,hr,hs,rfl⟩
    obtain ⟨a,rfl,rfl⟩ := (rule_iff ..).mp hp
    obtain ⟨b,rfl,rfl⟩ := (rule_iff ..).mp hq
    obtain ⟨c,rfl,rfl⟩ := (rule_iff ..).mp hr
    obtain ⟨f,rfl,rfl⟩ := (rule_iff ..).mp hs
    exact ⟨⟨a,b,c,f⟩,by rw [shell_degrees];rfl⟩
  · rintro ⟨s,rfl⟩
    rw [shell_degrees]
    refine ⟨_,_,_,_,_,_,_,_,(rule_iff ..).mpr ⟨s.abc,rfl,rfl⟩,
      (rule_iff ..).mpr ⟨s.abd,rfl,rfl⟩,(rule_iff ..).mpr ⟨s.acd,rfl,rfl⟩,
      (rule_iff ..).mpr ⟨s.bcd,rfl,rfl⟩,rfl⟩

end Recognition.StackedQuota
