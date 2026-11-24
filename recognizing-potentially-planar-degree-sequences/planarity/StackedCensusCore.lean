import CensusEncoding
import StackedHistory
import StackedCensusRows

namespace Recognition.StackedCensus
open CensusEncoding StackedQuota

/-- A directory of explicit finite certificates. Lookup is logarithmic for
the balanced directories of the census. The logical lemmas do not assume
balance or sortedness. -/
inductive Directory (α : Type) where
  | empty
  | node (left : Directory α) (key : Nat) (payload : α) (right : Directory α)

def Directory.find (k : Nat) : Directory α → Option α
  | .empty => none
  | .node l x value r => if k < x then l.find k else if x < k then r.find k else some value

def Directory.every (p : Nat → α → Bool) : Directory α → Bool
  | .empty => true
  | .node l x v r => p x v && l.every p && r.every p

theorem Directory.checked {p : Nat → α → Bool} (t : Directory α) {k v}
    (all : t.every p = true) (hit : t.find k = some v) : p k v = true := by
  induction t with
  | empty => simp [Directory.find] at hit
  | node l x a r hl hr =>
    simp only [Directory.every,Bool.and_eq_true] at all
    simp only [Directory.find] at hit
    split at hit
    · exact hl all.1.2 hit
    · split at hit
      · exact hr all.2 hit
      · have : k=x := by omega
        cases this
        cases hit
        exact all.1.1

def pack (a b c inv : Nat) := a + 16*(b+16*(c+16*inv))
def cornerA (x : Nat) := x % 16
def cornerB (x : Nat) := x / 16 % 16
def cornerC (x : Nat) := x / 256 % 16
def insideCode (x : Nat) := x / 4096

def diskKey (d : Disk) := pack d.quota.a d.quota.b d.quota.c (code d.degrees)
def combine (x y z : Nat) := pack
  (1 + cornerA x + cornerB z) (1 + cornerB x + cornerA y) (1 + cornerB y + cornerA z)
  (16^(3 + cornerC x + cornerC y + cornerC z) + insideCode x + insideCode y + insideCode z)

def assembled (p q r s : Nat) :=
  16^(3+cornerA p+cornerA q+cornerA r) + 16^(3+cornerB p+cornerB q+cornerA s) +
  16^(3+cornerC p+cornerB r+cornerB s) + 16^(3+cornerC q+cornerC r+cornerC s) +
  insideCode p + insideCode q + insideCode r + insideCode s

private theorem quotas (d : Disk) : d.quota.a ≤ d.size ∧ d.quota.b ≤ d.size ∧ d.quota.c ≤ d.size := by
  induction d with
  | empty => simp [Disk.quota,Disk.size]
  | split l m r hl hm hr => simp only [Disk.quota,Disk.size,merge]; omega

private theorem read_key (d : Disk) (small : d.size ≤ 8) :
    cornerA (diskKey d)=d.quota.a ∧ cornerB (diskKey d)=d.quota.b ∧
    cornerC (diskKey d)=d.quota.c ∧ insideCode (diskKey d)=code d.degrees := by
  have := quotas d
  unfold cornerA cornerB cornerC insideCode diskKey pack
  omega

theorem combine_key (l m r : Disk) (a : l.size ≤ 8) (b : m.size ≤ 8) (c : r.size ≤ 8) :
    diskKey (.split l m r) = combine (diskKey l) (diskKey m) (diskKey r) := by
  obtain ⟨la,lb,lc,li⟩ := read_key l a
  obtain ⟨ma,mb,mc,mi⟩ := read_key m b
  obtain ⟨ra,rb,rc,ri⟩ := read_key r c
  rw [combine,la,lb,lc,li,ma,mb,mc,mi,ra,rb,rc,ri]
  simp [diskKey,Disk.quota,merge,Disk.degrees,code,Nat.add_assoc]

theorem shell_key (s : Shell) (a : s.abc.size ≤ 8) (b : s.abd.size ≤ 8)
    (c : s.acd.size ≤ 8) (d : s.bcd.size ≤ 8) : code s.profile =
    assembled (diskKey s.abc) (diskKey s.abd) (diskKey s.acd) (diskKey s.bcd) := by
  obtain ⟨pa,pb,pc,pi⟩ := read_key s.abc a
  obtain ⟨qa,qb,qc,qi⟩ := read_key s.abd b
  obtain ⟨ra,rb,rc,ri⟩ := read_key s.acd c
  obtain ⟨sa,sb,sc,si⟩ := read_key s.bcd d
  rw [assembled,pa,pb,pc,pi,qa,qb,qc,qi,ra,rb,rc,ri,sa,sb,sc,si]
  simp [Shell.profile,corners,code,Nat.add_assoc]

theorem shell_length (s : Shell) :
    s.profile.length = 4 + s.abc.size + s.abd.size + s.acd.size + s.bcd.size := by
  have eq (d : Disk) : d.degrees.length = d.size := by
    induction d with
    | empty => rfl
    | split l m r hl hm hr => simp [Disk.degrees,Disk.size,hl,hm,hr]; omega
  simp [Shell.profile,corners,eq]
  omega

end Recognition.StackedCensus
