import StackedCensusCore
import Mathlib.Tactic.Eval

namespace Recognition.StackedCensus
open StackedQuota

/-- This generator proposes finite dictionaries and a four-disk witness at
every accepted code. All mathematical uses of this data are checked
independently after elaboration. -/
private def diskLevels (m : Nat) : Array (List (Nat × Disk)) := Id.run do
  let mut lists : Array (List (Nat × Disk)) := #[[(0,.empty)]]
  for n in [:m] do
    let mut out : Std.TreeMap Nat Disk := ∅
    for i in [:n+1] do
      for j in [:n-i+1] do
        for (x,l) in lists[i]! do
          for (y,s) in lists[j]! do
            for (z,r) in lists[n-i-j]! do
              out := out.insert (combine x y z) (.split l s r)
    lists := lists.push out.toList
  return lists

private def shellEntries (m : Nat) : List (Nat × Shell) := Id.run do
  let disks := diskLevels m
  let mut out : Std.TreeMap Nat Shell := ∅
  for i in [:m+1] do
    for j in [:m-i+1] do
      for k in [:m-i-j+1] do
        for (x,p) in disks[i]! do
          for (y,q) in disks[j]! do
            for (z,r) in disks[k]! do
              for (w,s) in disks[m-i-j-k]! do
                out := out.insert (assembled x y z w) ⟨p,q,r,s⟩
  return out.toList

private def balanced : Nat → List (Nat × α) → Directory α
  | 0,_ => .empty
  | k+1, xs =>
    let half := xs.length / 2
    match xs.drop half with
    | [] => .empty
    | (key,v) :: rest => .node (balanced k (xs.take half)) key v (balanced k rest)

private def diskDirectory (n : Nat) := balanced 15 (((diskLevels n)[n]!).map fun p => (p.1,()))
private def shellDirectory (n : Nat) := balanced 15 (shellEntries n)

private meta def quoteDisk : Disk → Lean.Expr
  | .empty => Lean.mkConst ``Disk.empty
  | .split a b c => Lean.mkApp3 (Lean.mkConst ``Disk.split) (quoteDisk a) (quoteDisk b) (quoteDisk c)
private meta instance : Lean.ToExpr Shell where
  toTypeExpr := Lean.mkConst ``Shell
  toExpr s := Lean.mkApp4 (Lean.mkConst ``Shell.mk)
    (quoteDisk s.abc) (quoteDisk s.abd) (quoteDisk s.acd) (quoteDisk s.bcd)

private meta def quoteDirectory [Lean.ToExpr α] : Directory α → Lean.Expr
  | .empty => Lean.mkApp (Lean.mkConst ``Directory.empty) (Lean.toTypeExpr α)
  | .node l k v r => Lean.mkApp5 (Lean.mkConst ``Directory.node) (Lean.toTypeExpr α)
      (quoteDirectory l) (Lean.toExpr k) (Lean.toExpr v) (quoteDirectory r)
private meta instance [Lean.ToExpr α] : Lean.ToExpr (Directory α) where
  toTypeExpr := Lean.mkApp (Lean.mkConst ``Directory) (Lean.toTypeExpr α)
  toExpr := quoteDirectory

set_option maxRecDepth 200000
set_option maxHeartbeats 0

private def d0 : Directory Unit := eval% diskDirectory 0
private def d1 : Directory Unit := eval% diskDirectory 1
private def d2 : Directory Unit := eval% diskDirectory 2
private def d3 : Directory Unit := eval% diskDirectory 3
private def d4 : Directory Unit := eval% diskDirectory 4
private def d5 : Directory Unit := eval% diskDirectory 5
private def d6 : Directory Unit := eval% diskDirectory 6
private def d7 : Directory Unit := eval% diskDirectory 7
private def d8 : Directory Unit := eval% diskDirectory 8
private def s0 : Directory Shell := eval% shellDirectory 0
private def s1 : Directory Shell := eval% shellDirectory 1
private def s2 : Directory Shell := eval% shellDirectory 2
private def s3 : Directory Shell := eval% shellDirectory 3
private def s4 : Directory Shell := eval% shellDirectory 4
private def s5 : Directory Shell := eval% shellDirectory 5
private def s6 : Directory Shell := eval% shellDirectory 6
private def s7 : Directory Shell := eval% shellDirectory 7
private def s8 : Directory Shell := eval% shellDirectory 8

def diskDir : Nat → Directory Unit
  | 0 => d0
  | 1 => d1
  | 2 => d2
  | 3 => d3
  | 4 => d4
  | 5 => d5
  | 6 => d6
  | 7 => d7
  | 8 => d8
  | _ => .empty

def shellDir : Nat → Directory Shell
  | 0 => s0
  | 1 => s1
  | 2 => s2
  | 3 => s3
  | 4 => s4
  | 5 => s5
  | 6 => s6
  | 7 => s7
  | 8 => s8
  | _ => .empty

end Recognition.StackedCensus
