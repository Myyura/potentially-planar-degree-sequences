import FiniteRowChecks

/-! Stored interval traces and forbidden-minor certificates in increasing
lexicographic order of the weakly decreasing degree rows. The separate
packed bit column is read from the distributed graph-atlas catalogue. -/
namespace Recognition.FiniteRowChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

def order1 : List Evidence := [
  .yes [0]]

def atlas1 : Nat := 1

theorem checked1 : audit (candidates 1) order1 atlas1 0=true := by decide +kernel

end Recognition.FiniteRowChecks
