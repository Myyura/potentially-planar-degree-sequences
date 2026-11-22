import FiniteRowChecks

/-! Stored interval traces and forbidden-minor certificates in increasing
lexicographic order of the weakly decreasing degree rows. The separate
packed bit column is read from the distributed graph-atlas catalogue. -/
namespace Recognition.FiniteRowChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

def order2 : List Evidence := [
  .yes [0,0],.no,.yes [1,4097]]

def atlas2 : Nat := 5

theorem checked2 : audit (candidates 2) order2 atlas2 0=true := by decide +kernel

end Recognition.FiniteRowChecks
