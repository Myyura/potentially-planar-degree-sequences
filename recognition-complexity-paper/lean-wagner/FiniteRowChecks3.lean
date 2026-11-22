import FiniteRowChecks

/-! Stored interval traces and forbidden-minor certificates in increasing
lexicographic order of the weakly decreasing degree rows. The separate
packed bit column is read from the distributed graph-atlas catalogue. -/
namespace Recognition.FiniteRowChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

def order3 : List Evidence := [
  .yes [0,0,0],.no,.yes [0,1,4097],.no,.no,.no,
  .yes [2,4097,4097],.no,.no,.yes [2,4098,4610]]

def atlas3 : Nat := 581

theorem checked3 : audit (candidates 3) order3 atlas3 0=true := by decide +kernel

end Recognition.FiniteRowChecks
