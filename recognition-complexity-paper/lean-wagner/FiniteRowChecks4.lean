import FiniteRowChecks

/-! Stored interval traces and forbidden-minor certificates in increasing
lexicographic order of the weakly decreasing degree rows. The separate
packed bit column is read from the distributed graph-atlas catalogue. -/
namespace Recognition.FiniteRowChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

def order4 : List Evidence := [
  .yes [0,0,0,0],.no,.yes [0,0,1,4097],.no,.yes [1,1,4097,4097],.no,
  .no,.yes [0,2,4097,4097],.no,.no,.no,.yes [2,4098,4097,4097],
  .yes [0,2,4098,4610],.no,.yes [2,2,4162,4610],.no,.no,.no,
  .yes [3,4097,4097,4097],.no,.no,.no,.no,.yes [3,4098,4610,4097],
  .no,.no,.no,.no,.no,.no,
  .yes [3,4099,4162,4610],.no,.no,.no,.yes [3,4099,4163,5123]]

def atlas4 : Nat := 18262284437

theorem checked4 : audit (candidates 4) order4 atlas4 0=true := by decide +kernel

end Recognition.FiniteRowChecks
