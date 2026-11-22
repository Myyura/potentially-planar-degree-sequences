import FiniteRowChecks

/-! Stored interval traces and forbidden-minor certificates in increasing
lexicographic order of the weakly decreasing degree rows. The separate
packed bit column is read from the distributed graph-atlas catalogue. -/
namespace Recognition.FiniteRowChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

def order5 : List Evidence := [
  .yes [0,0,0,0,0],.no,.yes [0,0,0,1,4097],.no,.yes [0,1,1,4097,4097],.no,
  .no,.no,.yes [0,0,2,4097,4097],.no,.yes [2,1,4097,4097,4097],.no,
  .no,.yes [0,2,4098,4097,4097],.no,.yes [0,0,2,4098,4610],.no,.yes [2,2,4162,4097,4097],
  .yes [0,2,2,4162,4610],.no,.yes [2,2,4098,4618,4610],.no,.no,.no,
  .yes [0,3,4097,4097,4097],.no,.no,.no,.no,.yes [3,4098,4097,4097,4097],
  .no,.yes [0,3,4098,4610,4097],.no,.no,.yes [3,2,4162,4610,4097],.no,
  .no,.no,.no,.no,.no,.no,
  .yes [3,4099,4162,4097,4097],.yes [0,3,4099,4162,4610],.no,.yes [3,3,4162,4162,4610],.no,.no,
  .no,.no,.yes [3,4099,4163,4610,4097],.no,.yes [0,3,4099,4163,5123],.no,
  .yes [3,3,4163,4675,4610],.no,.no,.no,.no,.no,
  .yes [4,4097,4097,4097,4097],.no,.no,.no,.no,.no,
  .no,.yes [4,4098,4610,4097,4097],.no,.no,.yes [4,4098,4610,4098,4610],.no,
  .no,.no,.no,.no,.no,.no,
  .no,.yes [4,4099,4162,4610,4097],.no,.no,.no,.no,
  .no,.no,.yes [4,4099,4163,4618,4610],.no,.yes [4,4099,4163,5123,4097],.no,
  .yes [4,4099,4163,4619,5123],.no,.no,.no,.no,.no,
  .no,.no,.no,.no,.yes [4,4100,4162,4162,4610],.no,
  .no,.no,.no,.no,.no,.no,
  .no,.yes [4,4100,4163,4675,4610],.no,.no,.no,.no,
  .no,.no,.no,.no,.no,.no,
  .yes [4,4100,4163,4676,5123],.no,.no,.no,.no,.no]

def atlas5 : Nat := 1329878302168235048400830902549521685

theorem checked5 : audit (candidates 5) order5 atlas5 0=true := by decide +kernel

end Recognition.FiniteRowChecks
