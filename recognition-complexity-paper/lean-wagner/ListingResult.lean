import Listing
import WireCost

/-! Fixed-order enumeration using the executable elementary comparator.
The weighted separator theorem is used solely for completeness. -/
namespace Recognition.ListingResult
open SparseBoundary AlgorithmCost

def enumerate (n : Nat) := Listing.run WireCost.construct n

/-- The program traverses the bounded partition tree in a fixed order;
under the geometric input its list is identical to that of the exhaustive
certificate finder. -/
theorem reference (sep : SeparatorInput.WeightedPlanarSeparator) (n : Nat) :
    (enumerate n).1=Listing.listAll n := by
  unfold enumerate
  rw [Listing.run_eq]
  unfold Listing.listAll Listing.result
  apply congrArg (fun p => (Listing.candidates n).filter p)
  funext ds
  exact Bool.eq_iff_iff.mpr ((WireCost.construct_iff sep ds).trans (Certificate.findRealization_iff ds).symm)

theorem membership (sep : SeparatorInput.WeightedPlanarSeparator) (n : Nat) (ds : List Nat) :
    ds∈(enumerate n).1 ↔ ds.length=n ∧ ds.Pairwise (·≥·) ∧ Planaric ds := by
  rw [reference sep,Listing.listAll_spec]

theorem no_duplicates (n : Nat) : (enumerate n).1.Nodup := by
  unfold enumerate
  rw [Listing.run_eq]
  apply Listing.no_duplicates

theorem population (sep : SeparatorInput.WeightedPlanarSeparator) (k n : Nat) (fits : k*(k+5)≤2*n) :
    2^k≤(enumerate n).1.length := by rw [reference sep]; exact Listing.output_lower k n fits

/-- All candidate tests, accepted or rejected, and the construction of the
complete output list are included in the declared charge. -/
theorem runtime (n : Nat) : Fits n 6000022 (enumerate n).2 := by
  let D := 2^(6000001*(n.sqrt+1))
  have bounded (ds : List Nat) (m : ds∈Listing.candidates n) : (WireCost.construct ds).2≤D := by
    have size := ((Listing.candidates_spec n ds).mp m).1
    simpa only [Fits,size,D] using WireCost.construct_cost ds
  have a : Fits n 35 (32*(n+1)) := (by simp only [pow_one]; omega : 32*(n+1)≤32*(n+2)^1).trans (polynomial n 32 1)
  have b : Fits n 6000001 D := le_rfl
  have c : Fits n 18 (Listing.candidates n).length := Listing.candidate_power n
  have all := (((a.plus b).plus (constant n 4)).prod c).plus (constant n 1)
  exact (Listing.run_cost _ _ _ bounded).trans all

#print axioms membership
#print axioms runtime
#print axioms population
end Recognition.ListingResult
