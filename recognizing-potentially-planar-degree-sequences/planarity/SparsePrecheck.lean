import RestrictedProfileResult
import SparseBoundary.LeafLift

/-! Acceptance in the low-sum branch of Appendix A. This branch does not
require ordinary graphicality as an extra hypothesis. -/
namespace Recognition.SparsePrecheck
open SparseBoundary

private theorem twice_le_sum (ds : List Nat) (h : ∀ d∈ds, 2≤d) :
    2*ds.length ≤ ds.sum := by
  induction ds with
  | nil => simp
  | cons a ds ih =>
    have x := h a (.head _)
    have y := ih (fun d m => h d (.tail _ m))
    simp; omega

private theorem raise_first {k : Nat} {rest : List Nat} (old : Planaric (k::rest)) :
    Planaric (1::(k+1)::rest) := by
  have h := planaric_attach_leaf old 0
  rw [List.ofFn_succ] at h
  simpa using h

theorem positive_sparse (ds : List Nat) (pos : ∀ d ∈ ds, 0<d)
    (even : ds.sum%2=0) (sparse : ds.sum+2 ≤ 2*ds.length) : Planaric ds := by
  have leaf : 1∈ds := by
    by_contra absent
    have big := twice_le_sum ds (fun d mem => by
      have := pos d mem
      have : d≠1 := fun eq => absent (eq ▸ mem)
      omega)
    omega
  let tail := ds.erase 1
  have perm : ds.Perm (1::tail) := List.perm_cons_erase leaf
  have size := perm.length_eq
  have total := perm.sum_eq
  simp only [List.length_cons] at size
  simp only [List.sum_cons] at total
  by_cases unit : ∀ d∈tail, d=1
  · have T : tail=List.replicate tail.length 1 := List.eq_replicate_iff.mpr ⟨rfl,unit⟩
    have mass : tail.sum=tail.length := by conv_lhs => rw [T];simp
    apply (planaric_perm perm).mpr
    rw [T]
    exact (RestrictedProfile.one_center_leaves_iff 1 _).mpr ⟨by omega,by omega⟩
  · push Not at unit
    obtain ⟨d,mem,ne⟩ := unit
    have ov := pos d (perm.mem_iff.mpr (.tail _ mem))
    let rest := tail.erase d
    have next : tail.Perm (d::rest) := List.perm_cons_erase mem
    have pair := perm.trans (next.cons 1)
    have len := next.length_eq
    have sum := next.sum_eq
    simp only [List.length_cons] at len
    simp only [List.sum_cons] at sum
    have prior := positive_sparse ((d-1)::rest) (by
        intro x xm
        rcases List.mem_cons.mp xm with rfl | inRest
        · omega
        · exact pos x (pair.mem_iff.mpr (.tail _ (.tail _ inRest))))
      (by simp; omega) (by simp; omega)
    apply (planaric_perm pair).mpr
    simpa [show d-1+1=d by omega] using raise_first prior
termination_by ds.length
decreasing_by
  change rest.length+1 < ds.length
  have a := perm.length_eq
  have b := next.length_eq
  simp only [List.length_cons] at a b
  omega

end Recognition.SparsePrecheck
