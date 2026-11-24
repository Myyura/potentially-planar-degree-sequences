import Frontier
import Mathlib.Data.Multiset.AddSub
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-! Enumerate multiplicities directly instead of enumerating the subsets of
the input positions. Repeated degrees therefore do not cause duplicate work. -/
namespace Recognition.ResidualTable
open PlanarDegrees.Frontier

def counts (S : Multiset Nat) (k : Nat) : Nat → List Nat
  | 0 => []
  | l+1 => S.count k :: counts S (k+1) l

def unpack (k : Nat) : List Nat → Multiset Nat
  | [] => 0
  | m::ms => Multiset.replicate m k + unpack (k+1) ms

private theorem count_unpack (S : Multiset Nat) (k l j : Nat) :
    (unpack k (counts S k l)).count j = if k≤j ∧ j<k+l then S.count j else 0 := by
  induction l generalizing k with
  | zero => simp [unpack,counts]
  | succ l ih =>
    rw [counts,unpack,Multiset.count_add,ih,Multiset.count_replicate]
    split_ifs <;> simp_all <;> omega

private theorem restored (ds : List Nat) {S : Multiset Nat} (sub : S≤(ds : Multiset Nat)) :
    unpack 0 (counts S 0 (ds.sum+1))=S := by
  ext j
  rw [count_unpack]
  split
  · rfl
  · rename_i out
    apply (Multiset.count_eq_zero.mpr ?_).symm
    intro mem
    have bound (ls : List Nat) (h : j∈ls) : j≤ls.sum := by
      induction ls with
      | nil => contradiction
      | cons a ls ih =>
        rcases List.mem_cons.mp h with rfl|m
        · simp
        · simpa only [List.sum_cons] using (ih m).trans (Nat.le_add_left ..)
    have h := bound ds (Multiset.mem_of_le sub mem)
    omega

private theorem covered {S T : Multiset Nat} (smaller : S≤T) (k l : Nat) :
    counts S k l∈residuals (counts T k l) := by
  induction l generalizing k with
  | zero => simp [counts,residuals]
  | succ l ih =>
    simpa [counts,residuals] using And.intro (Nat.lt_succ_of_le (Multiset.count_le_of_le k smaller)) (ih (k+1))

private theorem smaller {ms v : List Nat} (k : Nat) (m : v∈residuals ms) : unpack k v ≤ unpack k ms := by
  induction ms generalizing v k with
  | nil => simp [residuals] at m; subst v; rfl
  | cons a tail ih =>
    obtain ⟨c,when,vs,sm,rfl⟩ := by simpa [residuals,List.mem_flatMap] using m
    exact add_le_add ((Multiset.replicate_le_replicate k).mpr (by omega)) (ih (k+1) sm)

private theorem unpack_sum (k) (ms : List Nat) : (unpack k ms).sum=mass k ms := by
  induction ms generalizing k with
  | nil => simp [unpack,mass]
  | cons m ms ih => simp [unpack,mass,ih,Nat.mul_comm]

def table (ds : List Nat) : List (Multiset Nat) :=
  (residuals (counts (ds : Multiset Nat) 0 (ds.sum+1))).map (unpack 0)

theorem mem_table (ds : List Nat) (r : Multiset Nat) : r∈table ds ↔ r≤(ds : Multiset Nat) := by
  constructor
  · intro h; obtain ⟨v,hv,rfl⟩:=List.mem_map.mp h
    simpa only [restored ds (le_refl _)] using smaller 0 hv
  · intro h; exact List.mem_map.mpr ⟨_,covered h _ _,restored ds h⟩

theorem table_bound (ds : List Nat) :
    (table ds).length ≤ (ds.length+1)*2^(4*(ds.sum.sqrt+1)) := by
  let S := (ds : Multiset Nat)
  have h := residual_histogram_bound (S.count 0) (counts S 1 ds.sum)
  have sum : mass 1 (counts S 1 ds.sum)=ds.sum := by
    have size := unpack_sum 0 (counts S 0 (ds.sum+1))
    rw [restored ds (le_refl S)] at size
    simpa [counts,mass,S] using size.symm
  have zero : S.count 0≤ds.length := Multiset.count_le_card _ _
  simpa [table,counts,sum,S] using h.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right zero 1))

end Recognition.ResidualTable
