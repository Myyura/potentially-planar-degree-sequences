import SparseBoundary.TruncationBuild
import SparseBoundary.GraphPairInsertion

namespace SparseBoundary
open Graph

/-- A single degree-two slot suffices to restore two threes when another
    three is available. The nonadjacent case smooths the slot and then
    truncates the surviving three. -/
theorem restore_three_at_zero {d : List Nat} (hp : Planaric (2::3::d)) :
    Planaric (3::3::3::d) := by
  obtain ⟨G,real,plan⟩ := hp
  let K := G.restrict Fin.succ
  have kp : K.Planar := planar_restrict plan _ (fun _ _ => Fin.succ_inj.mp)
  obtain ⟨a,b,ne,eqn⟩ := degree_two_root (real 0 : G.degree 0=2)
  have eqn' : G=K.parallelPath a b := eqn
  have degrees (i : Fin (3::d).length) : (K.parallelPath a b).degree i.succ=(3::d)[i] := by
    rw [← eqn']; exact real _
  by_cases edge : K.adj a b=true
  · exact pair_from_triangle (g:=3) kp edge (by decide) degrees
  · obtain ⟨H,ph,dh⟩ := smooth_root ne (Bool.eq_false_iff.mpr edge) (eqn' ▸ plan)
    exact Truncation.truncate_profile ⟨H,fun i => (dh i).trans (degrees i),ph⟩

theorem restore_three_mem {r : List Nat} (hp : Planaric (2::r)) (h3 : 3∈r) :
    Planaric (3::3::r) := by
  have pm := List.perm_cons_erase h3
  have p := restore_three_at_zero ((planaric_perm (pm.cons 2)).mp hp)
  exact (planaric_perm ((pm.cons 3).cons 3)).mpr p

end SparseBoundary
