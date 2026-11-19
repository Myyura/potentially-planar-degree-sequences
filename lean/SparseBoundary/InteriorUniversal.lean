import SparseBoundary.InteriorNear
import SparseBoundary.FanSpokes
import SparseBoundary.GraphPetals
import SparseBoundary.GraphDeletion

namespace SparseBoundary

/-- A wheel, extra spokes and triangles at the apex realize every strictly
    sparse leaf-free input with a universal vertex and at least three
    non-apex high vertices. -/
theorem interior_universal (u : List Nat) (t : Nat) (q3 : 3≤u.length)
    (min : ∀ x∈u,3≤x) (sum : u.sum≤3*u.length+t) (even : (u.length+t+u.sum)%2=0) :
    Planaric ((u.length+t)::(List.replicate t 2++u)) := by
  let q:=u.length
  have wheel : Planaric (q::List.replicate q 3) := by
    apply RimGrowth.near_max_interior q (List.replicate q 3)
    · simp [q3,q]
    · simp [q3,q]
    · simp
    · simp
    · simp [List.sum_replicate_nat]; omega
    · simp [List.sum_replicate_nat]; omega
  obtain ⟨G,hp,hd⟩ := (Graph.planaric_on_labels (n:=q+1) (by simp)).mp wheel
  have apex : G.degree 0=q := hd 0
  have rim (i : Fin q) : G.degree i.succ=3 := by simpa using hd i.succ
  obtain ⟨m,vol,h⟩ := Fan.expand_spokes u G hp (Graph.root_universal apex)
    (fun i => (rim i).symm ▸ min _ (List.getElem_mem (n:=i.val) i.isLt))
  simp only [rim,List.map_const',List.length_finRange,List.sum_replicate_nat] at vol
  rw [apex] at h
  have m_le : m≤t := by dsimp [q] at *; omega
  let k := (t-m)/2
  have mk : 2*k+m=t := by dsimp [k,q] at *; omega
  have next := planaric_petals h k
  have eq : List.replicate (2*k) 2++List.replicate m 2=List.replicate t 2 :=
    List.eq_replicate_iff.mpr ⟨by simp;omega,by simp⟩
  rw [←List.append_assoc,eq,show q+m+2*k=u.length+t by dsimp [q];omega] at next
  exact next

end SparseBoundary
