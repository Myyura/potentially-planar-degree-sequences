import SparseBoundary.GraphEnumeration

namespace SparseBoundary
namespace Graph

/-- The five branch vertices are 0,...,4. Contract vertex 5 into vertex k. -/
def contractSix (k i : Fin 5) : List (Fin 6) :=
  if i == k then [5, i.castSucc] else [i.castSucc]

def firstProfile : List Nat := [4,4,4,4,4,2]

theorem exceptional_graphic : Graphic firstProfile := by
  refine ⟨⟨4094⟩, ?_⟩
  show ∀ i : Fin 6, degree ⟨4094⟩ i = firstProfile[i]
  decide

private def hasContract (x : BitVec 15) : Bool :=
  (List.finRange 5).any fun k => minorTest (n := 6) ⟨x⟩ clique5 (contractSix k)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem coversFirst :
    (candidates 6 (fun i => firstProfile[i.val]'i.isLt)).all (fun G => hasContract G.bits) := by
  decide +kernel

theorem exceptional_nonplanar : ¬ Planaric firstProfile := by
  rintro ⟨G,hG,hP⟩
  have hm : G ∈ candidates 6 (fun i => firstProfile[i.val]'i.isLt) :=
    candidates_complete G _ hG
  obtain ⟨k, _, hk⟩ := List.any_eq_true.mp (List.all_eq_true.mp coversFirst G hm)
  exact hP.1 ⟨contractSix k, hk⟩

end Graph

end SparseBoundary
