import SparseBoundary.Graph

namespace SparseBoundary.Graph

/-- Check a short minor certificate: five rows encode K5, six encode K3,3. -/
def certificateTest {n : Nat} (G : Graph n) (rows : List (List (Fin n))) : Bool :=
  if rows.length = 5 then G.minorTest clique5 (fun i => rows[i.val]?.getD [])
  else if rows.length = 6 then G.minorTest biclique33 (fun i => rows[i.val]?.getD [])
  else false

theorem certificate_nonplanar {n : Nat} (G : Graph n) (rows : List (List (Fin n)))
    (h : certificateTest G rows) : ¬ G.Planar := by
  intro hp
  unfold certificateTest at h
  split at h
  · exact hp.1 ⟨_,h⟩
  · split at h
    · exact hp.2 ⟨_,h⟩
    · contradiction

end SparseBoundary.Graph
