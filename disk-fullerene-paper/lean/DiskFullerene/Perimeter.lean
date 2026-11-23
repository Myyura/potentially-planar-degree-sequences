import DiskFullerene.CutCount
import DiskFullerene.ContourVisits

namespace DiskFullerene.Dual

private theorem compare_counts {α} [DecidableEq α] (xs ys : List α)
    (h : ∀ u, xs.count u≤ys.count u) : xs.length≤ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a as ih =>
    have ha := h a
    simp at ha
    have mem : a∈ys := List.count_pos_iff.mp (by omega)
    have bound := ih (ys.erase a) (fun v => by
      have hv := h v
      rw [List.count_cons] at hv
      rw [List.count_erase]
      split at hv <;> simp_all <;> omega)
    rw [List.length_erase_of_mem mem] at bound
    have := List.length_pos_of_mem mem
    simp only [List.length_cons]; omega

/-- The contour can visit each visible core vertex once and each cut
vertex once more. A list of distinct buried vertices can be subtracted
without assuming a block decomposition of the plane graph. -/
theorem perimeter_budget {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    (s : M.hexagons≤6) (buried : List (Face M)) (nd : buried.Nodup)
    (inside : buried⊆diskInterior G) (off : ∀ v∈buried, v∉contourWord G hh hc) :
    contourLength G + buried.length ≤ (diskInterior G).length + (coreCuts G).length := by
  classical
  let W := contourWord G hh hc
  have ni : (diskInterior G).Nodup := (List.nodup_finRange _).filter _
  have nc : (coreCuts G).Nodup := ni.filter _
  have point (v) : (W++buried).count v ≤ (diskInterior G++coreCuts G).count v := by
    simp only [List.count_append,nd.count,ni.count,nc.count]
    by_cases buriedV : v∈buried
    · have notW := off v buriedV
      have zero := List.count_eq_zero.mpr notW
      change W.count v=0 at zero
      simp [zero,buriedV,inside buriedV]
    by_cases inner : v∈diskInterior G
    · have visits := visits_le_two G hh hc s v
      change W.count v≤2 at visits
      by_cases twice : 2≤W.count v
      · obtain ⟨a,b,hi,ha,hb,ea,eb,diff⟩ := cut_of_visits G hh hc twice
        have cut : IsCoreCut G v := ⟨hi,a,b,ha,hb,ea,eb,diff⟩
        have m : v∈coreCuts G := by simp [coreCuts,hi,cut]
        simp [buriedV,inner,m]; omega
      · simp [buriedV,inner]; split <;> omega
    · have no : v∉W := fun wt => inner (contour_inside G hh hc wt).1
      simp [List.count_eq_zero.mpr no,buriedV]
  have total := compare_counts _ _ point
  simpa only [List.length_append,W,contour_card] using total

end DiskFullerene.Dual
