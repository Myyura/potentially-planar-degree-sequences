import DiskFullerene.ContourVisits
import DiskFullerene.SixOpen
import DiskFullerene.CutCount

namespace DiskFullerene.Dual
open EndEuler EndLabels Separation

/-- List and mask versions of the open and closed components at an actual
cut vertex differ in cardinality by the single attachment vertex. -/
theorem Branch.arm_size {M} {G : IsDiskFullerene M h} (hh : 3≤h) (D : Branch G) :
    num (arm G D.root D.seed) = D.members.length+1 := by
  classical
  have perm : ((List.finRange _).filter (arm G D.root D.seed)).Perm (D.root::D.members) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _)
      (List.nodup_cons.mpr ⟨D.out hh,((List.nodup_finRange _).filter _).filter _⟩)).mpr
    intro t; simp [in_arm,D.mem_iff]
  simpa [num,List.countP_eq_length_filter] using perm.length_eq

structure ArmWheel {M} (G : IsDiskFullerene M h) (D : Branch G) where
  center : Face M
  inside : center∈D.members
  degree : (dualRow G center).length=5
  closed : ∀ f∈dualRow G center, arm G D.root D.seed f=true
  allFaces : ∀ f, arm G D.root D.seed f=true ↔ f=center ∨ f∈dualRow G center
  rim : ∀ i k : Fin M.faces[center.val].length, i<k →
    (atSide G center k ∈ dualRow G (atSide G center i) ↔ k.val=i.val+1 ∨ (i.val=0 ∧ k.val=4))

/-- The center of a six-vertex arm lies in its open component as long
as there are any interior vertices outside the closed arm. -/
theorem closed_arm_wheel_of_table (table : ∀ L, SixTable.test L=true) {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    (D : Branch G) (small : D.members.length=5) (room : 6<(diskInterior G).length) :
    Nonempty (ArmWheel G D) := by
  let A := arm G D.root D.seed
  have six : num A=6 := by rw [D.arm_size hh,small]
  have d := arm_data G hh hc D.rootIn D.seedIn D.edge
  have conn := arm_complement_connected G hh D.rootIn D.seedIn
  obtain ⟨c,hit,cl⟩ := SixLabels.center_from_table G hh (table _) six d.pole d.nonisolated conn ⟨_,d.single⟩
  have sz : (items A).length=6 := ((List.countP_eq_length_filter ..).symm : (items A).length=num A).trans six
  obtain ⟨degree,occupies,rim⟩ := EndSix.wheel G hh (items A) sz (by simp [A,d.pole]) c (selected.mpr hit)
    (fun _ edge => selected.mpr (cl _ edge)) (SixLabels.outside_walks G conn)
  have notRoot : c≠D.root := by
    intro eq; subst c
    have spread {z} (path : Walk (InteriorAdj G) D.root z) : A z=true := by
      induction path with
      | refl => exact hit
      | @step x y _ edge ih =>
        by_cases equal : x=D.root
        · exact cl y (equal ▸ edge.2.2)
        cases chosen : A y with
        | true => rfl
        | false => exact False.elim (((mem_diskInterior G y).1 edge.2.1).2
            (arm_frontier D.rootIn D.seedIn equal ih chosen edge.2.2))
    have sub : diskInterior G ⊆ items A := fun {z} zI =>
      selected.mpr (spread (interior_connected G hh hc D.rootIn zI))
    have nd : (diskInterior G).Nodup := (List.nodup_finRange _).filter _
    have lo := nd.length_le_of_subset sub
    omega
  have cm := (D.mem_iff c).mpr ((in_arm.mp hit).resolve_left notRoot)
  exact ⟨⟨c,cm,degree,cl,fun f=>selected.symm.trans (occupies f),rim⟩⟩

theorem ArmWheel.absent {M} {G : IsDiskFullerene M h} {D : Branch G} (W : ArmWheel G D)
    (hh : 3≤h) (hc : ¬HasChord G) : W.center∉contourWord G hh hc := by
  intro member
  obtain ⟨_,f,bound,adj⟩ := contour_inside G hh hc member
  exact ((mem_diskInterior G f).1 (arm_stays_inside D.rootIn D.seedIn (W.closed f adj))).2 bound

/-- If at most eleven interior vertices are available, two separated
closed arms both have size six. Their distinct centers are absent from
the entire contour word. -/
theorem eleven_two_buried_of_table (table : ∀ L, SixTable.test L=true) {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    {u : Face M} (cut : IsCoreCut G u) (eleven : (diskInterior G).length≤11) :
    ∃ c d : Face M, c≠d ∧ c∈diskInterior G ∧ d∈diskInterior G ∧
      c∉contourWord G hh hc ∧ d∉contourWord G hh hc := by
  obtain ⟨ui,a,b,ai,bi,av,bv,apart⟩ := cut
  let D : Branch G := ⟨u,a,ui,ai,av⟩
  let E : Branch G := ⟨u,b,ui,bi,bv⟩
  have disj {x} (xd : x∈D.members) : x∉E.members := by
    intro xe
    exact apart (((D.mem_iff _).mp xd).trans (((E.mem_iff _).mp xe).symm (fun _ _ => CoreAvoid.symm G)))
  have nd : (diskInterior G).Nodup := (List.nodup_finRange _).filter _
  have pair := List.nodup_append.mpr (⟨(nd.filter _ : D.members.Nodup), (nd.filter _ : E.members.Nodup),
    fun x hx y hy eq => disj hx (eq ▸ hy)⟩)
  have root : u ∉ D.members++E.members := fun h => (List.mem_append.mp h).elim (D.out hh) (E.out hh)
  have all := List.nodup_cons.mpr ⟨root,pair⟩
  have sub : u::(D.members++E.members)⊆diskInterior G := List.cons_subset.mpr
    ⟨ui,List.append_subset.mpr ⟨fun _ m=>(List.mem_filter.mp m).1, fun _ m=>(List.mem_filter.mp m).1⟩⟩
  have budget := all.length_le_of_subset sub
  simp only [List.length_cons,List.length_append] at budget
  have lowerD := D.five hh hc; have lowerE := E.five hh hc
  obtain ⟨WD⟩ := closed_arm_wheel_of_table table G hh hc D (by omega) (by omega)
  obtain ⟨WE⟩ := closed_arm_wheel_of_table table G hh hc E (by omega) (by omega)
  exact ⟨WD.center,WE.center,fun eq => disj WD.inside (eq ▸ WE.inside),
    (List.mem_filter.mp WD.inside).1,(List.mem_filter.mp WE.inside).1,WD.absent hh hc,WE.absent hh hc⟩

end DiskFullerene.Dual
