import DiskFullerene.CapPerimeter
import DiskFullerene.CanonicalSpine

namespace DiskFullerene.StripFresh
open EndFans EndEuler EndLabels Dual Separation Strip

variable {M : MapData} {G : IsDiskFullerene M h} {d e : EndPiece M G}

private theorem endpoints {x y} (p : RimWalk G x y) : x∈p.vertices ∧ y∈p.vertices := by
  constructor
  · cases p <;> simp [RimWalk.vertices,RimWalk.starts]
  · simp [RimWalk.vertices]

private theorem private_vertex {x y} (p : RimWalk G x y) {f} (fx : f≠x) (fy : f≠y) (m : f∈p.vertices) :
    f∈p.starts.tail := by
  cases p with
  | nil z => exact False.elim (fx (by simpa [RimWalk.vertices,RimWalk.starts] using m))
  | cons ed tail =>
    change f∈tail.starts
    simp only [RimWalk.vertices,RimWalk.starts,List.cons_append,List.mem_cons,List.mem_append,
      List.not_mem_nil,or_false] at m
    exact (m.resolve_left fx).resolve_right fy

private theorem nonmark (C : Cap d) (hh : 3≤h) {x y} (marks : MarkedBy C x y) (i : Fin 10) :
    C.localFace i≠x ∧ C.localFace i≠y := by
  have sep := C.local_avoids_marks hh i
  rcases marks with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨sep.1,by simpa [Cap.strong,Cap.strongLabel,Cap.outer] using sep.2⟩
  · exact ⟨by simpa [Cap.strong,Cap.strongLabel,Cap.outer] using sep.2,sep.1⟩

private theorem local_outer (C : Cap d) (i : Fin 10) (b : IsBoundary G (C.localFace i)) :
    ∃ j, C.outer j=C.localFace i := by
  exact (C.outer_iff _).2 (.inr (.inr ⟨i,(C.local_boundary i).1 b,rfl⟩))

/-- The spine and the two ten-label cap charts are pairwise disjoint on
the actual dual. The strip can have arbitrary length and handedness. -/
theorem chart_disjoint {C : Cap d} {D : Cap e} {P Q : SeamState G} {moves}
    (hh : 3≤h) (B : LabeledBoundary C D P Q moves)
    (leftMarks : MarkedBy C P.x P.y) (rightMarks : MarkedBy D Q.y Q.x)
    (apart : ∀ z, ¬(vertexSide d.seam d.side z=true ∧ vertexSide e.seam e.side z=true)) :
    B.line.word.Nodup ∧
    (∀ v∈B.line.word, ∀ i : Fin 10, C.localFace i≠v ∧ D.localFace i≠v) ∧
    (∀ i j : Fin 10, C.localFace i≠D.localFace j) := by
  have sep := List.nodup_append.mp B.rare
  have front := List.nodup_append.mp sep.1
  have ends := endpoints B.first
  have xy : P.x≠P.y := by
    have ne := left_ne_right G hh P.cut.xy
    rcases P.cut.middle with m|m <;> rw [m] at ne <;> first | exact ne | exact ne.symm
  have roots {v} (r : v=P.x ∨ v=P.y) : v∈B.first.vertices := r.elim (· ▸ ends.1) (· ▸ ends.2)
  have newApart {x} (v : x∈B.first.vertices) : x∉B.line.newVertices :=
    fun w=>front.2.2 _ v _ w rfl
  have rare : B.line.word.Nodup := by
    change (P.x::P.y::B.line.newVertices).Nodup
    exact List.nodup_cons.mpr ⟨fun h=>(List.mem_cons.mp h).elim xy (newApart ends.1),
      List.nodup_cons.mpr ⟨newApart ends.2,front.2.1⟩⟩
  have support {x} (w : x∈B.line.word) : x∈B.first.vertices++B.line.newVertices := by
    rcases List.mem_cons.mp w with rfl|w;exact List.mem_append_left _ ends.1
    rcases List.mem_cons.mp w with rfl|w;exact List.mem_append_left _ ends.2
    exact List.mem_append_right _ w
  have rim {x} (w : x∈B.line.word) : IsBoundary G x := B.cover.mem_iff.mp
    (List.mem_append_left _ (support w))
  refine ⟨rare,?_,?_⟩
  · intro v vw i
    refine ⟨?_,?_⟩
    · intro eq;subst v
      have cv := (B.firstCover _).2 (local_outer C i (rim vw))
      have off := nonmark C hh leftMarks i
      rcases List.mem_cons.mp vw with eq|w; exact off.1 eq
      rcases List.mem_cons.mp w with eq|w; exact off.2 eq
      exact newApart cv w
    · intro eq;subst v
      have dv := (B.lastCover _).2 (local_outer D i (rim vw))
      have off := nonmark D hh rightMarks i
      exact sep.2.2 _ (support vw) _ (private_vertex B.last off.1 off.2 dv) rfl
  · intro i j eq
    obtain ⟨a,b,inc⟩ := face_dart G hh (C.localFace i)
    let v : Fin M.ord := ⟨a,(dart_info G (incident_dart G inc)).1⟩
    have t : C.localFace i∈triangle v := (mem_triangle _ _).2 (sideEnds inc).1
    exact apart v ⟨C.local_vertex_side hh i t,D.local_vertex_side hh j (eq ▸ t)⟩

end DiskFullerene.StripFresh
