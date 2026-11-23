import DiskFullerene.MarkedCap
import DiskFullerene.MarkedSector
import DiskFullerene.ActualLoads

namespace DiskFullerene.EndFans
open Dual EndEuler EndLabels Separation

private def reorder {V E} {p : E→V×V} {c d : E→Prop} (P : Bipartition p c) (eq : c=d) : Bipartition p d where
  left := P.left
  inhabitedLeft := P.inhabitedLeft
  inhabitedRight := P.inhabitedRight
  components := by rw [←eq]; exact P.components
  crosses := by rw [←eq]; exact P.crosses

private def rotate {M} {G : IsDiskFullerene M h} {w x y} (S : TriangleSide G w x y) : TriangleSide G x y w where
  wx := S.xy
  xy := S.yw
  yw := S.wx
  first := S.middle
  middle := S.last
  last := S.first
  part := reorder S.part (by funext e; apply propext; unfold ThreeEdges; grind)

private theorem count_at_next {M} {G : IsDiskFullerene M h} (hh : 3≤h) {w x y} (S : TriangleSide G w x y) (B : Bool) :
    M.faces[x.val].countP (primalLabelSide S B) = (dualRow G x).countP (faceSide S B)+1 := by
  classical
  have same : faceSide (rotate S) B = faceSide S B := by
    funext f; unfold faceSide; have eq : (f≠x ∧ f≠y ∧ f≠w) ↔ (f≠w ∧ f≠x ∧ f≠y) := by grind
    simp only [eq]; rfl
  rw [←same]; exact sector_count hh (rotate S) B

private theorem mark_count {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d : EndPiece M G) {r : Face M}
    (mark : r=atSide G (apex M) d.i ∨ r=atSide G (apex M) d.j) :
    loadAt d.seam d.side r=(dualRow G r).countP (faceSide d.seam d.side) := by
  classical
  unfold loadAt vertexCountAt
  rcases mark with rfl|rfl
  · rw [count_at_next hh d.seam]; omega
  · have same : faceSide (rotate d.seam) d.side=faceSide d.seam d.side := by
      funext f; unfold faceSide; have eq : (f≠atSide G (apex M) d.i ∧ f≠atSide G (apex M) d.j ∧ f≠apex M) ↔ (f≠apex M ∧ f≠atSide G (apex M) d.i ∧ f≠atSide G (apex M) d.j) := by grind
      simp only [eq]; rfl
    rw [←same]; change (M.faces[(atSide G (apex M) d.j).val].countP (primalLabelSide (rotate d.seam) d.side) - 1)=_
    rw [count_at_next hh (rotate d.seam)]; omega

theorem marked_load {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d : EndPiece M G) {r : Face M}
    (mark : r=atSide G (apex M) d.i ∨ r=atSide G (apex M) d.j) :
    loadAt d.seam d.side r=(dualRow G r).countP (sectorCore d.seam d.side)+1 := by
  classical
  let S:=d.seam; let B:=d.side; let R:=dualRow G r; let A:=sectorCore S B
  obtain ⟨b,bb,br,bS,unique⟩ := boundary_contribution hh d mark
  rw [mark_count hh d mark,List.countP_eq_length_filter,List.countP_eq_length_filter]
  change (R.filter (faceSide S B)).length=(R.filter A).length+1
  have apart : b∉R.filter A := by intro m; exact ((mem_diskInterior G b).mp (core_disk (List.mem_filter.mp m).2)).2 bb
  have perm : (R.filter (faceSide S B)).Perm (b::R.filter A) := by
    have nd := row_nodup G (noRepeatOnSphere G hh) r
    apply (List.perm_ext_iff_of_nodup (nd.filter _) (List.nodup_cons.mpr ⟨apart,nd.filter _⟩)).mpr
    intro z; simp only [List.mem_filter,List.mem_cons]; constructor
    · rintro ⟨zr,pick⟩
      by_cases iz : z∈diskInterior G
      · right; exact ⟨zr,by simp [A,sectorCore,iz,pick]⟩
      · left; apply unique z _ zr pick
        have away : z≠apex M := (of_decide_eq_true (Bool.and_eq_true_iff.mp pick).1 : z≠apex M ∧ z≠_ ∧ z≠_).1
        exact Classical.byContradiction (fun nb=>iz ((mem_diskInterior G z).mpr ⟨away,nb⟩))
    · rintro (rfl|⟨zr,zS⟩); exact ⟨br,bS⟩; exact ⟨zr,(Bool.and_eq_true_iff.mp zS).2⟩
  simpa using perm.length_eq

namespace Cap
variable {M : MapData} {G : IsDiskFullerene M h} {d : EndPiece M G}

private theorem boundary_core (C : Cap d) (_h3 : 3≤h) {b : Face M} (bc : IsBoundary G b) {q : Face M} :
    (sectorCore d.seam d.side q=true ∧ q∈dualRow G b) ↔ ∃ i, q=C.W.rim i ∧ b∈(C.fans.arc i).word := by
  have avoid (f : Face M) (fine : sectorCore d.seam d.side f=true) : b≠f := fun eq=>(mem_diskInterior G _).mp (core_disk fine) |>.2 (eq ▸ bc)
  have ar (i : I) : b≠C.W.rim i := avoid _ (C.rim_in i)
  have nz : b≠C.W.center := avoid _ ((C.W.chosen _).mpr (.inl rfl))
  constructor
  · rintro ⟨iq,nb⟩; have flipped := (dual_adj_symmetric G _ _).mp nb
    rcases (C.W.chosen _).mp iq with rfl|⟨i,rfl⟩
    · obtain ⟨i,eq⟩ := (C.W.central _).mp flipped; exact False.elim (ar i eq)
    · refine ⟨i,rfl,?_⟩; have m := (C.fans.neighbors i).mem_iff.mpr flipped; simp [ar,nz] at m; exact m
  · rintro ⟨i,rfl,mem⟩; exact ⟨C.rim_in i,(dual_adj_symmetric G _ _).mp (C.fans.in_row mem)⟩

theorem middle_neighbors (C : Cap d) (hh : 3≤h) (q : Face M) :
    (sectorCore d.seam d.side q=true ∧ q∈dualRow G C.middle) ↔ q=C.W.rim C.index := by
  have mc := C.boundary (i:=C.index) (v:=C.middle) (by simp [Arc.word,C.split])
  rw [C.boundary_core hh mc]; constructor
  · rintro ⟨i,rfl,mem⟩; rw [C.rim_arc hh i] at mem
    have diff (j : I) : C.middle≠C.junction j := C.mid_ne_corner hh C.split j
    by_cases eq : i=C.index; exact congrArg C.W.rim eq; simp [eq,diff] at mem
  · rintro rfl; exact ⟨_,rfl,by simp [Arc.word,C.split]⟩

theorem junction_neighbors (C : Cap d) (hh : 3≤h) (j : I) (q : Face M) :
    (sectorCore d.seam d.side q=true ∧ q∈dualRow G (C.junction j)) ↔ q=C.W.rim j ∨ q=C.W.rim (before j) := by
  rw [C.boundary_core hh (C.junction_boundary j)]; constructor
  · rintro ⟨i,rfl,mem⟩; rw [C.rim_arc hh i] at mem
    have diff : C.junction j≠C.middle := Ne.symm (C.mid_ne_corner hh C.split j)
    have eq : j=i ∨ j=after i := by split at mem <;> simp [diff] at mem <;> grind [TerminalAnnulus.distinct_corners]
    rcases eq with rfl|rfl; exact .inl rfl; exact .inr (congrArg C.W.rim ((by decide : ∀ i : I, before (after i)=i) i).symm)
  · rintro (rfl|rfl)
    · exact ⟨j,rfl,by simp [TerminalAnnulus.junction,Arc.word]⟩
    · refine ⟨before j,rfl,?_⟩; rw [C.rim_arc hh]; simp [(by decide : ∀ j : I, after (before j)=j) j]

/-- The actual sector loads use the original cubic vertex count minus one
on the marked face, exactly the load followed by the strip traversal. -/
theorem loads (C : Cap d) (hh : 3≤h) :
    loadAt d.seam d.side C.middle=2 ∧ loadAt d.seam d.side (C.junction (if C.second then after C.index else C.index))=3 := by
  let j:=if C.second then after C.index else C.index
  let x:=atSide G (apex M) d.i; let y:=atSide G (apex M) d.j
  have marks : (C.middle=x ∧ C.junction j=y) ∨ (C.middle=y ∧ C.junction j=x) := by cases s : C.second <;> simpa [j,s] using C.seam
  have weak : C.middle=x ∨ C.middle=y := by grind
  have strong : C.junction j=x ∨ C.junction j=y := by grind
  change _=2 ∧ loadAt d.seam d.side (C.junction j)=3
  rw [marked_load hh d weak, marked_load hh d strong,List.countP_eq_length_filter,List.countP_eq_length_filter]
  have a : ((dualRow G C.middle).filter (sectorCore d.seam d.side)).Perm [C.W.rim C.index] := by
    apply (List.perm_ext_iff_of_nodup ((row_nodup G (noRepeatOnSphere G hh) _).filter _) (by simp)).mpr; intro f; simp only [List.mem_filter,List.mem_singleton]
    exact and_comm.trans (C.middle_neighbors hh f)
  have ne : C.W.rim j≠C.W.rim (before j) := fun e=>(by decide : ∀ j : I,j≠before j) j (C.W.rim_injective _ _ e)
  have b : ((dualRow G (C.junction j)).filter (sectorCore d.seam d.side)).Perm [C.W.rim j,C.W.rim (before j)] := by
    apply (List.perm_ext_iff_of_nodup ((row_nodup G (noRepeatOnSphere G hh) _).filter _) (by simp [ne])).mpr; intro f; simp only [List.mem_filter,List.mem_cons,List.not_mem_nil,or_false]
    exact and_comm.trans (C.junction_neighbors hh j f)
  simp [a.length_eq,b.length_eq]

end Cap
end DiskFullerene.EndFans
