import DiskFullerene.CutSides
import DiskFullerene.Dissection
import DiskFullerene.BoundaryCount

namespace DiskFullerene.Dual
open Dissection

/-- Index both ends of a chord by positions on the *input* outer face. -/
def Drawn {M} (G : IsDiskFullerene M h) (c : Chord) : Prop :=
  ∃ i j : Fin M.faces[(apex M).val].length, c.l = i.val ∧ c.r = j.val ∧
    diagonal (· < M.faces[(apex M).val].length) c ∧
    atSide G (apex M) j ∈ dualRow G (atSide G (apex M) i)

private theorem pairs_nodup (n : Nat) :
    ((List.range n).flatMap (fun i => (List.range n).map (fun j => Chord.mk i j))).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro i _
    exact List.pairwise_map.mpr ((List.nodup_range).imp (fun ne eq => ne (congrArg Chord.r eq)))
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj lt a ha b hb
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hb
    simp only [List.getElem_range, ne_eq, Chord.mk.injEq]
    omega

noncomputable def chords {M} (G : IsDiskFullerene M h) : List Chord := by
  classical
  let n := M.faces[(apex M).val].length
  exact ((List.range n).flatMap fun i => (List.range n).map (fun j => Chord.mk i j)).filter
    (fun c => decide (Drawn G c))

theorem mem_chords {M} (G : IsDiskFullerene M h) (c : Chord) :
    c ∈ chords G ↔ Drawn G c := by
  classical
  unfold chords
  rw [List.mem_filter]
  constructor
  · intro h; exact of_decide_eq_true h.2
  · intro hc
    have orig := hc
    obtain ⟨i,j,hl,hr,_⟩ := hc
    exact ⟨List.mem_flatMap.mpr ⟨i.val,List.mem_range.mpr i.isLt,List.mem_map.mpr
      ⟨j.val,List.mem_range.mpr j.isLt, by cases c; simp_all⟩⟩,decide_eq_true orig⟩

theorem drawn_noncrossing {M} (G : IsDiskFullerene M h) (hh : 3≤h) {a b}
    (ha : Drawn G a) (hb : Drawn G b) : noncrossing a b := by
  obtain ⟨i,k,ai,ak,da,A⟩ := ha
  obtain ⟨j,l,bj,bl,db,B⟩ := hb
  have ik := da.1
  have jl := db.1
  have n1 : ¬(i < j ∧ j < k ∧ k < l) := fun ⟨p,q,r⟩ => noInterleaved G hh _ i j k l p q r A B
  have n2 : ¬(j < i ∧ i < l ∧ l < k) := fun ⟨p,q,r⟩ => noInterleaved G hh _ j i l k p q r B A
  change ¬(i.val < j.val ∧ j.val < k.val ∧ k.val < l.val) at n1
  change ¬(j.val < i.val ∧ i.val < l.val ∧ l.val < k.val) at n2
  unfold noncrossing within
  omega

/-- All actual chords can be cut successively; each is still a diagonal in
the piece in which it is cut. This records the boundary polygons, independently
of any later assignment of interior triangles to individual regions. -/
noncomputable def chordCuts {M} (G : IsDiskFullerene M h) (hh : 3≤h) :
    Cuts (· < M.faces[(apex M).val].length) (chords G) :=
  cutAll _ _ (by
    intro c hc
    obtain ⟨_,_,_,_,dia,_⟩ := (mem_chords G c).mp hc
    exact dia) (by
    have unique : (chords G).Nodup := List.filter_sublist.nodup (pairs_nodup _)
    apply unique.imp_of_mem
    intro a b ha hb ne
    exact ⟨ne,drawn_noncrossing G hh ((mem_chords G a).mp ha) ((mem_chords G b).mp hb)⟩)

theorem number_of_regions {M} (G : IsDiskFullerene M h) (hh : 3≤h) :
    cellCount (chordCuts G hh) = (chords G).length + 1 := cut_cell_count _

end DiskFullerene.Dual
