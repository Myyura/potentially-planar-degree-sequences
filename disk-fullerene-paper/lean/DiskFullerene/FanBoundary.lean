import DiskFullerene.EndFans
import DiskFullerene.TerminalInterior

namespace DiskFullerene.EndFans
open Dual EndEuler EndLabels Separation

structure Arc (α : Type) where
  first : α
  mid : Option α
  last : α

def Arc.word (a : Arc α) := a.first :: (a.mid.toList ++ [a.last])

private theorem arc_of_list {r : List α} (size : r.length=2 ∨ r.length=3) : ∃ a : Arc α, r=a.word := by
  cases r with
  | nil => simp at size
  | cons a r => cases r with
    | nil => simp at size
    | cons b r => cases r with
      | nil => exact ⟨⟨a,none,b⟩,rfl⟩
      | cons c r => cases r with
        | nil => exact ⟨⟨a,some b,c⟩,rfl⟩
        | cons d rest => simp at size

private theorem ends {r : List α} {a b : α} (e : (a,b)∈sides r) : a∈r ∧ b∈r := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp e; rw [sides_size] at hi; rw [side_at _ _ hi] at eq
  exact ⟨(Prod.mk.inj eq).1 ▸ List.getElem_mem _,(Prod.mk.inj eq).2 ▸ List.getElem_mem _⟩

private theorem next_unique {r : List α} (nd : r.Nodup) {a b c : α} (e : (a,b)∈sides r) (f : (a,c)∈sides r) : b=c := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp e; obtain ⟨j,hj,er⟩ := List.mem_iff_getElem.mp f
  rw [sides_size] at hi hj; rw [side_at _ _ hi] at eq; rw [side_at _ _ hj] at er
  have ij := index_eq nd hi hj ((Prod.mk.inj eq).1.trans (Prod.mk.inj er).1.symm); subst j
  exact (Prod.mk.inj eq).2.symm.trans (Prod.mk.inj er).2

structure Annulus {M} {G : IsDiskFullerene M h} {A : Face M→Bool} (W : Wheel G A) where
  arc : I→Arc (Face M)
  outside : ∀ i, ∀ z∈(arc i).word, A z=false
  neighbors : ∀ i, (W.rim (after i)::W.center::W.rim (before i)::(arc i).word).Perm (dualRow G (W.rim i))
  corners : ∀ i, (sides (W.rim (after i)::W.center::W.rim (before i)::(arc i).word)).Perm (sides (dualRow G (W.rim i)))

noncomputable def annulus {M} {G : IsDiskFullerene M h} {A : Face M→Bool} (hh : 3≤h) (pole : A (apex M)=false) (W : Wheel G A) : Annulus W := by
  let fans (i : I) := Classical.choice (rim_fan hh pole W i)
  let arms (i : I) := (arc_of_list (fans i).size).choose
  have eq (i : I) : (fans i).arc=(arms i).word := (arc_of_list (fans i).size).choose_spec
  refine ⟨arms,fun i=>eq i ▸ (fans i).outside,fun i=>eq i ▸ (fans i).neighbors,fun i=>eq i ▸ (fans i).corners⟩

namespace Annulus
variable {M : MapData} {G : IsDiskFullerene M h} {A : Face M→Bool} {W : Wheel G A}

theorem in_row (U : Annulus W) {i z} (m : z∈(U.arc i).word) : z∈dualRow G (W.rim i) := (U.neighbors i).mem_iff.mp (by simp [m])

theorem joined (U : Annulus W) (hh : 3≤h) (i : I) : (U.arc i).last=(U.arc (after i)).first := by
  have a (i : I) : ((U.arc i).last,W.rim (after i))∈sides (dualRow G (W.rim i)) := by
    apply (U.corners i).mem_iff.mp; cases eq : (U.arc i).mid <;> simp [Arc.word,eq,sides]
  have b (i : I) : (W.rim (before i),(U.arc i).first)∈sides (dualRow G (W.rim i)) := by
    apply (U.corners i).mem_iff.mp; cases eq : (U.arc i).mid <;> simp [Arc.word,eq,sides]
  have f := (turn_triangle G (a i)).2; have e := b (after i)
  have eq := (by decide : ∀ i : I, before (after i)=i) i
  rw [eq] at e; exact next_unique (row_nodup G (noRepeatOnSphere G hh) _) f e

theorem fan_run (U : Annulus W) (hh : 3≤h) {i b} (split : (U.arc i).mid=some b) :
    (U.arc i).first≠(U.arc i).last ∧ A (U.arc i).first=false ∧ A b=false ∧ A (U.arc i).last=false ∧
    ((U.arc i).first,b)∈sides (dualRow G (W.rim i)) ∧ (b,(U.arc i).last)∈sides (dualRow G (W.rim i)) := by
  have nd := (U.neighbors i).nodup_iff.mpr (row_nodup G (noRepeatOnSphere G hh) _)
  have rare : (U.arc i).first≠(U.arc i).last := by simp [Arc.word,split] at nd; grind
  refine ⟨rare,U.outside i _ (by simp [Arc.word]),U.outside i _ (by simp [Arc.word,split]),U.outside i _ (by simp [Arc.word,split]),?_,?_⟩ <;>
    apply (U.corners i).mem_iff.mp <;> simp [sides,Arc.word,split]

end Annulus

theorem core_disk {M} {G : IsDiskFullerene M h} {x y} {S : TriangleSide G (apex M) x y} {B f}
    (fIn : sectorCore S B f=true) : f∈diskInterior G := by classical exact of_decide_eq_true (Bool.and_eq_true_iff.mp fIn).1

structure TerminalAnnulus {M} {G : IsDiskFullerene M h} (d : EndPiece M G) where
  W : Wheel G (sectorCore d.seam d.side)
  fans : Annulus W

namespace TerminalAnnulus
variable {M : MapData} {G : IsDiskFullerene M h} {d : EndPiece M G}

theorem rim_in (T : TerminalAnnulus d) (i : I) : sectorCore d.seam d.side (T.W.rim i)=true := (T.W.chosen _).mpr (.inr ⟨i,rfl⟩)

theorem boundary (T : TerminalAnnulus d) {i v} (mem : v∈(T.fans.arc i).word) : IsBoundary G v :=
  core_frontier d.seam (T.rim_in i) (T.fans.outside i v mem) (T.fans.in_row mem)

theorem split_mark (T : TerminalAnnulus d) (hh : 3≤h) {i v} (split : (T.fans.arc i).mid=some v) :
    v=atSide G (apex M) d.i ∨ v=atSide G (apex M) d.j := by
  obtain ⟨ne,af,bf,cf,e,f⟩ := T.fans.fan_run hh split
  exact (terminal_run hh d.seam d.side d.terminal (T.rim_in i) ne af bf cf e f).1

theorem unique_split (T : TerminalAnnulus d) (hh : 3≤h) {i j a b} (one : (T.fans.arc i).mid=some a) (two : (T.fans.arc j).mid=some b) : i=j := by
  have run (k : I) (z : Face M) (eq : (T.fans.arc k).mid=some z) : BoundaryRun G (sectorCore d.seam d.side) (T.W.rim k) := by
    obtain ⟨ne,af,bf,cf,e,f⟩ := T.fans.fan_run hh eq; exact ⟨_,_,_,ne,af,bf,cf,e,f⟩
  obtain ⟨z,only⟩ := terminal_single_run hh d.seam d.side d.terminal
  exact T.W.rim_injective i j ((only _ (T.rim_in i) (run _ _ one)).trans (only _ (T.rim_in j) (run _ _ two)).symm)



noncomputable def touches (T : TerminalAnnulus d) (v : Face M) := (List.finRange 5).filter (fun i => decide (v∈dualRow G (T.W.rim i)))

theorem mixed_degree (T : TerminalAnnulus d) {v : Face M} (outside : List (Face M)) (rare : outside.Nodup)
    (near : outside ⊆ dualRow G v) (clean : ∀ b∈outside, b=apex M ∨ IsBoundary G b) :
    outside.length+(T.touches v).length ≤ (dualRow G v).length := by
  let r := (T.touches v).map T.W.rim
  have nd : r.Nodup := List.pairwise_map.mpr (((List.nodup_finRange _).filter _).imp (fun h eq=>h (T.W.rim_injective _ _ eq)))
  have both : (outside++r).Nodup := by
    apply List.nodup_append.mpr; refine ⟨rare,nd,?_⟩
    intro a ma b mb ab; obtain ⟨i,_,rfl⟩ := List.mem_map.mp mb
    have inner := (mem_diskInterior G _).mp (core_disk (T.rim_in i))
    rcases clean a ma with eq|bc; exact inner.1 (ab.symm.trans eq); exact inner.2 (ab ▸ bc)
  have sub : outside++r ⊆ dualRow G v := by
    apply List.append_subset.mpr; refine ⟨near,?_⟩
    intro u m; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp m
    exact (dual_adj_symmetric G _ _).mp (of_decide_eq_true (List.mem_filter.mp hi).2)
  simpa [r] using both.length_le_of_subset sub

theorem boundarySlots (_T : TerminalAnnulus d) (hh : 3≤h) {v : Face M} (b : IsBoundary G v) :
    ∃ p q : Face M, [apex M,p,q].Nodup ∧ [apex M,p,q] ⊆ dualRow G v ∧
      (∀ z∈[apex M,p,q], z=apex M ∨ IsBoundary G z) ∧ OnCycle (dualRow G (apex M)) v p ∧ OnCycle (dualRow G (apex M)) v q := by
  have cycle := boundary_cycle G hh
  obtain ⟨p,hp,q,hq,pq,px,xq,_⟩ := cycle_at cycle.1 (by omega) b
  have pole (a : Face M) (ha : IsBoundary G a) : apex M≠a := fun eq=>row_no_loop G hh _ (eq ▸ ha)
  refine ⟨p,q,by simp [pole _ hp,pole _ hq,pq],?_,?_,.inr px,.inl xq⟩
  · intro z zm; simp only [List.mem_cons,List.not_mem_nil,or_false] at zm
    rcases zm with rfl|rfl|rfl
    · exact (dual_adj_symmetric G _ _).mp b
    · exact (dual_adj_symmetric G _ _).mp (cyclic_link G _ px)
    · exact cyclic_link G _ xq
  · intro z zm; simp only [List.mem_cons,List.not_mem_nil,or_false] at zm; grind [IsBoundary]

theorem capacity (T : TerminalAnnulus d) (hh : 3≤h) {v : Face M} (b : IsBoundary G v) : (T.touches v).length≤3 := by
  obtain ⟨p,q,nd,sub,cl,_,_⟩ := boundarySlots T hh b
  have cap := T.mixed_degree [_,p,q] nd sub cl
  have deg := inner_degree G (show v≠apex M from fun eq=>row_no_loop G hh _ (eq ▸ b))
  simp only [List.length_cons,List.length_nil] at cap; omega

theorem meets (T : TerminalAnnulus d) {i} {z : Face M} (e : z∈(T.fans.arc i).word) : i∈T.touches z :=
  List.mem_filter.mpr ⟨List.mem_finRange _,decide_eq_true (T.fans.in_row e)⟩

theorem previous_meets (T : TerminalAnnulus d) (hh : 3≤h) (i : I) : before i∈T.touches (T.fans.arc i).first := by
  have eq := T.fans.joined hh (before i); rw [(by decide : ∀ i : I, after (before i)=i) i] at eq
  rw [←eq]; apply T.meets; simp [Arc.word]

private theorem fan_first_ne_last (T : TerminalAnnulus d) (hh : 3≤h) (i : I) : (T.fans.arc i).first≠(T.fans.arc i).last := by
  have nd := (T.fans.neighbors i).nodup_iff.mpr (row_nodup G (noRepeatOnSphere G hh) _)
  cases e : (T.fans.arc i).mid <;> simp [Arc.word,e] at nd <;> grind

/-- The five junctions of the fan arcs are distinct actual boundary
vertices. A repeated nonconsecutive junction would see four rim vertices. -/
theorem distinct_corners (T : TerminalAnnulus d) (hh : 3≤h) (i j : I) (eq : (T.fans.arc i).first=(T.fans.arc j).first) : i=j := by
  apply Classical.byContradiction; intro ne
  have consecutive (a b : I) (ab : b=after a) : (T.fans.arc a).first≠(T.fans.arc b).first := by
    rw [ab,←T.fans.joined hh a]; exact T.fan_first_ne_last hh a
  have ij : j≠after i := fun e=>consecutive i j e eq
  have ji : i≠after j := fun e=>consecutive j i e eq.symm
  have table : ∀ a b : I, a≠b → b≠after a → a≠after b → [before a,a,before b,b].Nodup := by decide
  let z := (T.fans.arc i).first
  have h1 : before i∈T.touches z := T.previous_meets hh i
  have h2 : i∈T.touches z := T.meets (by simp [Arc.word,z])
  have h3 : before j∈T.touches z := by change _∈T.touches (T.fans.arc i).first; rw [eq]; exact T.previous_meets hh j
  have h4 : j∈T.touches z := by change _∈T.touches (T.fans.arc i).first; rw [eq]; exact T.meets (by simp [Arc.word])
  have bound := (table i j ne ij ji).length_le_of_subset (l₂:=T.touches z) (by intro a m; simp at m; grind)
  have cap := T.capacity hh (T.boundary (i:=i) (v:=z) (by simp [z,Arc.word]))
  simp at bound; omega

end TerminalAnnulus
end DiskFullerene.EndFans
