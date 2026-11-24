import TraceOverlay
import LeanPool.K5MinorFreeChoosability.Planar.Nonplanar
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! The retained simple primal graph has at most three times as many edges as
active names, including prefixes whose retained graph has leaves or isolates. -/
namespace Recognition.SparseOverlay
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep Recognition.Overlay
open PlanarDegrees.Topology Recognition.Wagner Recognition.Witness
open LeanPool.K5MinorFreeChoosability Equiv.Perm

private theorem sub_planar [Finite V] (G : SimpleGraph V) (H : SimpleGraph W)
    (g : W → V) (inj : Function.Injective g) (sub : ∀ a b, H.Adj a b → G.Adj (g a) (g b))
    (flat : IsPlanar G) : IsPlanar H := by
  classical
  apply isPlanar_of_minorModel flat
  refine ⟨fun w => {g w},fun _ => Finset.singleton_nonempty _,?_,?_,?_⟩
  · intro w
    rw [← connSet_iff_induce_connected]
    simpa using connSet_singleton G (g w)
  · intro a b ne
    simpa using inj.ne ne
  · exact fun a b h => ⟨g a,by simp,g b,by simp,sub a b h⟩

theorem edge_bound (V : Type) [Finite V] (G : SimpleGraph V) (flat : IsPlanar G) :
    Nat.card G.edgeSet ≤ 3*Nat.card V := by
  classical
  have work (n : Nat) : ∀ (U : Type) [Finite U] (H : SimpleGraph U), Nat.card U=n →
      IsPlanar H → Nat.card H.edgeSet ≤ 3*Nat.card U := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro U _ H order emb
      let _ := Fintype.ofFinite U
      by_cases deg : ∀ x : U, 2≤Nat.card {y // H.Adj x y}
      · obtain ⟨M⟩ := emb
        have darts := card_dart_eq_two_mul H
        rw [← card_edgeSet_eq_cycleCount] at darts
        have faces : 3*M.numFaces ≤ Nat.card H.Dart := mul_numClasses_le (SameCycle.setoid M.facePerm)
          3 (three_le_card_face M.isRotationSystem deg)
        have eul := M.euler
        have vert : cycleCount M.rot ≤ Nat.card U := by
          rw [cycleCount_eq_card_nonisolated M.isRotationSystem]
          exact Nat.card_le_card_of_injective _ Subtype.val_injective
        omega
      · obtain ⟨x,small⟩ := Classical.not_forall.mp deg
        let s := ({x}ᶜ : Set U)
        have fewer : Nat.card s<Nat.card U := by
          rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
          exact Fintype.card_subtype_lt (x := x) (p := (·∈s)) (by simp [s])
        let J := H.induce s
        have w := ih _ (lt_of_lt_of_eq fewer order) s J rfl
          (sub_planar H J Subtype.val Subtype.val_injective (fun _ _ h => h) emb)
        have stat := H.card_edgeFinset_induce_compl_singleton x
        rw [H.card_edgeFinset_deleteIncidenceSet] at stat
        have d : H.degree x=Nat.card {y // H.Adj x y} := by
          rw [Nat.card_eq_fintype_card]; exact (H.card_neighborSet_eq_degree x).symm
        have edges {T : Type} [Fintype T] (A : SimpleGraph T) [DecidableRel A.Adj] :
            Nat.card A.edgeSet=A.edgeFinset.card := by simp [SimpleGraph.edgeFinset,Nat.card_eq_fintype_card]
        change J.edgeFinset.card=H.edgeFinset.card-H.degree x at stat
        rw [← edges J,← edges H] at stat
        omega
  exact work _ V G rfl flat

private theorem active_iff (s : Inventory) (a : Nat) :
    a∈(activeNames s).eraseDups ↔ live s a := by simp [activeNames,live,List.mem_flatMap,List.any_eq_true,touches]

private theorem endpoints (s : Inventory) {e : Edge} (h : e∈retained s) :
    e.lo∈(activeNames s).eraseDups ∧ e.hi∈(activeNames s).eraseDups := by
  rw [active_iff,active_iff]
  simp only [retained,List.mem_eraseDups,List.mem_append,retain,List.mem_filter,Bool.and_eq_true] at h
  rcases h with open_|⟨_,h⟩
  · exact ⟨List.any_eq_true.mpr ⟨e,open_,by simp [touches]⟩,
      List.any_eq_true.mpr ⟨e,open_,by simp [touches]⟩⟩
  · exact h

theorem retained_bound {v f : Nat} (C : ClosedTrace v f) (count : (f+1)+4=2*(v+1))
    (read todo : List Face) (perm : (read++todo).Perm (List.ofFn C.faces))
    (s : Inventory) (ok : replay (read.flatMap Face.sides)=some s) :
    (retained s).length≤3*(activeNames s).eraseDups.length := by
  classical
  have seen (e : Edge) (m : e∈retained s) : e∈C.ledger.sealed ∧ e.hi<v+1 := by
    have acc := replay_accurate ok
    have pos : 0<occurrences (read.flatMap Face.sides) e := by
      simp only [retained,List.mem_eraseDups,List.mem_append,retain,List.mem_filter] at m
      rcases m with p|p
      · have := (acc.pending e).mp p; omega
      · have := (acc.sealed e).mp p.1; omega
    obtain ⟨a,ha,eq⟩ := List.mem_map.mp (List.count_pos_iff.mp pos)
    obtain ⟨F,hF,side⟩ := List.mem_flatMap.mp ha
    have full := perm.mem_iff.mp (List.mem_append_left todo hF)
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp full
    have present : e∈(sideTrace C.faces).map Event.edge :=
      List.mem_map.mpr ⟨a,List.mem_flatMap.mpr ⟨i,List.mem_finRange _,side⟩,eq⟩
    have fullP : 0<occurrences (sideTrace C.faces) e := List.count_pos_iff.mpr present
    have pair := (paired_iff_closed.mpr ⟨_,C.accepted,C.closed⟩) e
    refine ⟨((replay_accurate C.accepted).sealed _).mpr (by omega),?_⟩
    subst e
    have ht := C.bounded i
    have yz := (C.faces i).yz
    simp only [Face.sides,List.mem_cons,List.not_mem_nil,or_false] at side
    rcases side with rfl|rfl|rfl
    · exact lt_trans yz ht
    · exact ht
    · exact ht
  let V := (activeNames s).eraseDups.toFinset
  let E := (retained s).toFinset
  have inV {e : Edge} (mem : e∈E) : e.lo∈V ∧ e.hi∈V := by
    simpa [V] using endpoints s (show e∈retained s by simpa [E] using mem)
  let G : SimpleGraph V := {
    Adj := fun a b => ∃ e∈E, joins e a.val b.val
    symm := ⟨fun a b ⟨e,h,j⟩ => ⟨e,h,by simpa [joins,Bool.or_comm] using j⟩⟩
    loopless := ⟨fun a ⟨e,_,j⟩ => by have := e.increasing; simp [joins] at j; omega⟩ }
  have inside (x : V) : x.val<v+1 := by
    have act := (active_iff s x.val).mp (List.mem_toFinset.mp x.property)
    obtain ⟨e,p,t⟩ := List.any_eq_true.mp act
    have hb := (seen e (by simp [retained,p])).2
    have lo := e.increasing
    simp [touches] at t
    omega
  let label := fun x : V => (⟨x.val,inside x⟩ : Fin (v+1))
  obtain ⟨R,_⟩ := TracePlanarity.host_rows C count
  have planar : IsPlanar G := by
    apply sub_planar (toSimple (host C)) G label (fun x y h => Subtype.ext (congrArg Fin.val h)) _ ⟨R.plane⟩
    rintro x y ⟨e,mem,edge⟩
    apply (graph_adj ..).mpr
    exact ⟨e,(seen e (by simpa [E] using mem)).1,edge⟩
  let lp := fun e : E => (⟨e.val.lo,(inV e.property).1⟩ : V)
  let rp := fun e : E => (⟨e.val.hi,(inV e.property).2⟩ : V)
  let send := fun e : E => (⟨s(lp e,rp e),(G.mem_edgeSet).mpr ⟨e.val,e.property,by simp [lp,rp,joins]⟩⟩ : G.edgeSet)
  have inj : Function.Injective send := by
    rintro ⟨e,he⟩ ⟨g,hg⟩ same
    have eq := congrArg Subtype.val same
    rcases Sym2.eq_iff.mp eq with p|p
    all_goals
      have l := congrArg Subtype.val p.1
      have r := congrArg Subtype.val p.2
      simp only [lp,rp] at l r
    · cases e; cases g; simp_all
    · have := e.increasing; have := g.increasing; omega
  have w := (Nat.card_le_card_of_injective send inj).trans (edge_bound V G planar)
  have card {A : Type} [DecidableEq A] (xs : List A) (nd : xs.Nodup) :
      Nat.card ↥xs.toFinset=xs.length := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,List.toFinset_card_of_nodup nd]
  rw [card _ (show (retained s).Nodup from distinct_names _),card _ (distinct_names _)] at w
  exact w

#print axioms retained_bound
end Recognition.SparseOverlay
