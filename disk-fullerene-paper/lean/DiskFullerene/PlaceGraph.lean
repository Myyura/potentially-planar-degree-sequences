import DiskFullerene.CanonicalIso
import DiskFullerene.CanonicalSpine
import DiskFullerene.EndpointLoads
import DiskFullerene.CapPerimeter

namespace DiskFullerene.CanonicalIso
open Dual EndFans Strip StripFresh Construction Separation

private theorem across_neighbor {M} (G : IsDiskFullerene M h) {e : Edge M} {x y}
    (A : Across (dual G) e x y) : y∈dualRow G x := by
  have base : (dual G e).2∈dualRow G (dual G e).1 := (mem_row_iff _ _ _).mpr
    ⟨endpoints e,left_incident G (endpoints_mem e),left_incident G (dart_reverse G (endpoints_mem e))⟩
  rcases A with eq|eq <;> rw [eq] at base
  · exact base
  · exact (dual_adj_symmetric G _ _).mp base

theorem place {M n} {G : IsDiskFullerene M (n+12)} {d e : EndPiece M G} (C : Cap d) (D : Cap e)
    {P Q : SeamState G} {moves : List Side} (B : LabeledBoundary C D P Q moves)
    (norm : moves=List.replicate moves.length .right)
    (first : P.x=C.strong ∧ P.y=C.weak) (last : Q.x=D.weak ∧ Q.y=D.strong)
    (simple : B.line.word.Nodup) (sep : ∀ i j, C.localFace i≠D.localFace j)
    (away : ∀ v∈B.line.word, ∀ i, C.localFace i≠v ∧ D.localFace i≠v) :
    Nonempty (Labeling G) := by
  let word := B.line.word
  let vtx (i : Nat) := word[i]?.getD (apex M)
  let cap (s : Bool) (i : Fin 10) := if s then D.localFace i else C.localFace i
  let label : Vertex → Face M
    | .pole => apex M
    | .cap s i => cap s i
    | .spine i => vtx i
  have hh : 3≤n+12 := by omega
  have count := B.count
  have len : moves.length=n+2 := by omega
  have wl : word.length=n+4 := by change B.line.word.length=_; rw [B.line.word_len,B.agrees,len]
  have right : B.line.moves=List.replicate (n+2) .right := B.agrees.trans (norm.trans (by rw [len]))
  have atWord (i) (hi : i<word.length) : vtx i=word[i] := by simp [vtx,List.getElem?_eq_getElem hi]
  have wmem (i) (hi : i<n+4) : vtx i∈word := by rw [atWord i (by omega)]; exact List.getElem_mem _
  have inside : word⊆dualRow G (apex M) := B.line.word_boundary
    (across_neighbor G P.cut.first) (across_neighbor G (Or.symm P.cut.last))
  have vnot (i) (hi : i<n+4) : vtx i≠apex M := fun eq => row_no_loop G hh _ (eq ▸ inside (wmem _ hi))
  have capOff (s i) : cap s i≠apex M := by cases s; exact C.local_notPole hh i; exact D.local_notPole hh i
  have diff (s i j) (hj : j<n+4) : cap s i≠vtx j := by
    have H := away _ (wmem j hj) i
    cases s; exact H.1; exact H.2
  have ci (a b i j) (H : cap a i=cap b j) : a=b ∧ i=j := by
    cases a <;> cases b <;> simp only [cap,ite_true,ite_false,Bool.false_eq_true,Bool.true_eq_false] at H ⊢
    · exact ⟨trivial,C.local_injective hh i j H⟩
    · exact False.elim (sep _ _ H)
    · exact False.elim (sep _ _ H.symm)
    · exact ⟨trivial,D.local_injective hh i j H⟩
  have range {i} (valid : Vertex.spine i∈vertices n) : i<n+4 := by simpa [vertices] using valid
  have inject (a) (ha : a∈vertices n) (b) (hb : b∈vertices n) (H : label a=label b) : a=b := by
    cases a <;> cases b
    case pole.pole => rfl
    case pole.cap s j => exact False.elim (capOff s j H.symm)
    case pole.spine j => exact False.elim (vnot j (range hb) H.symm)
    case cap.pole s i => exact False.elim (capOff s i H)
    case cap.cap s i t j => obtain ⟨rfl,rfl⟩ := ci s t i j H; rfl
    case cap.spine s i j => exact False.elim (diff s i j (range hb) H)
    case spine.pole i => exact False.elim (vnot i (range ha) H)
    case spine.cap i s j => exact False.elim (diff s j i (range ha) H.symm)
    case spine.spine i j =>
      change vtx i=vtx j at H
      rw [atWord i (by have := range ha; omega), atWord j (by have := range hb; omega)] at H
      exact congrArg Vertex.spine (index_eq simple _ _ H)
  have final := B.line.final_pair right
  have lastWeak : vtx (n+2)=D.weak := by simpa [vtx,word,final.1] using last.1
  have lastStrong : vtx (n+3)=D.strong := by simpa [vtx,word,final.2] using last.2
  have firstWeak : vtx 1=C.weak := first.2
  have firstStrong : vtx 0=C.strong := first.1
  have join (s i j) (edge : joinEdge n s i j=true) : vtx j∈dualRow G (cap s i) := by
    simp only [joinEdge,Bool.or_eq_true_iff,Bool.and_eq_true_iff,beq_iff_eq] at edge
    rcases edge with ⟨ed,rfl⟩|⟨ed,rfl⟩ <;> cases s
    · simpa only [seamZero,Bool.false_eq_true,ite_false,firstWeak,cap] using C.local_weak hh i ed
    · simpa only [seamZero,ite_true,lastWeak,cap] using D.local_weak hh i ed
    · simpa only [seamOne,Bool.false_eq_true,ite_false,firstStrong,cap] using C.local_strong hh i ed
    · simpa only [seamOne,ite_true,lastStrong,cap] using D.local_strong hh i ed
  have capB (s i) : IsBoundary G (cap s i) ↔ 6≤i.val := by cases s; exact C.local_boundary i; exact D.local_boundary i
  refine ⟨⟨label,inject,?_⟩⟩
  intro a ha b hb edge
  cases a <;> cases b
  case pole.pole => contradiction
  case pole.cap s i => exact (capB s i).mpr (of_decide_eq_true edge)
  case cap.pole s i => exact (dual_adj_symmetric G _ _).mp ((capB s i).mpr (of_decide_eq_true edge))
  case pole.spine i => exact inside (wmem i (range hb))
  case spine.pole i => exact (dual_adj_symmetric G _ _).mp (inside (wmem i (range ha)))
  case cap.cap s i t j =>
    have ⟨eq,ed⟩ := Bool.and_eq_true_iff.mp edge
    have st : s=t := by simpa using eq
    subst t; cases s
    · exact C.local_edges hh i j ed
    · exact D.local_edges hh i j ed
  case cap.spine s i j => exact join s i j edge
  case spine.cap i s j => exact (dual_adj_symmetric G _ _).mp (join s j i edge)
  case spine.spine i j =>
    have hi : i<word.length := by have := range ha; omega
    have hj : j<word.length := by have := range hb; omega
    change vtx j∈dualRow G (vtx i)
    rw [atWord j hj,atWord i hi]
    exact B.line.word_edges hh right B.actualFaces simple (across_neighbor G P.cut.middle) i j hi hj edge

end DiskFullerene.CanonicalIso
