import Combined.EdgePatch
import BoundaryEG
import SparseBoundary.FanRealization
import SparseBoundary.GraphCliqueSum
import SparseBoundary.GraphWeighted

/-! Local constructions on the three sides of a marked triangle. -/
namespace Combined.Spectrum
open SparseBoundary SparseBoundary.Graph Combined.EdgePatch

structure Frame (a b c : ℕ) (tail : Multiset ℕ) where
  n : ℕ
  G : Graph n
  plane : G.Planar
  A : Fin n
  B : Fin n
  C : Fin n
  ab : G.adj A B=true
  bc : G.adj B C=true
  ca : G.adj C A=true
  da : G.degree A=a
  db : G.degree B=b
  dc : G.degree C=c
  rest : List (Fin n)
  cover : (List.finRange n).Perm (A::B::C::rest)
  degrees : (rest.map G.degree : Multiset ℕ) = tail

def Frame.rotate (w : Frame a b c t) : Frame b c a t :=
  { w with A:=w.B, B:=w.C, C:=w.A, ab:=w.bc,bc:=w.ca,ca:=w.ab,
           da:=w.db,db:=w.dc,dc:=w.da,cover:=w.cover.trans
             ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons _)) }

theorem Frame.planaric (w : Frame a b c t) (ds : List ℕ) (hs : (ds : Multiset ℕ)=t) :
    Planaric (a::b::c::ds) := by
  apply (planaric_perm (d:=List.ofFn w.G.degree) _).mp (planaric_profile w.plane)
  rw [List.ofFn_eq_map]
  refine (w.cover.map _).trans ?_
  simp only [List.map_cons,w.da,w.db,w.dc]
  exact ((Multiset.coe_eq_coe.mp (w.degrees.trans hs.symm)).cons c |>.cons b).cons a

private theorem away (w : Frame a b c t) (x : Fin w.n) (hx : x∈w.rest) :
    x≠w.A ∧ x≠w.B := by
  have h := w.cover.nodup_iff.mp (List.nodup_finRange _)
  simp only [List.nodup_cons,List.mem_cons,not_or] at h
  exact ⟨fun eq => h.1.2.2 (eq ▸ hx),fun eq => h.2.1.2 (eq ▸ hx)⟩

def Frame.patch (w : Frame a b c t) (j : Bool) :
    Frame (a+2) (b+2) c ((2+j.toNat)::ₘ(2+j.toNat)::ₘt) := by
  let K := twins w.G w.A w.B j
  let shift := fun x : Fin w.n => x.succ.succ
  let y := (0 : Fin (w.n+1)).succ
  have old (x z : Fin w.n) : K.adj (shift x) (shift z)=w.G.adj x z := by
    simp [K,twins,shift,parallelPath,incident]
  have ca : w.C≠w.A := by intro e; have h := w.ca; rw [e,Graph.adj_self] at h; contradiction
  have cb : w.C≠w.B := by intro e; have h := w.bc; rw [e,Graph.adj_self] at h; contradiction
  have fresh := twins_new w.ab j
  refine ⟨w.n+2,K,twins_planar w.plane w.ab j,shift w.A,shift w.B,shift w.C,
    (old ..).trans w.ab,(old ..).trans w.bc,(old ..).trans w.ca,?_,?_,?_,
    0::y::w.rest.map shift,?_,?_⟩
  · simp [K,shift,twins_old,pairRow,w.da]
  · simp [K,shift,twins_old,pairRow,w.db]
  · simp [K,shift,twins_old,pairRow,w.dc,ca,cb]
  · rw [List.finRange_succ,List.finRange_succ,List.map_cons,List.map_map]
    have h := ((w.cover.map shift).cons y).cons 0
    simp only [List.map_cons] at h
    refine h.trans ?_
    exact (List.perm_append_comm (l₁:=[0,y]) (l₂:=[shift w.A,shift w.B,shift w.C])).append_right _
  · have h : (w.rest.map shift).map K.degree=w.rest.map w.G.degree := by
      rw [List.map_map]
      apply List.map_congr_left
      intro x hx
      obtain ⟨ha,hb⟩ := away w x hx
      simp [K,shift,twins_old,pairRow,ha,hb]
    simp only [List.map_cons,h]
    change K.degree 0 ::ₘ K.degree y ::ₘ (w.rest.map w.G.degree : Multiset ℕ) = _
    rw [w.degrees]
    exact congrArg₂ Multiset.cons fresh.1 (congrArg (fun x => x ::ₘ t) fresh.2)

def Frame.single (w : Frame a b c t) : Frame (a+1) (b+1) c (2 ::ₘ t) := by
  let K := w.G.parallelPath w.A w.B
  have old (x z : Fin w.n) : K.adj x.succ z.succ=w.G.adj x z := by simp [K,parallelPath,incident]
  have ca : w.C≠w.A := by intro e; have h := w.ca; rw [e,Graph.adj_self] at h; contradiction
  have cb : w.C≠w.B := by intro e; have h := w.bc; rw [e,Graph.adj_self] at h; contradiction
  refine ⟨w.n+1,K,parallelPath_planar w.plane w.ab,w.A.succ,w.B.succ,w.C.succ,
    (old ..).trans w.ab,(old ..).trans w.bc,(old ..).trans w.ca,?_,?_,?_,0::w.rest.map Fin.succ,?_,?_⟩
  · simp [K,parallelPath_old_degree,pairRow,w.da]
  · simp [K,parallelPath_old_degree,pairRow,w.db]
  · simp [K,parallelPath_old_degree,pairRow,w.dc,ca,cb]
  · rw [List.finRange_succ]
    refine ((w.cover.map Fin.succ).cons 0).trans ?_
    exact (List.perm_middle (a:=0) (l₁:=[w.A.succ,w.B.succ,w.C.succ])).symm
  · have h : (w.rest.map Fin.succ).map K.degree=w.rest.map w.G.degree := by
      rw [List.map_map]
      apply List.map_congr_left
      intro x hx
      obtain ⟨ha,hb⟩ := away w x hx
      simp [K,parallelPath_old_degree,pairRow,ha,hb]
    simp only [List.map_cons,h]
    change K.degree 0 ::ₘ (w.rest.map w.G.degree : Multiset ℕ) = _
    rw [w.degrees,show K.degree 0=2 from parallelPath_new_degree w.ab]

def Frame.stepTwo (w : Frame a b c t) :
    Frame (a+4) (b+4) (c+4) (2::ₘ2::ₘ3::ₘ3::ₘ3::ₘ3::ₘt) := by
  exact (((w.patch true).rotate.patch true).rotate.patch false).rotate

/-- The double fan on a path of length k+1, marked at its two apices and
the first endpoint of the path. -/
def evenBase (k : ℕ) : Frame (k+3) (k+3) 3 (Multiset.replicate k 4 + {3}) := by
  let G := Fan.support (k+2)
  let A : Fin (k+2+2) := ⟨0,by omega⟩
  let B : Fin (k+2+2) := ⟨1,by omega⟩
  let C : Fin (k+2+2) := ⟨2,by omega⟩
  let f (i : Fin (k+1)) : Fin (k+2+2) := ⟨3+i.val,by omega⟩
  let R := List.ofFn f
  have fa : A.val=0 := rfl
  have fb : B.val=1 := rfl
  have fc : C.val=2 := rfl
  have degs : R.map G.degree = List.replicate k 4 ++ [3] := by
    apply List.ext_getElem
    · simp [R]
    · intro i hi hi'
      simp only [R,List.getElem_map,List.getElem_ofFn]
      rw [Fan.support_path _ (by simp [f];omega)]
      simp only [f]
      by_cases lt : i<k
      · rw [List.getElem_append_left (by simp;omega),List.getElem_replicate]
        split_ifs <;> omega
      · rw [List.getElem_append_right (by simp;omega)]
        have e : i=k := by simp at hi';omega
        subst i
        simp only [List.length_replicate,Nat.sub_self,List.getElem_cons_zero]
        split_ifs <;> omega
  refine ⟨_,G,Fan.support_planar _,A,B,C,?_,?_,?_,?_,?_,?_,R,?_,?_⟩
  · apply (Fan.support_adjacent_iff ..).mpr; simp [fa,fb]
  · apply (Fan.support_adjacent_iff ..).mpr; simp [fb,fc]
  · apply (Fan.support_adjacent_iff ..).mpr; simp [fc,fa]
  · apply Fan.support_hub _ (by simp [fa])
  · apply Fan.support_hub _ (by simp [fb])
  · rw [Fan.support_path _ (by simp [fc])]
    simp [fc]
  · apply List.Perm.of_eq
    apply List.ext_getElem
    · simp [R]
    · intro i hi hi'
      apply Fin.ext
      match i with
      | 0 | 1 | 2 => simp only [List.getElem_finRange,List.getElem_cons_zero,List.getElem_cons_succ];rfl
      | i+3 => simp only [List.getElem_finRange,List.getElem_cons_succ,R,List.getElem_ofFn,f,Fin.val_cast];omega
  · rw [degs, ←Multiset.coe_add, Multiset.coe_replicate]; rfl

private theorem erase_other_degree (H : Graph n) (a b x : Fin n) (ha : x≠a) (hb : x≠b) :
    (H.eraseEdge a b).degree x = H.degree x := by
  have eq : (H.eraseEdge a b).adj x = H.adj x := by
    funext y
    simp [erase_adj,eraseRel,ha,hb]
  simp [Graph.degree,eq]

private theorem erase_target (H : Graph n) (a b : Fin n) (he : H.adj a b=true) :
    (H.eraseEdge a b).degree b + 1 = H.degree b := by
  have eq : H.eraseEdge a b=H.eraseEdge b a := by
    apply eq_of_adj
    intro u v
    simp [erase_adj,eraseRel,Bool.or_comm]
  rw [eq]
  exact erase_source H b a ((H.adj_comm b a).trans he)

/-- For the odd base use the path x,y,C,u,... under the two apices.
Deleting Ay leaves x and y cubic. A single parallel AC path finishes the base. -/
def oddBase (k : ℕ) :
    Frame (k+5) (k+5) 5 (2::ₘ(3::ₘ3::ₘ( Multiset.replicate k 4+{3}))) := by
  let H := Fan.support (k+4)
  let atV (i : ℕ) (h : i < k+4+2) : Fin (k+4+2) := ⟨i,h⟩
  let A := atV 0 (by omega)
  let B := atV 1 (by omega)
  let X := atV 2 (by omega)
  let Y := atV 3 (by omega)
  let C := atV 4 (by omega)
  let G := H.eraseEdge A Y
  let f (i : Fin (k+1)) : Fin (k+4+2) := ⟨5+i.val,by omega⟩
  let R := List.ofFn f
  have edge : H.adj A Y=true := (Fan.support_adjacent_iff ..).mpr (by simp +zetaDelta)
  have original : G.Planar := by
    apply Fan.two_apex_path_planar
    intro u v hu hv e
    have e' : H.adj u v=true := (Bool.and_eq_true_iff.mp (by simpa only [G,erase_adj,eraseRel] using e)).1
    have h := (Fan.support_adjacent_iff ..).mp e'
    omega
  have q : G.degree A=k+4 := by
    change (H.eraseEdge A Y).degree A = _
    have h := erase_source H A Y edge
    rw [Fan.support_hub A (by simp +zetaDelta)] at h
    omega
  have qy : G.degree Y=3 := by
    change (H.eraseEdge A Y).degree Y = _
    have h := erase_target H A Y edge
    rw [Fan.support_path Y (by simp +zetaDelta)] at h
    change (H.eraseEdge A Y).degree Y+1 = 2+(if 2<3 then 1 else 0)+(if 3+1<k+4+2 then 1 else 0) at h
    split_ifs at h <;> omega
  have qx : G.degree X=3 := by
    rw [erase_other_degree H A Y X (by simp +zetaDelta) (by simp +zetaDelta),
      Fan.support_path X (by simp +zetaDelta)]
    simp only [X,atV]
    split_ifs <;> omega
  have degs : R.map G.degree=List.replicate k 4 ++ [3] := by
    apply List.ext_getElem
    · simp [R]
    · intro i hi hi'
      simp only [R,List.getElem_map,List.getElem_ofFn]
      rw [erase_other_degree H A Y _ (by intro e; have := congrArg Fin.val e; dsimp [A,f,atV] at this; omega)
        (by intro e; have := congrArg Fin.val e; dsimp [Y,f,atV] at this; omega)]
      rw [Fan.support_path _ (by dsimp [f];omega)]
      dsimp [f]
      by_cases lt : i<k
      · rw [List.getElem_append_left (by simp;omega),List.getElem_replicate]
        split_ifs <;> omega
      · rw [List.getElem_append_right (by simp;omega)]
        have e : i=k := by simp at hi';omega
        subst i
        simp only [List.length_replicate,Nat.sub_self,List.getElem_cons_zero]
        split_ifs <;> omega
  let w : Frame (k+4) (k+5) 4 (3::ₘ3::ₘ( Multiset.replicate k 4+{3})) := by
    refine ⟨_,G,original,A,B,C,?_,?_,?_,q,?_,?_,X::Y::R,?_,?_⟩
    · rw [erase_adj,eraseRel]; simp [show H.adj A B=true from (Fan.support_adjacent_iff ..).mpr (by simp +zetaDelta),
        show B≠Y by simp +zetaDelta,show A≠Y by simp +zetaDelta]
    · rw [erase_adj,eraseRel]; simp [show H.adj B C=true from (Fan.support_adjacent_iff ..).mpr (by simp +zetaDelta),
        show B≠A by simp +zetaDelta,show B≠Y by simp +zetaDelta]
    · rw [erase_adj,eraseRel]; simp [show H.adj C A=true from (Fan.support_adjacent_iff ..).mpr (by simp +zetaDelta),
        show C≠A by simp +zetaDelta,show C≠Y by simp +zetaDelta]
    · rw [erase_other_degree H A Y B (by simp +zetaDelta) (by simp +zetaDelta),Fan.support_hub B (by simp +zetaDelta)]
    · rw [erase_other_degree H A Y C (by simp +zetaDelta) (by simp +zetaDelta),Fan.support_path C (by simp +zetaDelta)]

      change (2+(if 2<4 then 1 else 0)+(if 5<k+6 then 1 else 0) : ℕ)=4
      split_ifs <;> omega
    · have eq : List.finRange (k+4+2)=A::B::X::Y::C::R := by
        apply List.ext_getElem
        · simp [R]
        · intro i _ _
          apply Fin.ext
          match i with
          | 0 | 1 | 2 | 3 | 4 => simp only [List.getElem_finRange,List.getElem_cons_zero,List.getElem_cons_succ];rfl
          | i+5 => simp only [List.getElem_finRange,List.getElem_cons_succ,R,List.getElem_ofFn,f,Fin.val_cast];omega
      rw [eq]
      exact ((List.perm_middle (a:=C) (l₁:=[X,Y]) (l₂:=R)).cons B).cons A
    · simp only [List.map_cons,qx,qy,degs]
      rw [←Multiset.coe_replicate]
      rfl
  exact w.rotate.rotate.single.rotate

private def bulk (k m base : ℕ) : Multiset ℕ :=
  Multiset.replicate k 4 + Multiset.replicate (2*m+base) 3 + Multiset.replicate m 2

private theorem bulk_step (k m h : ℕ) :
    2::ₘ2::ₘ3::ₘ3::ₘ3::ₘ3::ₘbulk k m h = bulk k (m+2) h := by
  ext x
  simp only [bulk,Multiset.count_add,Multiset.count_cons,Multiset.count_replicate]
  split_ifs <;> omega

private theorem of_frame (k m : ℕ) :
    Nonempty (Frame (k+2*m+3) (k+2*m+3) (2*m+3) (bulk k m 1)) := by
  induction m using Nat.twoStepInduction with
  | zero => simpa [bulk] using (show Nonempty _ from ⟨evenBase k⟩)
  | one =>
    have shape : 2::ₘ3::ₘ3::ₘ( Multiset.replicate k 4+{3}) = bulk k 1 1 := by
      ext x; simp only [bulk,Multiset.count_add,Multiset.count_cons,Multiset.count_replicate,
        Multiset.count_singleton]; split_ifs <;> omega
    exact ⟨shape ▸ oddBase k⟩
  | more m ih _ =>
    obtain ⟨w⟩ := ih
    rw [show k+2*(m+2)+3=(k+2*m+3)+4 by omega,show 2*(m+2)+3=(2*m+3)+4 by omega,←bulk_step]
    exact ⟨w.stepTwo⟩

theorem spectrum_expanded (k m : ℕ) :
    Planaric ((k+2*m+3)::(k+2*m+3)::(2*m+3)::
      (List.replicate k 4 ++ List.replicate (2*m+1) 3 ++ List.replicate m 2)) := by
  obtain ⟨w⟩ := of_frame k m
  apply w.planaric
  simp only [←Multiset.coe_add,Multiset.coe_replicate,bulk]

private def symmetricSeed : Frame 4 4 4 (bulk 0 0 2) := by
  refine ⟨5,Fan.support 3,Fan.support_planar _,0,1,3,?_,?_,?_,?_,?_,?_,[2,4],?_,?_⟩ <;> decide

private def Frame.stepThree (w : Frame a b c t) :
    Frame (a+6) (b+6) (c+6) (2::ₘ2::ₘ2::ₘ3::ₘ3::ₘ3::ₘ3::ₘ3::ₘ3::ₘt) := by
  let z := (((w.patch true).rotate.patch true).rotate.patch true).rotate
  exact ((z.single.rotate.single).rotate.single).rotate

private theorem symmetric_frames (m : ℕ) (ok : m≠1) :
    Nonempty (Frame (2*m+4) (2*m+4) (2*m+4) (bulk 0 m 2)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    match m with
    | 0 => exact ⟨symmetricSeed⟩
    | 1 => contradiction
    | m+2 =>
      by_cases e : m=1
      · subst m
        have shape : 2::ₘ2::ₘ2::ₘ3::ₘ3::ₘ3::ₘ3::ₘ3::ₘ3::ₘbulk 0 0 2 = bulk 0 3 2 := by decide
        exact ⟨shape ▸ symmetricSeed.stepThree⟩
      · obtain ⟨w⟩ := ih m (by omega) e
        rw [show 2*(m+2)+4=(2*m+4)+4 by omega,←bulk_step]
        exact ⟨w.stepTwo⟩

theorem odd_symmetric_expanded (m : ℕ) (ok : m≠1) :
    Planaric ((2*m+4)::(2*m+4)::(2*m+4)::
      (List.replicate (2*m+2) 3 ++ List.replicate m 2)) := by
  obtain ⟨w⟩ := symmetric_frames m ok
  apply w.planaric
  simp only [←Multiset.coe_add,Multiset.coe_replicate,bulk,Multiset.replicate_zero,zero_add]

end Combined.Spectrum
