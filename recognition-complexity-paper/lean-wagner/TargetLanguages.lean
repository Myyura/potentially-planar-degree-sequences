import Augmentation
import PolytopeDual
import HardnessResult
import SATCost

/-! The ordinary (unpromised) languages of maximal planar degree rows and
complete cubic dual face-size rows. All positive instances use the same
bounded rotation certificate, including the tetrahedron and the small
complete graphs in the maximal-planar language. -/
namespace Recognition.TargetLanguages
open SparseBoundary Recognition.Wagner LeanPool.K5MinorFreeChoosability
open PolytopeDual Equiv Equiv.Perm

def MaximalRow (ds : List Nat) : Prop :=
  ∃ G : Graph ds.length, G.Realizes ds ∧ Maximal IsPlanar (toSimple G)

def PolyhedralRow (ds : List Nat) : Prop := 4≤ds.length ∧ HasCubicDual ds

theorem handshake (G : Graph ds.length) (realizes : G.Realizes ds) :
    ds.sum=2*Nat.card (toSimple G).edgeSet := by
  classical
  have sum := (toSimple G).sum_degrees_eq_twice_card_edges
  have each (i : Fin ds.length) : (toSimple G).degree i=ds[i] := by
    rw [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
    exact (neighbor_count G i).trans (realizes i)
  simp_rw [each] at sum
  have s : (∑ i : Fin ds.length, ds[i])=ds.sum := by
    rw [←List.sum_ofFn]; congr 1; apply List.ext_getElem <;> simp
  simpa only [s,Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card] using sum

def guardRow (ds : List Nat) : Bool :=
  if ds.length<4 then decide (ds.sum=2 * Nat.choose ds.length 2)
  else decide (ds.sum+12=6*ds.length)

private theorem guard_iff (G : Graph ds.length) (realizes : G.Realizes ds)
    (m : Maximal IsPlanar (toSimple G)) : guardRow ds=true := by
  classical
  have sum := handshake G realizes
  unfold guardRow
  split
  next small =>
    have flat : IsPlanar (⊤ : SimpleGraph (Fin ds.length)) := isPlanar_of_card_le_four
      (S:=Finset.univ) (fun _ _ _=>Finset.mem_univ _) (by simpa using small.le)
    have eq : toSimple G=⊤ := top_unique (m.2 flat le_top)
    rw [eq,Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin] at sum
    exact decide_eq_true sum
  next large =>
    let _ : Nonempty (Fin ds.length) := ⟨⟨0,by omega⟩⟩
    obtain ⟨M⟩ := m.1
    have edges := (Augment.maximal_tight M m (Augment.maximal_connected m) (by simp;omega)).2
    rw [Nat.card_fin] at edges
    exact decide_eq_true (by omega)

theorem maximal_row_iff (ds : List Nat) : MaximalRow ds ↔ guardRow ds=true ∧ Planaric ds := by
  classical
  constructor
  · rintro ⟨G,r,m⟩
    exact ⟨guard_iff G r m, G,r,(planar_iff_rotation G).mpr m.1⟩
  rintro ⟨test,G,r,flat⟩
  obtain ⟨H,le,m⟩ := Augment.exists_maximal (toSimple G) ((planar_iff_rotation G).mp flat)
  have eqEdges : (toSimple G).edgeFinset.card=H.edgeFinset.card := by
    have sum:=handshake G r
    rw [Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card] at sum
    unfold guardRow at test
    split at test
    next small =>
      have topFlat : IsPlanar (⊤ : SimpleGraph (Fin ds.length)) := isPlanar_of_card_le_four
        (S:=Finset.univ) (fun _ _ _=>Finset.mem_univ _) (by simpa using small.le)
      have eq : H=⊤ := top_unique (m.2 topFlat le_top)
      have cnt : Nat.card H.edgeSet=ds.length.choose 2 := by
        rw [eq,Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card,
          SimpleGraph.card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin]
      rw [Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card] at cnt
      have := of_decide_eq_true test;omega
    next big =>
      let _ : Nonempty (Fin ds.length) := ⟨⟨0,by omega⟩⟩
      obtain ⟨M⟩ := m.1
      have edges := (Augment.maximal_tight M m (Augment.maximal_connected m) (by simp;omega)).2
      rw [Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card,Nat.card_fin] at edges
      have := of_decide_eq_true test; omega
  have eq : toSimple G=H := SimpleGraph.edgeFinset_inj.mp
    (Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono le) eqEdges.ge)
  exact ⟨G,r,eq ▸ m⟩

private theorem cubic_card {D : Type*} [Finite D] (p : Perm D)
    (cubic : ∀ c : Cell p, cellSize p c=3) : Nat.card D=3*cycleCount p := by
  classical
  let _ := Fintype.ofFinite (Cell p)
  let f : D → Cell p := Quotient.mk (SameCycle.setoid p)
  have mass := Nat.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Nat.card_sigma] at mass
  have eq (c : Cell p) : Nat.card {t // f t=c}=3 := cubic c
  simp only [eq,Finset.sum_const,Finset.card_univ,smul_eq_mul] at mass
  change Nat.card D=3*Nat.card (Cell p)
  rw [Nat.card_eq_fintype_card (α:=Cell p)]; omega

theorem polyhedral_row_iff (ds : List Nat) :
    PolyhedralRow ds ↔ 4≤ds.length ∧ ds.sum+12=6*ds.length ∧ Planaric ds := by
  classical
  constructor
  · rintro ⟨n,h⟩
    have yes := dual_spectrum_sound h
    obtain ⟨G,M,con,flat,cubic,bij,sizes⟩ := h
    have r : G.Realizes ds := by
      intro v
      obtain ⟨c,rfl⟩ := bij.2 v
      exact (neighbor_count G _).symm.trans ((dual_face_size M c).symm.trans (sizes c))
    have sum := handshake G r
    have count := cubic_card _ cubic
    have vertices : cycleCount (dualRot M * dartSymm (toSimple G))=ds.length :=
      (Nat.card_congr (Equiv.ofBijective _ bij)).trans (Nat.card_fin _)
    have darts := card_dart_eq_two_mul (toSimple G)
    unfold eulerDefect at flat
    rw [con,vertices,←card_edgeSet_eq_cycleCount] at flat
    rw [←card_edgeSet_eq_cycleCount] at darts
    exact ⟨n,by omega,yes⟩
  · rintro ⟨n,tight,G,r,flat⟩
    have test : guardRow ds=true := by simp [guardRow,show ¬ds.length<4 by omega,tight]
    obtain ⟨K,rk,m⟩ := (maximal_row_iff ds).mpr ⟨test,G,r,flat⟩
    obtain ⟨M⟩ := m.1
    let _ : Nonempty (Fin ds.length) := ⟨⟨0,by omega⟩⟩
    have facts := Augment.maximal_tight M m (Augment.maximal_connected m) (by simpa using n)
    have low (v) : 2≤Nat.card {u // (toSimple K).Adj v u} := (by decide : 2≤3).trans (facts.1 v)
    have nbr (v) : ∃ u, (toSimple K).Adj v u := by
      obtain ⟨u⟩ := (Nat.card_pos_iff.mp (by have := low v;omega : 0<Nat.card {u // (toSimple K).Adj v u})).1
      exact ⟨u.val,u.property⟩
    exact ⟨n,K,M,(numClasses_congr (component_iff M)).trans (tight_faces M low inferInstance facts.2).1,
      dual_spherical M,tight_dual_cubic M low inferInstance facts.2,(faceEquiv M nbr).bijective,
      fun c => (dual_face_size M c).trans ((neighbor_count K _).trans (rk _))⟩

def checkMaximal (ds : List Nat) (w : List Bool) := guardRow ds && RawWire.verify ds w

def checkPolyhedral (ds : List Nat) (w : List Bool) :=
  decide (4≤ds.length ∧ ds.sum+12=6*ds.length) && RawWire.verify ds w

theorem maximal_certificate (ds : List Nat) : MaximalRow ds ↔
    ∃ w : List Bool,w.length≤5*(ds.length+1)^3 ∧ checkMaximal ds w=true := by
  rw [maximal_row_iff,RawWire.bounded_certificate]
  simp only [checkMaximal,Bool.and_eq_true]
  grind

theorem polyhedral_certificate (ds : List Nat) : PolyhedralRow ds ↔
    ∃ w : List Bool,w.length≤5*(ds.length+1)^3 ∧ checkPolyhedral ds w=true := by
  rw [polyhedral_row_iff,RawWire.bounded_certificate]
  simp only [checkPolyhedral,Bool.and_eq_true,decide_eq_true_eq]
  grind

private theorem output (bs : List Bool) : ∃ I : Reduction.Instance,
    (SATCost.run bs).1=Wire.degrees (Reduction.reduceInstance I) := by
  rw [SATCost.run_value]
  cases h : SATBridge.readSAT bs with
  | none =>
    let I : Reduction.Instance := ⟨[],0,0⟩
    have bad : ¬Reduction.Valid I := by intro v;have := v.1;change 0<0 at this;omega
    exact ⟨I,by simp only [SATBridge.satWire,h,Reduction.reduce_invalid I bad];rfl⟩
  | some x => exact ⟨SATBridge.instanceOfSAT x,by simp [SATBridge.satWire,h,Wire.reduceBits,Wire.reduceRow,Wire.source_round_trip]⟩

theorem reductions (bs : List Bool) :
    let out := (SATCost.run bs).1
    (SATBridge.SATLanguage bs ↔ Wire.degreeLanguage MaximalRow out) ∧
    (SATBridge.SATLanguage bs ↔ Wire.degreeLanguage HasStackedRealization out) ∧
    (SATBridge.SATLanguage bs ↔ Wire.degreeLanguage PolyhedralRow out) := by
  obtain ⟨I,row⟩ := output bs
  let ds := Reduction.reduceInstance I
  have valid := Reduction.reduce_promise I
  change Reduction.TableValid ds at valid
  have non : ds≠[] := by intro h;have := valid.1;simp [h] at this
  have n := valid.1
  have guard : guardRow ds=true := by simp [guardRow,show ¬ds.length<4 by omega,valid.2.1]
  have sat := (SATBridge.sat_wire_iff bs).symm
  rw [←SATCost.run_value,row] at sat
  simp only [row,Wire.degreeLanguage,Wire.degrees_round_trip,Option.some.injEq,exists_eq_left']
  change (_ ↔ ds≠[] ∧ MaximalRow ds) ∧ (_ ↔ ds≠[] ∧ HasStackedRealization ds) ∧
    (_ ↔ ds≠[] ∧ PolyhedralRow ds)
  simp only [Wire.degreeLanguage,Wire.degrees_round_trip,Option.some.injEq,exists_eq_left'] at sat
  have sat' : SATBridge.SATLanguage bs ↔ Planaric ds := sat.trans (and_iff_right non)
  exact ⟨sat'.trans (by simp [maximal_row_iff,non,guard]),sat'.trans (by
    rw [and_iff_right non];exact (planaric_reduction_iff I).trans (stacked_reduction_iff I).symm),
    sat'.trans (by simp [polyhedral_row_iff,non,valid.2.1,show 4≤ds.length by omega])⟩

end Recognition.TargetLanguages
