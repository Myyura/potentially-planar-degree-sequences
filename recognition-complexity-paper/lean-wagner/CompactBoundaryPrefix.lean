import CompactBoundaryRibbon
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import LeanPool.K5MinorFreeChoosability.Wagner.WagnerA

namespace Recognition.CompactBoundary
open LeanPool.K5MinorFreeChoosability Equiv Equiv.Perm
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep PlanarDegrees.Topology
open Recognition.Overlay Recognition.OverlayMinor Recognition.OverlayCoverage

/-- Join the components inside a planar supergraph; the new edges can
be identified and discarded from the decoded drawing. -/
theorem connected_extension {V : Type} [Finite V] [Nonempty V] (G : SimpleGraph V)
    (flat : IsPlanar G) : ∃ H : SimpleGraph V,G≤H ∧ IsPlanar H ∧ H.Connected ∧
      Nat.card H.edgeSet≤Nat.card G.edgeSet+Nat.card V-1 := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨M,sub,maximal⟩ := Augment.exists_maximal G flat
  obtain ⟨T,t,tree⟩ := (Augment.maximal_connected maximal).exists_isTree_le
  let H := G⊔T
  have upper : H≤M := sup_le sub t
  refine ⟨H,le_sup_left,maximal.1.mono upper,tree.connected.mono le_sup_right,?_⟩
  have treeSize := tree.card_edgeFinset
  have count : H.edgeFinset.card≤G.edgeFinset.card+T.edgeFinset.card := by
    change (G⊔T).edgeFinset.card≤_
    rw [SimpleGraph.edgeFinset_sup]
    exact Finset.card_union_le .. 
  simp only [SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card] at count treeSize
  omega

private theorem shadow_edges (fs : List Face) (s : Inventory) :
    Nat.card (shadow fs s).edgeSet≤(edges fs s).length := by
  classical
  let V := Nodes fs s
  let raw := edges fs s
  let es := (raw.map fun p => s(p.1,p.2)).toFinset
  have mem (u : Sym2 V) (h : u∈(shadow fs s).edgeSet) :
      Sym2.map Subtype.val u∈es := by
    induction u using Sym2.inductionOn with
    | _ a b =>
      change (shadow fs s).Adj a b at h
      rcases h.2 with f|g
      · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_,f,rfl⟩)
      · apply List.mem_toFinset.mpr
        exact List.mem_map.mpr ⟨(b.val,a.val),g,Sym2.eq_swap⟩
  let send (u : (shadow fs s).edgeSet) : ↥es := ⟨Sym2.map Subtype.val u.val,mem _ u.property⟩
  have inj : Function.Injective send := fun a b h =>
    Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h))
  have bound := Nat.card_le_card_of_injective send inj
  rw [Nat.card_eq_fintype_card (α:=↥es),Fintype.card_coe] at bound
  exact bound.trans (by simpa [es,raw] using (List.toFinset_card_le (raw.map fun p => s(p.1,p.2))))

/-- The 22b bound for an actual connected plane supergraph of the anonymous
prefix overlay. Its adjacency relation contains the entire original shadow. -/
theorem extension_at_prefix {v f : Nat} (C : ClosedTrace v f)
    (terminal : (f+1)+4=2*(v+1)) (rd todo : List Face) (p : (rd++todo).Perm (List.ofFn C.faces))
    (s : Inventory) (ok : replay (rd.flatMap Face.sides)=some s) (nonempty : s.pending≠[]) :
    ∃ H : SimpleGraph (Nodes rd s),shadow rd s≤H ∧ IsPlanar H ∧ H.Connected ∧
      Nat.card H.edgeSet ≤ 22*(activeNames s).eraseDups.length := by
  classical
  obtain ⟨e,ep⟩ := List.exists_mem_of_ne_nil _ nonempty
  have kept : e∈retained s := by simp [retained,ep]
  let _ : Nonempty (Nodes rd s) := ⟨⟨.point e, by simp [vertices,kept]⟩⟩
  let V := Nodes rd s
  let _ : Fintype V := Fintype.ofFinset (vertices rd s).toFinset (fun _ => List.mem_toFinset)
  have size : Nat.card V≤(vertices rd s).length := by
    have eq : Fintype.card V=(vertices rd s).toFinset.card :=
      Fintype.card_ofFinset (p:={x | x∈vertices rd s}) (vertices rd s).toFinset (fun _ => List.mem_toFinset)
    rw [Nat.card_eq_fintype_card,eq]; exact List.toFinset_card_le _
  change Nat.card {a // a∈vertices rd s}≤_ at size
  obtain ⟨H,sub,flat,conn,h⟩ := connected_extension (shadow rd s) (TraceOverlay.prefix_planar C terminal rd todo p ok)
  have es := shadow_edges rd s
  have full := edge_budget C terminal rd todo p s ok
  exact ⟨H,sub,flat,conn,by omega⟩


/-- One prefix supplies both the connected plane supergraph and the compact
code for its marked rotation system. Marks are in the decoded vertex and
edge order; active counter fields may occur in any corresponding order. -/
theorem prefix_record {v f : Nat} (C : ClosedTrace v f)
    (terminal : (f+1)+4=2*(v+1)) (rd todo : List Face) (p : (rd++todo).Perm (List.ofFn C.faces))
    (s : Inventory) (ok : replay (rd.flatMap Face.sides)=some s) (nonempty : s.pending≠[])
    (weight : activeCost s * activeCost s≤220^2*(v+1)) :
    ∃ H : SimpleGraph (Nodes rd s),shadow rd s≤H ∧ H.Connected ∧
    ∃ M : PlaneMap H, ∃ e : H.Dart ≃ Fin (2*Nat.card H.edgeSet),
    ∃ ts : List Tag, ∃ other : List Bool, ∃ R : RibbonCode.Rows,
      R.length=2*Nat.card H.edgeSet ∧ (∀ x : H.Dart,R.rotation (e x).val=some (e (M.rot x)).val) ∧
      (∀ x : H.Dart,R.pairing (e x).val=some (e x.symm).val) ∧
      ∀ (vs es : List Tag) (ds : List Nat),vs.length=cycleCount M.rot → es.length=Nat.card H.edgeSet →
        ds.length=vs.count original → ds.Perm ((activeNames s).eraseDups.map s.redDegree) →
        readPlane (packPlane ts other vs es ds)=some (some ⟨R,vs,es,ds⟩) ∧
        (planeFields ts other vs es).length≤14*Nat.card H.edgeSet+5 ∧
        (packPlane ts other vs es ds).length≤100000*ceilRoot (v+1) := by
  classical
  obtain ⟨H,sub,⟨M⟩,conn,small⟩ := extension_at_prefix C terminal rd todo p s ok nonempty
  let _ : Fintype (Nodes rd s) := Fintype.ofFinset (vertices rd s).toFinset (fun _ => List.mem_toFinset)
  let e := Nat.card H.edgeSet
  have card : Fintype.card H.Dart=2*e := by
    rw [←Nat.card_eq_fintype_card,card_dart_eq_two_mul H,←card_edgeSet_eq_cycleCount]
  let z : H.Dart ≃ Fin (2*e) := (Fintype.equivFin H.Dart).trans (finCongr card)
  let r := z.permCongr M.rot
  let a := z.permCongr (dartSymm H)
  have joint : ∀ i j,compSetoid r a i j := by
    have one : Subsingleton (Quotient (compSetoid M.rot (dartSymm H))) :=
      Finite.card_le_one_iff_subsingleton.mp (numComponents_le_one_of_connected M.isRotationSystem conn)
    intro i j
    have related : compSetoid M.rot (dartSymm H) (z.symm i) (z.symm j) := Quotient.exact (one.elim _ _)
    simpa [r,a] using (compSetoid_permCongr_iff z M.rot (dartSymm H) _ _).mp related
  have c : cycleCount r=cycleCount M.rot := cycleCount_permCongr _ _
  have verts : cycleCount r≤e+1 := by
    rw [c,cycleCount_eq_card_nonisolated M.isRotationSystem]
    exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans conn.card_vert_le_card_edgeSet_add_one
  have undo (x) : a (a x)=x := by simp [a,permCongr_apply,dartSymm]
  have moved (x) : a x≠x := by
    intro h
    apply (z.symm x).symm_ne
    simpa [a,permCongr_apply,dartSymm] using congrArg z.symm h
  have planar : eulerDefect r a=0 := by simpa [r,a,eulerDefect_permCongr] using M.eulerDefect_eq_zero
  obtain ⟨ts,oth,R,o,size,rotate,mate,pack⟩ := plane_record (n:=v+1) (by omega) r a undo moved planar joint verts
  refine ⟨H,sub,conn,M,z.trans o,ts,oth,R,size,?_,?_,?_⟩
  · intro x; change R.rotation (o (z x)).val=some (o (z (M.rot x))).val; simpa [r,permCongr_apply] using rotate (o (z x))
  · intro x; change R.pairing (o (z x)).val=some (o (z x.symm)).val; simpa [a,permCongr_apply,dartSymm] using mate (o (z x))
  · intro vs es ds hv he hd perm
    obtain ⟨decode,width,bound⟩ := pack vs es ds (hv.trans c.symm) he hd
    have len := perm.length_eq
    simp only [List.length_map] at len
    have sum := (perm.map cost).sum_eq
    change (ds.map cost).sum=(((activeNames s).eraseDups.map s.redDegree).map cost).sum at sum
    have sw : (ds.map cost).sum=activeCost s := by simpa [activeCost,List.map_map,Function.comp_def] using sum
    exact ⟨decode,width,bound (by change Nat.card H.edgeSet≤_;omega) (by rw [sw,pow_two];exact weight)⟩

end Recognition.CompactBoundary
