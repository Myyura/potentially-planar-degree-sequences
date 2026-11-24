import TerminalOrder
import FullDegrees
import Augmentation

/-! Replay a complete labelled face certificate through the anonymous-state
algorithm, retaining its supplied face order and full multiplicities. -/
namespace Recognition.OrderInput
open Recognition.QuotientDP Recognition.FullBlocks Recognition.FullDegrees
open PlanarDegrees.Frontier PlanarDegrees.Topology Recognition.Witness

private theorem side_of_corners {a : Triangle n} {x y : Fin n} (ne : x≠y)
    (hx : x∈vertices a) (hy : y∈vertices a) : on a (x,y)=true := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
  have fin3 : ∀ i j : Fin 3, i=j ∨ i+1=j ∨ j+1=i := by decide
  rcases fin3 i j with rfl|rfl|rfl
  · contradiction
  · exact decide_eq_true ⟨i,Or.inl rfl⟩
  · exact decide_eq_true ⟨j,Or.inr rfl⟩

private theorem corners_of_dual (G : Gluing v f e) {z d} (h : incident G.dual d z) :
    (G.primal d).1∈(G.tri z).corners ∧ (G.primal d).2∈(G.tri z).corners := by
  have side_ := (G.faceSide z d).mp h
  simp only [PlanarDegrees.Topology.Triangle.sides,List.mem_cons,List.not_mem_nil,or_false] at side_
  rcases side_ with rfl|rfl|rfl
  · rcases G.abEnds z with eq|eq <;> simp [eq,PlanarDegrees.Topology.Triangle.corners]
  · rcases G.bcEnds z with eq|eq <;> simp [eq,PlanarDegrees.Topology.Triangle.corners]
  · rcases G.caEnds z with eq|eq <;> simp [eq,PlanarDegrees.Topology.Triangle.corners]

private theorem corner_link {v f} (C : ClosedTrace v f) (euler : (f+1)+4=2*(v+1))
    (fs : List (Triangle (v+1))) (q : Index fs ≃ Fin (f+1))
    (corner : ∀ i x, x∈vertices (faceAt fs i) ↔ x.val∈cornerNames (C.faces (q i))) : ConnectedLinks fs := by
  obtain ⟨G,hf,he⟩ := C.gluing
  have mk (x : Fin (v+1)) (i) : x∈vertices (faceAt fs (q.symm i)) ↔ x∈(G.tri i).corners := by
    rw [corner,q.apply_symm_apply,←hf]; simp only [List.mem_map]; constructor
    · rintro ⟨z,h,eq⟩; exact Fin.ext eq ▸ h
    · intro h; exact ⟨_,h,rfl⟩
  have simple (d) : (G.primal d).1≠(G.primal d).2 := by
    have h₁ := congrArg Prod.fst (he d)
    have h₂ := congrArg Prod.snd (he d)
    have lt := (C.ledger.sealed[d.val]).increasing
    intro eq; rw [eq] at h₁
    change (G.primal d).2.val=_ at h₁ h₂; omega
  intro x i j hi hj
  have w := G.links_connected euler x (q i) (q j) ((mk _ _).mp (by simpa using hi)) ((mk _ _).mp (by simpa using hj))
  have edge (z z') (h : G.link x z z') : Link fs x (q.symm z) (q.symm z') := by
    obtain ⟨d,inc_,across⟩ := h
    have hz : incident G.dual d z := by rcases across with eq|eq <;> simp [incident,eq]
    have hz' : incident G.dual d z' := by rcases across with eq|eq <;> simp [incident,eq]
    have appears {z} (hit : incident G.dual d z) : inc fs (q.symm z) (G.primal d) := by
      have vs := corners_of_dual G hit
      exact side_of_corners (simple d) ((mk _ _).mpr vs.1) ((mk _ _).mpr vs.2)
    exact ⟨G.primal d,inc_,appears hz,appears hz'⟩
  simpa using w.map q.symm edge

/-- Any ordering of the same normalized triangle rows is legal. The final
histogram is computed from the first colors in the selected order. -/
theorem reordered_run {v f} (C : ClosedTrace v f) (euler : (f+1)+4=2*(v+1))
    (fs : List (Triangle (v+1))) (q : Index fs ≃ Fin (f+1))
    (valid : ∀ a∈fs,Function.Injective a.v)
    (labels : ∀ i,row (faceAt fs i)=C.faces (q i))
    (perm : (fs.map FullDegrees.row).Perm ((List.finRange (f+1)).map C.faces)) :
    ∃ target U s, FullRun (f+1) target fs U s ∧ finished (f+1) s=true ∧
      target=(Finset.univ : Finset (Fin (v+1))).val.map (fun x : Fin (v+1) => simpleDegree (reds (rows fs)) x.val) := by
  have proper (i : Index fs) := valid _ (by rw [faceAt_get]; exact List.getElem_mem _ : faceAt fs i∈fs)
  have corners (i) (x : Fin (v+1)) : x∈vertices (faceAt fs i) ↔ x.val∈cornerNames (C.faces (q i)) := by
    rw [←labels]; exact (row_corner _ (proper i) _).symm
  have covered (x : Fin (v+1)) : ∃ a∈fs,x∈vertices a := by
    obtain ⟨j,h⟩ := C.used x
    refine ⟨faceAt fs (q.symm j),?_,(corners _ _).mpr (by simpa using h)⟩
    rw [faceAt_get]; exact List.getElem_mem _
  have eqp : (rows fs).Perm (sideTrace C.faces) := by
    simpa [rows,sideTrace,List.flatMap_map,Function.comp_def] using perm.flatMap_right Face.sides
  have paired (p : Side (v+1)) : FullBlocks.occurrences fs p=0 ∨ FullBlocks.occurrences fs p=2 := by
    by_cases eq : p.1=p.2
    · left
      have no : ¬ 0<FullBlocks.occurrences fs p := by
        intro pos
        obtain ⟨i,h⟩ := (occ_pos fs p).mp pos
        obtain ⟨k,ha|ha⟩ := of_decide_eq_true h <;> subst p <;> apply (by decide : ∀ j : Fin 3,j≠j+1) k <;> apply proper i
        · exact eq
        · exact eq.symm
      omega
    · have neq : p.1.val≠p.2.val := fun e => eq (Fin.ext e)
      have someKey : ∃ key : Edge, Represents p key := by
        rcases lt_or_gt_of_ne neq with low|high
        · exact ⟨⟨_,_,low⟩,Or.inl ⟨rfl,rfl⟩⟩
        · exact ⟨⟨_,_,high⟩,Or.inr ⟨rfl,rfl⟩⟩
      obtain ⟨key,rep⟩ := someKey
      rw [← count_rows fs valid rep]
      have counts := (eqp.map Event.edge).count_eq key
      change PlanarDegrees.Frontier.occurrences (rows fs) key=PlanarDegrees.Frontier.occurrences (sideTrace C.faces) key at counts
      rw [counts]; exact paired_iff_closed.mpr ⟨_,C.accepted,C.closed⟩ key
  have dual : ∀ i j, PlanarDegrees.Frontier.Walk (Dual fs) i j := by
    have lift (u w) (h : shared C.faces u w) : Dual fs (q.symm u) (q.symm w) := by
      obtain ⟨ne,e,hu,hw⟩ := h
      have limit : e.hi<v+1 := by
        have bound := C.bounded u
        have lt := (C.faces u).yz
        simp [sideNames,Face.sides] at hu; rcases hu with rfl|rfl|rfl <;> simp_all
        omega
      let p : Side (v+1) := (⟨e.lo,lt_trans e.increasing limit⟩,⟨e.hi,limit⟩)
      have rep : Represents p e := .inl ⟨rfl,rfl⟩
      apply (dual_iff _ _ _).mpr
      refine ⟨q.symm.injective.ne ne,p,(row_side _ (proper _) rep).mp ?_,(row_side _ (proper _) rep).mp ?_⟩
      · simpa [labels] using hu
      · simpa [labels] using hw
    intro i j
    have W := ((C.connected (q i)).symm (fun _ _ ⟨n,e,a,b⟩ => ⟨Ne.symm n,e,b,a⟩)).trans (C.connected (q j))
    simpa using W.map q.symm lift
  obtain ⟨target,U,s,run,done⟩ := TerminalOrder.realize_order fs valid covered paired dual (corner_link C euler fs q corners)
  have len : fs.length=f+1 := by simpa using perm.length_eq
  exact ⟨target,U,s,len ▸ run,len ▸ done,terminal_histogram run done⟩

end Recognition.OrderInput

namespace Recognition.OrderInput
open Recognition.QuotientDP Recognition.FullBlocks Recognition.FullDegrees
open PlanarDegrees.Frontier PlanarDegrees.Topology Recognition.Witness

/-- Convert the stored increasing face records directly to the three slots of
the state machine, choosing the colors from those same recorded edges. -/
def inputFaces {v f} (C : ClosedTrace v f) := (List.finRange (f+1)).map (fun i => fromFace (C.faces i) (C.bounded i))

theorem input_rows {v f} (C : ClosedTrace v f) : (inputFaces C).map FullDegrees.row=(List.finRange (f+1)).map C.faces := by
  simp [inputFaces,List.map_map,Function.comp_def,row_fromFace]

theorem original_run {v f} (C : ClosedTrace v f) (euler : (f+1)+4=2*(v+1)) :
    ∃ U s, FullRun (f+1) (witnessDegrees C : Multiset Nat) (inputFaces C) U s ∧ finished (f+1) s=true := by
  let fs := inputFaces C
  have len : fs.length=f+1 := by simp [fs,inputFaces]
  let q := (indexEquiv fs).trans (finCongr len)
  have valid (a) (h : a∈fs) : Function.Injective a.v := by
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
    exact fromFace_injective ..
  have eq (i : Index fs) : FullDegrees.row (faceAt fs i)=C.faces (q i) := by
    rw [faceAt_get]; simp [fs,inputFaces,q,row_fromFace]; rfl
  have traceEq : rows fs=sideTrace C.faces := by
    have listEq := input_rows C
    simpa only [List.flatMap_map,Function.comp_def,rows,sideTrace] using congrArg (List.flatMap Face.sides) listEq
  obtain ⟨target,U,s,run,done,budget⟩ := reordered_run C euler fs q valid eq ((input_rows C) ▸ List.Perm.refl _)
  have names : (List.finRange (v+1)).map Fin.val=List.range (v+1) := by apply List.ext_getElem <;> simp
  have every : (List.finRange (v+1) : Multiset (Fin (v+1)))=(Finset.univ : Finset (Fin (v+1))).val := by
    have eq : (List.finRange (v+1)).toFinset=Finset.univ := by ext; simp
    rw [←eq,List.toFinset_val,List.dedup_eq_self.mpr (List.nodup_finRange _)]
  have budgetEq : target=(witnessDegrees C : Multiset Nat) := by
    rw [budget,traceEq,←every,witnessDegrees,←names,List.map_map,←Multiset.map_coe]
    exact Multiset.map_congr rfl (fun x _ => ((replay_accurate C.accepted).redDegree x.val).symm)
  exact ⟨U,s,budgetEq ▸ run,done⟩

private def paint (col : Edge → Bool) (F : Face) : Face :=
  {F with redXY := col ⟨F.x,F.y,F.xy⟩,redXZ := col ⟨F.x,F.z,lt_trans F.xy F.yz⟩,redYZ := col ⟨F.y,F.z,F.yz⟩}

private theorem paint_consistent (col : Edge → Bool) (F : Face) {a : Event} (h : a∈(paint col F).sides) : a.red=col a.edge := by
  simp only [paint,Face.sides,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl <;> rfl

/-- Reorder the faces arbitrarily after giving each occurrence of an edge
its original first-occurrence color. This preserves every labelled degree. -/
theorem repainted_trace {v f} (C : ClosedTrace v f) (π : Equiv.Perm (Fin (f+1))) :
    ∃ D : ClosedTrace v f, (∀ i, cornerNames (D.faces i)=cornerNames (C.faces (π i))) ∧
      (∀ i, sideNames (D.faces i)=sideNames (C.faces (π i))) ∧ witnessDegrees D=witnessDegrees C ∧
      (∃ col : Edge → Bool, ∀ a∈sideTrace D.faces, a.red=col a.edge) := by
  classical
  let original := sideTrace C.faces
  let col (e : Edge) := decide (e ∈ reds original)
  let fs (i : Fin (f+1)) := paint col (C.faces (π i))
  have color (a) (h : a∈sideTrace fs) : a.red=col a.edge := by
    obtain ⟨i,_,h⟩ := List.mem_flatMap.mp h; exact paint_consistent _ _ h
  have plain : (sideTrace fs).map Event.edge=(List.finRange (f+1)).flatMap (fun j => sideNames (C.faces (π j))) := by
    simp only [sideTrace,List.map_flatMap]; rfl
  have order : ((List.finRange (f+1)).map π).Perm (List.finRange _) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).map π.injective) (List.nodup_finRange _)).mpr
    intro x; simpa using π.surjective x
  have perm : ((sideTrace fs).map Event.edge).Perm (original.map Event.edge) := by
    rw [plain]; simpa only [original,sideTrace,List.map_flatMap,List.flatMap_map,Function.comp_def,sideNames] using
      order.flatMap_right (fun i => sideNames (C.faces i))
  have pairs (e) : PlanarDegrees.Frontier.occurrences (sideTrace fs) e=0 ∨ PlanarDegrees.Frontier.occurrences (sideTrace fs) e=2 := by
    have count := perm.count_eq e
    change PlanarDegrees.Frontier.occurrences (sideTrace fs) e=PlanarDegrees.Frontier.occurrences original e at count
    rw [count]; exact paired_iff_closed.mpr ⟨_,C.accepted,C.closed⟩ e
  obtain ⟨s,acc,closed⟩ := paired_iff_closed.mp pairs
  have conn (i) : PlanarDegrees.Frontier.Walk (shared fs) 0 i := by
    have w := ((C.connected (π 0)).symm (fun _ _ ⟨ne,e,h,k⟩ => ⟨ne.symm,e,k,h⟩)).trans (C.connected (π i))
    have step (u t) (g : shared C.faces u t) : shared fs (π.symm u) (π.symm t) := by
      obtain ⟨ne,e,l,r⟩ := g
      exact ⟨π.symm.injective.ne ne,e,by simpa [fs,paint,sideNames,Face.sides] using l,
        by simpa [fs,paint,sideNames,Face.sides] using r⟩
    simpa using w.map π.symm step
  have cov (x : Fin (v+1)) : ∃ i, x.val∈cornerNames (fs i) := by
    obtain ⟨j,h⟩ := C.used x; exact ⟨π.symm j,by simpa [fs,paint,cornerNames] using h⟩
  let D : ClosedTrace v f := ⟨fs,fun i => C.bounded _,cov,conn,s,acc,closed⟩
  refine ⟨D,fun _ => rfl,fun _ => rfl,?_,col,color⟩
  have redEq : (reds (sideTrace fs)).Perm (reds original) := by
    apply (List.perm_ext_iff_of_nodup (reds_nodup _) (reds_nodup _)).mpr
    intro e; rw [ReverseTrace.red_mem _ _ color]
    change (e∈List.map Event.edge (sideTrace fs) ∧ decide (e∈reds original)=true) ↔ _
    simp only [decide_eq_true_eq,and_iff_right_iff_imp]
    intro h; exact perm.mem_iff.mpr (List.count_pos_iff.mp (reds_seen h))
  apply List.map_congr_left; intro x _
  change s.redDegree x=C.ledger.redDegree x
  rw [(replay_accurate acc).redDegree,(replay_accurate C.accepted).redDegree]
  exact redEq.countP_eq (touches · x)

theorem reordered_trace {v f} (C : ClosedTrace v f) (π : Equiv.Perm (Fin (f+1))) :
    ∃ D : ClosedTrace v f, (∀ i, cornerNames (D.faces i)=cornerNames (C.faces (π i))) ∧
      (∀ i, sideNames (D.faces i)=sideNames (C.faces (π i))) ∧ witnessDegrees D=witnessDegrees C := by
  obtain ⟨D,v,e,d,_⟩ := repainted_trace C π
  exact ⟨D,v,e,d⟩

end Recognition.OrderInput

namespace Recognition.OrderInput
open Recognition.QuotientDP Recognition.FullDegrees Recognition.Witness SparseBoundary
open PlanarDegrees.Frontier PlanarDegrees.Topology

theorem chosen_order_run {v f} (C : ClosedTrace v f) (π : Equiv.Perm (Fin (f+1)))
    (euler : (f+1)+4=2*(v+1)) {ds : List Nat} (degrees : (witnessDegrees C).Perm ds) :
    ∃ D : ClosedTrace v f, (∀ i, cornerNames (D.faces i)=cornerNames (C.faces (π i))) ∧
      (∀ i, sideNames (D.faces i)=sideNames (C.faces (π i))) ∧
      ∃ U s, FullRun (f+1) (ds : Multiset Nat) (inputFaces D) U s ∧ finished (f+1) s=true := by
  obtain ⟨D,vertices,edges,vals⟩ := reordered_trace C π
  obtain ⟨U,s,run,yes⟩ := original_run D euler
  have target : (witnessDegrees D : Multiset Nat)=(ds : Multiset Nat) := Multiset.coe_eq_coe.mpr (vals ▸ degrees)
  exact ⟨D,vertices,edges,U,s,target ▸ run,yes⟩

/-- A complete actual face-ordered recurrence for the project language on
inputs of order at least four. All labels are fixed across a witness run. -/
theorem full_iff_planaric (d : Nat) (ds : List Nat) (order : 4≤ds.length+1) :
    Planaric (d::ds) ↔ ∃ f, (f+1)+4=2*(ds.length+1) ∧ ∃ fs U, ∃ s : State (ds.length+1),
      FullRun (f+1) ((d::ds) : Multiset Nat) fs U s ∧ finished (f+1) s=true := by
  constructor
  · intro yes
    obtain ⟨f,r,checked⟩ := (Augment.face_certificate_iff d ds order).mp yes
    obtain ⟨_,euler,_,C,degrees,_⟩ := TraceCheck.verify_sound _ _ checked
    obtain ⟨U,s,run,done⟩ := original_run C euler
    exact ⟨f,euler,inputFaces C,U,s,(Multiset.coe_eq_coe.mpr degrees) ▸ run,done⟩
  · rintro ⟨f,euler,fs,U,s,run,done⟩
    obtain ⟨r,checked⟩ := full_certificate (d::ds) run done order euler
    exact TracePlanarity.verify_planaric checked

end Recognition.OrderInput

namespace Recognition.OrderInput
open Recognition.QuotientDP Recognition.FullBlocks Recognition.FullDegrees Recognition.Witness
open PlanarDegrees.Frontier PlanarDegrees.Topology

/-- With a common color for the two records of each edge, an arbitrary
permutation of the literal face records gives a successful run with those
exact records and the original degree multiset. -/
theorem literal_run {v f} (C : ClosedTrace v f) (euler : (f+1)+4=2*(v+1))
    (col : Edge → Bool) (color : ∀ a∈sideTrace C.faces,a.red=col a.edge)
    (seq : List Face) (perm : seq.Perm (List.ofFn C.faces)) :
    ∃ fs U, ∃ s : State (v+1), fs.map FullDegrees.row=seq ∧
      FullRun (f+1) (witnessDegrees C : Multiset Nat) fs U s ∧ finished (f+1) s := by
  classical
  rw [List.ofFn_eq_map] at perm
  have lift : Relation.Comp (· = List.map C.faces ·) List.Perm seq (List.finRange (f+1)) := by
    rw [List.eq_map_comp_perm]; exact perm
  obtain ⟨ids,withIds,allIds⟩ := lift
  let pack (i : Fin (f+1)) := fromFace (C.faces i) (C.bounded i)
  let fs := ids.map pack
  have records : fs.map FullDegrees.row=seq := by simp [fs,List.map_map,Function.comp_def,pack,row_fromFace,withIds]
  have valid (a) (mem : a∈fs) : Function.Injective a.v := by
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp mem
    exact fromFace_injective ..
  let atId : Fin ids.length ≃ Fin (f+1) := Equiv.ofBijective ids.get
    ⟨(allIds.nodup_iff.mpr (List.nodup_finRange _)).injective_get,
      List.get_surjective_iff.mpr (fun x => allIds.mem_iff.mpr (List.mem_finRange x))⟩
  let q := ((indexEquiv fs).trans (finCongr (by simp [fs] : fs.length=ids.length))).trans atId
  have labels (i : Index fs) : FullDegrees.row (faceAt fs i) = C.faces (q i) := by
    rw [faceAt_get]; simp [fs,pack,q,atId,row_fromFace]; rfl
  obtain ⟨target,U,s,run,done,want⟩ := reordered_run C euler fs q valid labels (records ▸ perm)
  have words : (rows fs).Perm (sideTrace C.faces) := by
    have same := (records ▸ perm : (fs.map FullDegrees.row).Perm _).flatMap_right Face.sides
    simpa [FullDegrees.rows,sideTrace,List.flatMap_map,Function.comp_def] using same
  have redEq : (reds (rows fs)).Perm (reds (sideTrace C.faces)) := by
    apply (List.perm_ext_iff_of_nodup (reds_nodup _) (reds_nodup _)).mpr
    intro e
    rw [ReverseTrace.red_mem _ col (fun a h => color a (words.mem_iff.mp h)),ReverseTrace.red_mem _ col color]
    exact and_congr (words.map Event.edge).mem_iff Iff.rfl
  have names : (List.finRange (v+1)).map Fin.val=List.range (v+1) := by apply List.ext_getElem <;> simp
  have every : (List.finRange (v+1) : Multiset (Fin (v+1)))=(Finset.univ : Finset (Fin (v+1))).val := by
    have eq : (List.finRange (v+1)).toFinset=Finset.univ := by ext; simp
    rw [←eq,List.toFinset_val,List.dedup_eq_self.mpr (List.nodup_finRange _)]
  have budget : target=(witnessDegrees C : Multiset Nat) := by
    rw [want,←every,witnessDegrees,←names,List.map_map,←Multiset.map_coe]
    apply Multiset.map_congr rfl; intro x _
    exact (redEq.countP_eq (touches · x.val)).trans ((replay_accurate C.accepted).redDegree x.val).symm
  exact ⟨fs,U,s,records,budget ▸ run,done⟩

end Recognition.OrderInput
