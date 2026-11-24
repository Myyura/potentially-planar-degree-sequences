import CompactBoundaryPrefix
import OverlayRead
import CatalogueResult
import Mathlib.Data.List.Nodup

/-! Canonical discovery order for the compact vertex, edge and counter
fields. It depends only on the two recovered dart permutations. -/
namespace Recognition.CompactBoundary
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep PlanarDegrees.Topology
open Recognition.Overlay Recognition.OverlayMinor Recognition.OverlayCoverage

def orbitKey (row : Nat → Option Nat) (n : Nat) (i : Fin n) : Fin n :=
  let xs := List.finRange n
  let next (d : Fin n) := (row d.val).bind fun j => if h : j<n then some (⟨j,h⟩ : Fin n) else none
  OrbitTable.key (OrbitTable.run xs (xs.map fun d => (d,(next d).getD d))) i

private theorem orbitKey_iff {n} (row : Nat → Option Nat) (rot : Perm (Fin n))
    (read : ∀ i : Fin n,row i.val=some (rot i).val) (i j : Fin n) :
    orbitKey row n i=orbitKey row n j ↔ SameCycle rot i j := by
  unfold orbitKey
  simp only [read,Option.bind_some,Fin.is_lt,↓reduceDIte,Fin.eta,Option.getD_some]
  apply OrbitTable.generated _ List.mem_finRange _ (SameCycle.setoid rot)
  · rintro z hz; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hz
    exact sameCycle_apply_right.mpr (SameCycle.refl _ _)
  · intro s h
    exact fun _ _ => sameCycle_of_step s (fun a => h (a,rot a) (List.mem_map.mpr ⟨a,List.mem_finRange _,rfl⟩))

def first {n} (k : Fin n → Fin n) (i : Fin n) :=
  ((List.finRange n).find? (fun j => k j==k i)).getD i

def reps {n} (k : Fin n → Fin n) := ((List.finRange n).map (first k)).eraseDups

private theorem found {n} (k : Fin n → Fin n) (i : Fin n) :
    (List.finRange n).find? (fun j => k j==k i)=some (first k i) := by
  unfold first
  cases h : (List.finRange n).find? (fun j => k j==k i) with
  | none => exact False.elim ((List.find?_eq_none.mp h) i (List.mem_finRange _) (by simp))
  | some j => rfl

private theorem same_key {n} (k : Fin n → Fin n) (i : Fin n) : k (first k i)=k i :=
  by
  have h := List.find?_some (found k i)
  exact beq_iff_eq.mp h

private theorem first_iff {n} (k : Fin n → Fin n) (i j : Fin n) :
    first k i=first k j ↔ k i=k j := by
  constructor
  · intro e; rw [←same_key k i,←same_key k j,e]
  · intro e; have h := found k i; rw [e,found] at h; exact (Option.some.inj h).symm

private theorem rep_mem {n} (k : Fin n → Fin n) (i : Fin n) : first k i∈reps k := by
  simp only [reps,List.mem_eraseDups,List.mem_map]; exact ⟨i,List.mem_finRange _,rfl⟩

private theorem rep_fixed {n} (k : Fin n → Fin n) {i} (h : i∈reps k) : first k i=i := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp h)
  exact (first_iff ..).mpr (same_key k j)

private theorem reps_card {n} {X : Type} [Finite X] (k : Fin n → Fin n) (name : Fin n → X)
    (onto : Function.Surjective name) (same : ∀ i j,k i=k j ↔ name i=name j) :
    (reps k).length=Nat.card X := by
  classical
  have nd : ((reps k).map name).Nodup := by
    apply (List.nodup_map_iff_inj_on (Overlay.distinct_names _)).mpr
    intro i hi j hj e
    rw [←rep_fixed k hi,←rep_fixed k hj]
    exact (first_iff ..).mpr ((same ..).mpr e)
  let _ := Fintype.ofFinite X
  have full : ((reps k).map name).toFinset=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro x; obtain ⟨i,rfl⟩ := onto x
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨first k i,rep_mem k i,(same ..).mp (same_key k i)⟩)
  have eq := List.toFinset_card_of_nodup nd
  rw [full,Finset.card_univ,List.length_map] at eq
  simpa [Nat.card_eq_fintype_card] using eq.symm

def fieldAt {n} (ids : List (Fin n)) (fields : List α) (i : Fin n) := fields[ids.idxOf i]?

private theorem field_map {n} (ids : List (Fin n)) (f : Fin n → α) {i : Fin n} (mem : i∈ids) :
    fieldAt ids (ids.map f) i=some (f i) := by
  have h := List.idxOf_lt_length_of_mem mem
  simp [fieldAt,h,List.getElem_idxOf h]

def PlaneDrawing.vKey (P : PlaneDrawing) (n : Nat) := orbitKey P.ribbon.rotation n
def PlaneDrawing.eKey (P : PlaneDrawing) (n : Nat) := orbitKey P.ribbon.pairing n

def PlaneDrawing.vTag (P : PlaneDrawing) {n} (i : Fin n) :=
  fieldAt (reps (P.vKey n)) P.vertexTags (first (P.vKey n) i)

def PlaneDrawing.eTag (P : PlaneDrawing) {n} (i : Fin n) :=
  fieldAt (reps (P.eKey n)) P.edgeTags (first (P.eKey n) i)

def PlaneDrawing.active (P : PlaneDrawing) (n : Nat) :=
  (reps (P.vKey n)).filter (fun i => P.vTag i==some original)

def PlaneDrawing.red (P : PlaneDrawing) {n} (i : Fin n) : Option Nat := do
  guard (P.vTag i==some original)
  fieldAt (P.active n) P.redDegrees (first (P.vKey n) i)

def vertexRole (s : Inventory) {A : Type} : Node A → Tag
  | .vertex _ => original
  | .point e => if e∈s.pending then (false,true) else (true,false)
  | .centre _ => (true,true)

def rawName {A : Type} : Node A → Nat
  | .vertex v => v
  | _ => 0

def roleNumber (p : Tag) := 2*p.1.toNat+p.2.toNat

private theorem role_num (s : Inventory) {A} (x : Node A) :
    roleNumber (vertexRole s x)=(role s x).val := by
  cases x with
  | vertex _ | centre _ => rfl
  | point e => by_cases h : e∈s.pending <;> simp [roleNumber,vertexRole,role,h]

private theorem is_original (s : Inventory) {A} (x : Node A) :
    vertexRole s x=original ↔ x=Node.vertex (rawName x) := by
  cases x with
  | vertex _ | centre _ => simp [vertexRole,rawName,original]
  | point e => by_cases h : e∈s.pending <;> simp [vertexRole,rawName,h,original]

def bridgeTag : Tag := (true,false)
def primalTag : Tag := (false,false)
def spokeTag : Tag := (false,true)

noncomputable def edgeRole {fs s} (x y : Nodes fs s) : Tag := by
  classical
  exact if (shadow fs s).Adj x y then
    (if vertexRole s x.val=original ∨ vertexRole s y.val=original then primalTag else spokeTag)
  else bridgeTag

private theorem edge_flip {fs s} (x y : Nodes fs s) : edgeRole x y=edgeRole y x := by
  by_cases h : (shadow fs s).Adj x y
  · simp [edgeRole,h,h.symm,or_comm]
  · have no : ¬(shadow fs s).Adj y x := fun q => h q.symm
    simp [edgeRole,h,no]


private theorem vertices_data {n fs s} (k : Fin n → Fin n) (tail : Fin n → Nodes fs s)
    (onto : Function.Surjective tail) (same : ∀ i j,k i=k j ↔ tail i=tail j) :
    let F := fun i => vertexRole s (tail i).val
    let live := (reps k).filter (fun i => F i==original)
    let names := live.map (fun i => rawName (tail i).val)
    names.Perm (activeNames s).eraseDups := by
  dsimp only
  let live := (reps k).filter (fun i => vertexRole s (tail i).val==original)
  have hit {i : Fin n} (hi : i∈live) : (tail i).val=Node.vertex (rawName (tail i).val) :=
    (is_original s _).mp (beq_iff_eq.mp (List.mem_filter.mp hi).2)
  have active_iff (x : Nat) : (Node.vertex x : Node (Patch fs (retained s)))∈vertices fs s ↔
      x∈(activeNames s).eraseDups := by simp [vertices]
  apply (List.perm_ext_iff_of_nodup _ (Overlay.distinct_names _)).mpr
  · intro x
    constructor
    · rintro mem
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp mem
      apply (active_iff _).mp
      rw [←hit hi]; exact (tail i).property
    · intro mem
      obtain ⟨i,eq⟩ := onto ⟨Node.vertex x,(active_iff x).mpr mem⟩
      have rep := (same ..).mp (same_key k i)
      have val : (tail (first k i)).val=.vertex x := congrArg Subtype.val (rep.trans eq)
      exact List.mem_map.mpr ⟨first k i,List.mem_filter.mpr ⟨rep_mem k i,by simp [val,vertexRole]⟩,by simp [val,rawName]⟩
  · apply (List.nodup_map_iff_inj_on ((Overlay.distinct_names _).filter _)).mpr
    intro i hi j hj e
    have sameVal : tail i=tail j := Subtype.ext ((hit hi).trans ((congrArg Node.vertex e).trans (hit hj).symm))
    rw [←rep_fixed k (List.mem_filter.mp hi).1,←rep_fixed k (List.mem_filter.mp hj).1]
    exact (first_iff ..).mpr ((same ..).mpr sameVal)

private theorem nonisolated {fs s} (H : SimpleGraph (Nodes fs s)) (conn : H.Connected)
    (open_ : s.pending≠[]) : ∀ x,∃ y,H.Adj x y := by
  obtain ⟨e,ep⟩ := List.exists_mem_of_ne_nil _ open_
  let lo : Nodes fs s := ⟨.vertex e.lo,by simp [vertices,activeNames,List.mem_flatMap];exact ⟨e,ep,by simp⟩⟩
  let hi : Nodes fs s := ⟨.vertex e.hi,by simp [vertices,activeNames,List.mem_flatMap];exact ⟨e,ep,by simp⟩⟩
  have neq : lo≠hi := fun eq => e.increasing.ne (Node.vertex.inj (congrArg Subtype.val eq))
  let _ : Nontrivial (Nodes fs s) := ⟨lo,hi,neq⟩
  exact conn.preconnected.exists_adj_of_nontrivial

/-- The recovered fields determine a role, a retained/bridge edge type and an
optional active degree at each dart. These agree with the permanent-name
overlay simultaneously. -/
structure MarkedPrefix (fs : List Face) (s : Inventory) (P : PlaneDrawing) (n : Nat) where
  host : SimpleGraph (Nodes fs s)
  inclusion : shadow fs s≤host
  plane : PlaneMap host
  order : host.Dart ≃ Fin n
  onto : Function.Surjective (fun i => (order.symm i).fst)
  size : P.ribbon.length=n
  rotation : ∀ i : Fin n,P.ribbon.rotation i.val=some (order (plane.rot (order.symm i))).val
  pairing : ∀ i : Fin n,P.ribbon.pairing i.val=some (order (order.symm i).symm).val
  same : ∀ i j : Fin n,P.vKey n i=P.vKey n j ↔ (order.symm i).fst=(order.symm j).fst
  roleAt : ∀ i : Fin n,P.vTag i=some (vertexRole s (order.symm i).fst.val)
  edgeAt : ∀ i : Fin n,P.eTag i=some (edgeRole (order.symm i).fst (order.symm i).snd)
  degreeAt : ∀ i : Fin n,P.red i=match (order.symm i).fst.val with
        | .vertex v => some (s.redDegree v) | _ => none

set_option maxHeartbeats 1200000 in
theorem marked_prefix {v f : Nat} (C : ClosedTrace v f)
    (terminal : (f+1)+4=2*(v+1)) (fs todo : List Face) (p : (fs++todo).Perm (List.ofFn C.faces))
    (s : Inventory) (ok : replay (fs.flatMap Face.sides)=some s) (nonempty : s.pending≠[])
    (weight : activeCost s * activeCost s≤220^2*(v+1)) :
    ∃ bits : List Bool,∃ P : PlaneDrawing,∃ n,Nonempty (MarkedPrefix fs s P n) ∧
      readPlane bits=some (some P) ∧ bits.length≤100000*ceilRoot (v+1) := by
  classical
  obtain ⟨H,sub,conn,M,z,ts,bs,R,rn,rot,pair,pack⟩ := prefix_record C terminal fs todo p s ok nonempty weight
  let _ : Fintype (Nodes fs s) := Fintype.ofFinset (vertices fs s).toFinset (fun _ => List.mem_toFinset)
  let n := 2*Nat.card H.edgeSet
  let tail (i : Fin n) := (z.symm i).fst
  let edge (i : Fin n) : H.edgeSet := ⟨(z.symm i).edge,(z.symm i).edge_mem⟩
  let vk := orbitKey R.rotation n
  let ek := orbitKey R.pairing n
  have vr (i : Fin n) := rot (z.symm i)
  have er (i : Fin n) := pair (z.symm i)
  simp only [apply_symm_apply] at vr er
  have sameV (i j : Fin n) : vk i=vk j ↔ tail i=tail j := by
    rw [orbitKey_iff _ (z.permCongr M.rot) vr]
    have e := sameCycle_permCongr_iff z M.rot (z.symm i) (z.symm j)
    simp only [apply_symm_apply] at e
    rw [←e]
    exact ⟨r_eq_of_sameCycle (r:=id) M.isRotationSystem.fst_apply,M.isRotationSystem.sameCycle _ _⟩
  have sameE (i j : Fin n) : ek i=ek j ↔ edge i=edge j := by
    rw [orbitKey_iff _ (z.permCongr (dartSymm H)) er]
    have e := sameCycle_permCongr_iff z (dartSymm H) (z.symm i) (z.symm j)
    simp only [apply_symm_apply] at e
    rw [←e,sameCycle_dartSymm_iff,Subtype.ext_iff,SimpleGraph.dart_edge_eq_iff]
    constructor
    · rintro (h|h)
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h];simp)
    · rintro (h|h)
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h];simp)
  have adj := nonisolated H conn nonempty
  have onto : Function.Surjective tail := by
    intro x; obtain ⟨y,h⟩ := adj x; exact ⟨z ⟨(x,y),h⟩,congrArg (fun d : H.Dart => d.fst) (z.symm_apply_apply _)⟩
  have ontoE : Function.Surjective edge := by
    rintro ⟨e,he⟩; induction e using Sym2.ind with
    | h x y => exact ⟨z ⟨(x,y),he⟩,Subtype.ext (congrArg SimpleGraph.Dart.edge (z.symm_apply_apply _))⟩
  let vRole (i : Fin n) := vertexRole s (tail i).val
  let eRole (i : Fin n) := edgeRole (tail i) (z.symm i).snd
  let vs := (reps vk).map vRole
  let es := (reps ek).map eRole
  let lives := (reps vk).filter (fun i => vRole i==original)
  let ds := lives.map (fun i => s.redDegree (rawName (tail i).val))
  let P : PlaneDrawing := ⟨R,vs,es,ds⟩
  have vlookup (i : Fin n) : P.vTag i=some (vRole i) := by
    change fieldAt (reps vk) ((reps vk).map vRole) (first vk i)=_
    rw [field_map _ _ (rep_mem _ _)]
    exact congrArg (fun a => some (vertexRole s (Subtype.val a))) ((sameV ..).mp (same_key vk i))
  have elookup (i : Fin n) : P.eTag i=some (eRole i) := by
    change fieldAt (reps ek) ((reps ek).map eRole) (first ek i)=_
    rw [field_map _ _ (rep_mem _ _)]
    have eq : (z.symm (first ek i)).edge=(z.symm i).edge := congrArg Subtype.val ((sameE ..).mp (same_key ek i))
    change some (edgeRole (z.symm (first ek i)).fst (z.symm (first ek i)).snd)=some (edgeRole (z.symm i).fst (z.symm i).snd)
    rcases (SimpleGraph.dart_edge_eq_iff ..).mp eq with eq|eq
    · rw [eq]
    · rw [eq]; exact congrArg some (edge_flip _ _)
  have liveEq : P.active n=lives := by simp [PlaneDrawing.active,lives,vlookup,vRole,P,PlaneDrawing.vKey,vk]
  have dlookup (i : Fin n) : P.red i=match (tail i).val with | .vertex x => some (s.redDegree x) | _ => none := by
    have rep := (sameV ..).mp (same_key vk i)
    cases h : (tail i).val with
    | vertex x =>
      have good : first vk i∈lives := List.mem_filter.mpr ⟨rep_mem _ _,by simp [vRole,rep,h,vertexRole]⟩
      have tag : P.vTag i=some original := by simpa [vRole,h,vertexRole] using vlookup i
      simp [PlaneDrawing.red,tag,liveEq]
      change fieldAt lives (lives.map _) (first vk i)=some (s.redDegree x)
      rw [field_map _ _ good,rep,h]; rfl
    | point e => by_cases m : e∈s.pending <;> simp [PlaneDrawing.red,vlookup,vRole,h,vertexRole,m,original]
    | centre q => simp [PlaneDrawing.red,vlookup,vRole,h,vertexRole,original]
  have vl : vs.length=cycleCount M.rot := by
    rw [show vs.length=(reps vk).length by simp [vs],reps_card vk tail onto sameV,cycleCount_eq_card_nonisolated M.isRotationSystem]
    exact (Nat.card_congr (Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,fun x => ⟨⟨x,adj x⟩,rfl⟩⟩)).symm
  have el : es.length=Nat.card H.edgeSet := by simpa [es] using reps_card ek edge ontoE sameE
  have dl : ds.length=vs.count original := by simp [ds,vs,lives,List.count_eq_length_filter,List.filter_map,Function.comp_def]
  have perm := (vertices_data vk tail onto sameV).map s.redDegree
  have pd : ds.Perm ((activeNames s).eraseDups.map s.redDegree) := by
    simpa [ds,lives,vRole,List.map_map,Function.comp_def] using perm
  obtain ⟨parsed,_,bound⟩ := pack vs es ds vl el dl pd
  exact ⟨_,P,n,⟨⟨H,sub,M,z,onto,rn,vr,er,sameV,vlookup,elookup,dlookup⟩⟩,parsed,bound⟩


/-- Expand the read fields, once per orbit, to the dart arrays consumed by
the existing incidence and block readers. This is a function of the bits
alone after decoding. -/
def PlaneDrawing.view (P : PlaneDrawing) (n : Nat) : MarkedPlane.View :=
  ⟨P.ribbon,List.ofFn (fun i : Fin n => (P.eTag i).any (fun tag => tag != bridgeTag)),
    List.ofFn (fun i : Fin n => ((P.vTag i).map roleNumber).getD 4),
    List.ofFn (fun i : Fin n => if i=first (P.vKey n) i then (P.red i).getD 0 else 0)⟩

def MarkedPrefix.tail {fs s P n} (L : MarkedPrefix fs s P n) (i : Fin n) := (L.order.symm i).fst

noncomputable def MarkedPrefix.labels {fs s P n} (L : MarkedPrefix fs s P n) :
    OverlayRead.Labels fs s n (P.view n) := by
  classical
  let W := P.view n
  have turn (i : Fin n) : W.turn i=L.order (L.plane.rot (L.order.symm i)) := by
    simp [W,PlaneDrawing.view,MarkedPlane.View.turn,L.rotation]
  have key (i : Fin n) : W.vertexKey i=P.vKey n i := by
    unfold MarkedPlane.View.vertexKey PlaneDrawing.vKey orbitKey
    simp only [L.rotation,Option.bind_some,Fin.is_lt,↓reduceDIte,Fin.eta,Option.getD_some,turn]
  have same (i j : Fin n) : W.vertexKey i=W.vertexKey j ↔ L.tail i=L.tail j := by
    rw [key,key]; exact L.same i j
  have dval (i : Fin n) : (P.red i).getD 0=value s (L.tail i).val := by
    unfold MarkedPrefix.tail; rw [L.degreeAt]; cases h : (L.order.symm i).fst.val <;> rfl
  have counter (i : Fin n) : W.counter i=value s (L.tail i).val := by
    have get (j : Fin n) : W.values[j.val]?.getD 0 =
        if j=first (P.vKey n) j then value s (L.tail j).val else 0 := by simp [W,PlaneDrawing.view,dval]
    unfold MarkedPlane.View.counter
    simp only [get,key]
    let k := P.vKey n
    rw [Finset.sum_eq_single (first k i)]
    · have eq := same_key k i
      have fix := rep_fixed k (rep_mem k i)
      have val := (L.same ..).mp eq
      change (if k (first k i)=k i then (if first k i=first k (first k i) then _ else _) else _)=_
      simp [eq,fix,MarkedPrefix.tail,val]
    · intro j _ ne
      by_cases eq : P.vKey n j=P.vKey n i
      · have f := (first_iff _ _ _).mpr eq
        simp [eq,f,ne,k]
      · simp [eq]
    · simp
  refine ⟨L.tail,L.onto,same,?_,?_⟩
  · intro i; refine ⟨?_,counter i⟩
    simp [PlaneDrawing.view,L.roleAt,role_num,MarkedPrefix.tail]
  · intro a b
    have test (d : Fin n) : W.retained[d.val]?.getD false =
        decide ((shadow fs s).Adj (L.tail d) (L.order.symm d).snd) := by
      by_cases h : (shadow fs s).Adj (L.tail d) (L.order.symm d).snd
      · simp [W,PlaneDrawing.view,L.edgeAt,MarkedPrefix.tail] at *
        simp [edgeRole,h]; split <;> decide
      · simp [W,PlaneDrawing.view,L.edgeAt,MarkedPrefix.tail] at *
        simp [edgeRole,h]
    change W.edgeBetween a b ↔ _
    have pe (d : Fin n) : W.ribbon.pairing d.val = some (L.order (L.order.symm d).symm).val := L.pairing d
    simp only [MarkedPlane.View.edgeBetween,List.any_eq_true,List.mem_finRange,true_and,Bool.and_eq_true,
      test,decide_eq_true_eq,beq_iff_eq,same,pe,Option.any_some]
    constructor
    · rintro ⟨d,⟨good,hd⟩,he⟩
      rw [dite_eq_left (L.order (L.order.symm d).symm).isLt,beq_iff_eq,same] at he
      have tip : L.tail (L.order (L.order.symm d).symm)=(L.order.symm d).snd :=
        congrArg (fun d : L.host.Dart => d.fst) (L.order.symm_apply_apply _)
      rwa [←hd,←he,tip]
    · intro good
      let d : L.host.Dart := ⟨(L.tail a,L.tail b),L.inclusion good⟩
      refine ⟨L.order d,⟨?_,?_⟩,?_⟩
      · change (shadow fs s).Adj (L.order.symm (L.order d)).fst (L.order.symm (L.order d)).snd
        rw [L.order.symm_apply_apply]; exact good
      · change (L.order.symm (L.order d)).fst=d.fst
        rw [L.order.symm_apply_apply]
      · rw [dite_eq_left (L.order (L.order.symm (L.order d)).symm).isLt,beq_iff_eq,same]
        change (L.order.symm (L.order (L.order.symm (L.order d)).symm)).fst=L.tail b
        rw [L.order.symm_apply_apply,L.order.symm_apply_apply]; rfl

/-- The compact records feed the same block query as the search: the query
succeeds exactly for two open edges belonging to the same read component. -/
theorem MarkedPrefix.blocks {fs s P n} (L : MarkedPrefix fs s P n)
    (x y u v : Fin n) (e f : Edge) (xl : (L.tail x).val=.vertex e.lo)
    (yh : (L.tail y).val=.vertex e.hi) (ul : (L.tail u).val=.vertex f.lo)
    (vh : (L.tail v).val=.vertex f.hi) :
    OverlayRead.block (P.view n) x y u v ↔ e∈s.pending ∧ f∈s.pending ∧ sameBlock fs e f := by
  exact OverlayRead.blocks_read L.labels x y u v e f xl yh ul vh

/-- Concrete records for every prefix of one order, including the two empty
boundaries, in the catalogue with the manuscript's explicit cutoff. -/
theorem compact_catalogue (sep : SeparatorInput.WeightedPlanarSeparator)
    (C : ClosedTrace v f) (terminal : (f+1)+4=2*(v+1)) :
    ∃ order : List Face,order.Perm (List.ofFn C.faces) ∧ ∀ fs todo,order=fs++todo →
      ∃ s : Inventory,replay (fs.flatMap Face.sides)=some s ∧
      ∃ bits∈PlanarDegrees.Frontier.words (100000*ceilRoot (v+1)),
        (vertices fs s=[] ∧ readPlane bits=some none) ∨
        ∃ P n,readPlane bits=some (some P) ∧ Nonempty (MarkedPrefix fs s P n) := by
  have weighted := SeparatorInput.host sep C terminal (fun x => cost (simpleDegree C.ledger.sealed x)) (by simp [cost])
  obtain ⟨seq,perm,all⟩ := bounded_codes C terminal C.ledger.sealed
    (fun i _ h _ => ShortBoundary.seen C i h) (ShortBoundary.hostMass C terminal) weighted
  refine ⟨seq,perm,?_⟩
  intro fs todo cut
  obtain ⟨s,ok,_,_,_,weight⟩ := all fs todo cut
  have full : (fs++todo).Perm (List.ofFn C.faces) := cut ▸ perm
  refine ⟨s,ok,?_⟩
  by_cases empty : s.pending=[]
  · have sparse := SparseOverlay.retained_bound C terminal fs todo full s ok
    have nil : retained s=[] := List.length_eq_zero_iff.mp (by simpa [activeNames,empty] using sparse)
    refine ⟨[false],(PlanarDegrees.Frontier.words_spec ..).mpr ?_,.inl ⟨?_,rfl⟩⟩
    · simp [ceilRoot]; omega
    · simp [vertices,activeNames,spokes,contacts,nil,empty]
  · obtain ⟨bits,P,n,lab,dec,bound⟩ := marked_prefix C terminal fs todo full s ok empty weight
    exact ⟨bits,(PlanarDegrees.Frontier.words_spec ..).mpr bound,.inr ⟨P,n,dec,lab⟩⟩

end Recognition.CompactBoundary
