import Orientation
import SphereRotation
import TraceCheck

/-! Coherently oriented rows of a checked face trace form a plane map of
its full edge host; deleting the blue edges recovers the planar witness. -/
namespace Recognition.TracePlanarity
open PlanarDegrees.Frontier PlanarDegrees.Topology Recognition.Orientation
open LeanPool.K5MinorFreeChoosability

private structure Signing (G : Gluing v f e) where
  s : Fin (f+1) → ℤ
  unit : ∀ i, s i=1 ∨ s i= -1
  cancel : ∀ d, s (G.dual d).1 * coefficient G (G.dual d).1 d =
    -(s (G.dual d).2 * coefficient G (G.dual d).2 d)

private def raw (pos : Bool) (k : Fin 3) := if pos then k else -(k+1)
private def pos {G : Gluing v f e} (S : Signing G) (i : Fin (f+1)) : Bool := decide (S.s i=1)
private def key {G : Gluing v f e} (S : Signing G) (i) (k) := side G i (raw (pos S i) k)
private def tail {G : Gluing v f e} (S : Signing G) (i) (k : Fin 3) :=
  corner G i (if pos S i then k else -k)
private def pair {G : Gluing v f e} (S : Signing G) (i) (k) := (tail S i k,tail S i (k+1))

private theorem raw_inv : ∀ p k, raw p (raw p k)=k := by decide
private theorem cancel_add : ∀ k : Fin 3, -(k+1)+1= -k := by decide

private theorem ends {G : Gluing v f e} (S : Signing G) (i) (k) :
    Across G.primal (key S i k) (tail S i k) (tail S i (k+1)) := by
  have h := side_ends G i (raw (pos S i) k)
  cases hp : pos S i
  · simpa [Across,key,raw,tail,hp,cancel_add] using h.symm
  · simpa [key,raw,tail,hp] using h

private theorem value {G : Gluing v f e} (S : Signing G) (simple : ∀ d, (G.primal d).1 ≠ (G.primal d).2)
    (i) (k) : S.s i * coefficient G i (key S i k) =
      if G.primal (key S i k) = pair S i k then 1 else -1 := by
  rcases S.unit i with h|h
  · simp [h,key,side_coeff,pos,pair,tail,raw]
  · have H := side_ends G i (-(k+1))
    let a := corner G i (-(k+1))
    let b := corner G i (-k)
    let d := side G i (-(k+1))
    have ab : G.primal d=(a,b) ∨ G.primal d=(b,a) := by simpa [a,b,d,Across,cancel_add] using H
    simp only [h,key,pos,show (decide ((-1:ℤ)=1))=false by decide,raw,ite_false,Bool.false_eq_true,
      side_coeff,pair,tail,cancel_add]
    change -1 * (if G.primal d=(a,b) then 1 else -1) = if G.primal d=(b,a) then 1 else -1
    have ne := simple d
    rcases ab with eq|eq <;> rw [eq] at ne ⊢ <;> simp_all [Prod.ext_iff]

private theorem incident_key {G : Gluing v f e} (S : Signing G) (i) (d) :
    incident G.dual d i ↔ ∃ k, key S i k=d := by
  rw [incident_side]; constructor
  · rintro ⟨j,rfl⟩; exact ⟨raw (pos S i) j,congrArg (side G i) (raw_inv _ _)⟩
  · rintro ⟨k,rfl⟩; exact ⟨_,rfl⟩

private theorem key_inj {G : Gluing v f e} (S : Signing G) (i) : Function.Injective (key S i) := by
  intro k l h
  have eq := (side_injective G i) h
  exact (raw_inv _ _).symm.trans ((congrArg (raw (pos S i)) eq).trans (raw_inv _ _))

private theorem tail_onto {G : Gluing v f e} (S : Signing G) (x : Fin (v+1)) : ∃ i k, tail S i k=x := by
  obtain ⟨i,h⟩ := G.used x
  have ex : ∃ j, corner G i j=x := by
    simp only [Triangle.corners,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
  obtain ⟨j,rfl⟩ := ex
  cases hp : pos S i
  · exact ⟨i,-j,by simp [tail,hp]⟩
  · exact ⟨i,j,by simp [tail,hp]⟩

private theorem reversed {G : Gluing v f e} (S : Signing G) (simple : ∀ d, (G.primal d).1 ≠ (G.primal d).2)
    {i j k l} (ne : i≠j) (same : key S i k=key S j l) : (pair S i k).swap = pair S j l := by
  let d := key S j l
  have hi := (incident_key S i d).mpr ⟨k,same⟩
  have hj := (incident_key S j d).mpr ⟨l,rfl⟩
  have co : S.s i*coefficient G i d = -(S.s j*coefficient G j d) := by
    have c := S.cancel d
    rcases hi with a|a <;> rcases hj with b|b <;> grind
  have vi := value S simple i k
  have vj := value S simple j l
  have ai := ends S i k
  have aj := ends S j l
  change G.primal (key S i k)=pair S i k ∨ G.primal (key S i k)=(pair S i k).swap at ai
  change G.primal d=pair S j l ∨ G.primal d=(pair S j l).swap at aj
  rw [same] at vi ai
  change S.s i * coefficient G i d = if G.primal d=pair S i k then 1 else -1 at vi
  change S.s j * coefficient G j d = if G.primal d=pair S j l then 1 else -1 at vj
  change G.primal d=pair S i k ∨ G.primal d=(pair S i k).swap at ai
  rw [vi,vj] at co
  by_cases a : G.primal d=pair S i k <;> by_cases b : G.primal d=pair S j l
  · simp only [ite_eq_left a,ite_eq_left b] at co; omega
  · have hh := aj.resolve_left b
    exact congrArg Prod.swap (a.symm.trans hh)
  · exact (ai.resolve_left a).symm.trans b
  · simp [a,b] at co

/-- A permanently labelled, loopless simple graph using precisely the edge
identifiers of the gluing. An unoriented pair determines its identifier. -/
structure Labelling (G : Gluing v f e) (H : SimpleGraph (Fin (v+1))) where
  adj : ∀ a b, H.Adj a b ↔ ∃ d, Across G.primal d a b
  unique : ∀ d d' a b, Across G.primal d a b → Across G.primal d' a b → d=d'

/-- Original row indices are the facial orbits of this plane rotation. -/
structure Indexed (H : SimpleGraph (Fin n)) (f : Nat) where
  plane : PlaneMap H
  row : (Fin (f+1) × Fin 3) ≃ H.Dart
  follows : ∀ i k, plane.facePerm (row (i,k))=row (i,k+1)
  orbit : ∀ a b, plane.facePerm.SameCycle a b ↔ (row.symm a).1=(row.symm b).1
  connected : ∀ i, Walk (fun a b => ∃ k l, (row (a,k)).symm=row (b,l)) 0 i

/-- All the conditions needed to reconstruct the plane map come from the
closed gluing, its simple edge labelling, and its number of faces. -/
theorem gluing_rows (G : Gluing v f e) (H : SimpleGraph (Fin (v+1)))
    (M : Labelling G H) (count : (f+1)+4=2*(v+1)) :
    ∃ R : Indexed H f, ∀ i x, x∈(G.tri i).corners ↔ ∃ k, (R.row (i,k)).fst=x := by
  classical
  obtain ⟨s,u,c⟩ := coherent G count
  let S : Signing G := ⟨s,u,c⟩
  have simple (d) : (G.primal d).1≠(G.primal d).2 := by
    intro eq
    have h := (M.adj _ _).mpr ⟨d,Or.inl (Prod.eta ..).symm⟩
    exact (H.ne_of_adj h) eq
  let dart (t : Fin (f+1) × Fin 3) : H.Dart :=
    ⟨pair S t.1 t.2,(M.adj _ _).mpr ⟨_,ends S t.1 t.2⟩⟩
  have twin {i j k l} (diff : i≠j) (same : key S i k=key S j l) :
      (dart (i,k)).symm = dart (j,l) := SimpleGraph.Dart.ext _ _ (reversed S simple diff same)
  have inj : Function.Injective dart := by
    rintro ⟨i,k⟩ ⟨j,l⟩ eq
    have a := ends S i k
    have b := ends S j l
    have eq₁ : tail S i k=tail S j l := congrArg (fun t : H.Dart => t.fst) eq
    have eq₂ : tail S i (k+1)=tail S j (l+1) := congrArg (fun t : H.Dart => t.snd) eq
    rw [eq₁,eq₂] at a
    have same := M.unique _ _ _ _ a b
    by_cases ne : i=j
    · subst j; rw [key_inj S i same]
    · have self := (twin ne same).trans eq.symm
      exact ((dart (i,k)).adj.ne (congrArg (fun t : H.Dart => t.snd) self)).elim
  have onto : Function.Surjective dart := by
    intro h
    obtain ⟨d,ed⟩ := (M.adj _ _).mp h.adj
    let a := (G.dual d).1
    let b := (G.dual d).2
    obtain ⟨k,hk⟩ := (incident_key S a d).mp (Or.inl rfl)
    obtain ⟨l,hl⟩ := (incident_key S b d).mp (Or.inr rfl)
    have rev := twin (G.twoFaces d) (hk.trans hl.symm)
    have opts : dart (a,k)=h ∨ (dart (a,k)).symm=h := by
      have ae := ends S a k
      rw [hk] at ae
      rcases ae with eq|eq <;> rcases ed with g|g <;> rw [eq] at g <;>
        first | exact Or.inl (SimpleGraph.Dart.ext _ _ g) | exact Or.inr (SimpleGraph.Dart.ext _ _ g) |
          exact Or.inl (SimpleGraph.Dart.ext _ _ (congrArg Prod.swap g)) |
          exact Or.inr (SimpleGraph.Dart.ext _ _ (congrArg Prod.swap g))
    rcases opts with x|x
    · exact ⟨(a,k),x⟩
    · exact ⟨(b,l),rev.symm.trans x⟩
  let row := Equiv.ofBijective dart ⟨inj,onto⟩
  have all : Function.Surjective (fun d : H.Dart => d.fst) := by
    intro x
    obtain ⟨i,k,eq⟩ := tail_onto S x
    exact ⟨dart (i,k),eq⟩
  have conn (i) : Walk (fun a b => ∃ k l, (row (a,k)).symm=row (b,l)) 0 i := by
    induction G.dualConnected i with
    | refl => exact .refl
    | @step a b _ edge ih =>
      obtain ⟨d,_,ed⟩ := edge
      have ne : a≠b := by have nn := G.twoFaces d; rcases ed with eq|eq <;> simpa [eq,ne_comm] using nn
      have ia : incident G.dual d a := by rcases ed with eq|eq <;> simp [incident,eq]
      have ib : incident G.dual d b := by rcases ed with eq|eq <;> simp [incident,eq]
      obtain ⟨k,hk⟩ := (incident_key S a d).mp ia
      obtain ⟨l,hl⟩ := (incident_key S b d).mp ib
      exact ih.step ⟨k,l,twin ne (hk.trans hl.symm)⟩
  obtain ⟨P,step,orbits⟩ := Recognition.SphereRotation.plane_of_rows H row (fun _ _ => rfl) all conn count
  refine ⟨⟨P,row,step,orbits,conn⟩,?_⟩
  intro i x
  change x∈(G.tri i).corners ↔ ∃ k, tail S i k=x
  have base : x∈(G.tri i).corners ↔ ∃ j, corner G i j=x := by
    simp only [Triangle.corners,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · rintro (rfl|rfl|rfl); exact ⟨0,rfl⟩; exact ⟨1,rfl⟩; exact ⟨2,rfl⟩
    · rintro ⟨k,rfl⟩
      by_cases a : k=0 <;> by_cases b : k=1 <;> simp [corner,a,b]
  rw [base]; constructor
  · rintro ⟨j,rfl⟩; cases hp : pos S i
    · exact ⟨-j,by simp [tail,hp]⟩
    · exact ⟨j,by simp [tail,hp]⟩
  · rintro ⟨k,rfl⟩; exact ⟨_,rfl⟩

theorem gluing_planar (G : Gluing v f e) (H : SimpleGraph (Fin (v+1)))
    (M : Labelling G H) (count : (f+1)+4=2*(v+1)) : IsPlanar H := by
  obtain ⟨R,_⟩ := gluing_rows G H M count
  exact ⟨R.plane⟩

open Recognition.Witness Recognition.Wagner SparseBoundary

/-- A terminal trace has a forbidden-minor planar host on the original
labels. No orientability or spherical interpretation is supplied as input. -/
theorem host_rows {v f} (C : ClosedTrace v f) (count : (f+1)+4=2*(v+1)) :
    ∃ R : Indexed (toSimple (host C)) f, ∀ i (x : Fin (v+1)),
      x.val∈cornerNames (C.faces i) ↔ ∃ k, (R.row (i,k)).fst=x := by
  classical
  obtain ⟨G,hf,he⟩ := C.gluing
  let keys := C.ledger.sealed
  let ed (d : Fin keys.length) := keys[d.val]
  have ends' (d : Fin keys.length) (a b : Fin (v+1)) :
      Across G.primal d a b ↔ joins (ed d) a.val b.val := by
    have ha := congrArg Prod.fst (he d)
    have hb := congrArg Prod.snd (he d)
    change (G.primal d).1.val=(ed d).lo at ha
    change (G.primal d).2.val=(ed d).hi at hb
    simp [Across,Prod.ext_iff,Fin.ext_iff,ha,hb,joins]
  have g : Labelling G (toSimple (host C)) := by
    constructor
    · intro a b
      rw [toSimple_adj,host,graph_adj]
      constructor
      · rintro ⟨edge,mem,eq⟩
        obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem mem
        exact ⟨⟨i,hi⟩,(ends' _ _ _).mpr eq⟩
      · rintro ⟨d,eq⟩
        exact ⟨ed d,List.getElem_mem _,(ends' _ _ _).mp eq⟩
    · intro d d' a b hs ht
      have h := (ends' d a b).mp hs
      have t := (ends' d' a b).mp ht
      have h₁ := (ed d).increasing
      have h₂ := (ed d').increasing
      simp only [joins,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at h t
      have edgeEq : ed d=ed d' := by
        have lo : (ed d).lo=(ed d').lo := by omega
        have hi : (ed d).hi=(ed d').hi := by omega
        have extEdge (p q : Edge) (l : p.lo=q.lo) (r : p.hi=q.hi) : p=q := by
          cases p; cases q; congr
        exact extEdge _ _ lo hi
      have nd : keys.Nodup := (inventory_counts C.accepted).2.1
      have h₃ := nd.idxOf_getElem d.val d.isLt
      have h₄ := nd.idxOf_getElem d'.val d'.isLt
      exact Fin.ext (h₃.symm.trans ((congrArg keys.idxOf edgeEq).trans h₄))
  obtain ⟨R,rc⟩ := gluing_rows G _ g count
  refine ⟨R,fun i x => ?_⟩
  rw [←hf i,← rc]; simp only [List.mem_map]; constructor
  · rintro ⟨z,h,e⟩; exact Fin.ext e ▸ h
  · intro h; exact ⟨_,h,rfl⟩

theorem host_planar {v f} (C : ClosedTrace v f) (count : (f+1)+4=2*(v+1)) : (host C).Planar := by
  obtain ⟨R,_⟩ := host_rows C count
  exact (planar_iff_rotation _).mpr ⟨R.plane⟩

theorem terminal_planaric {v f} (C : ClosedTrace v f) (ds : List Nat)
    (degrees : (witnessDegrees C).Perm ds) (count : (f+1)+4=2*(v+1)) : Planaric ds :=
  planar_of_host C ds degrees (host_planar C count)

/-- Unconditional soundness of the executable, bounded-bit certificate
verifier for the project's potentially planar degree-list language. -/
theorem verify_planaric {v f} {ds : List Nat} {r : TraceCheck.Records v f}
    (yes : TraceCheck.verify ds r) : Planaric ds := by
  obtain ⟨_,count,_,C,perm,_⟩ := TraceCheck.verify_sound ds r yes
  exact terminal_planaric C ds perm count

end Recognition.TracePlanarity
