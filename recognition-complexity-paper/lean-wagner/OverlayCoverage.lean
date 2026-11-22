import SparseOverlay
import MarkedPlane

/-! Typed marked graph records for the entire separator-chosen face order,
including the empty boundary at either end. -/
namespace Recognition.OverlayCoverage
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep PlanarDegrees.Topology
open Recognition.Outline Recognition.Overlay Recognition.OverlayMinor Recognition.MarkedPlane

abbrev Nodes (fs : List Face) (s : Inventory) := {a // a∈vertices fs s}

private noncomputable instance instFintypeNodes {fs : List Face} {s : Inventory} : Fintype (Nodes fs s) := by
  classical
  exact Fintype.ofFinset (vertices fs s).toFinset (fun _ => List.mem_toFinset)

def role (s : Inventory) {P : Type} : Node P → Fin 4
  | .vertex _ => 0
  | .point e => if e∈s.pending then 1 else 2
  | .centre _ => 3

def value (s : Inventory) {P : Type} : Node P → Nat
  | .vertex v => s.redDegree v
  | _ => 0

def activeCost (s : Inventory) :=
  ((activeNames s).eraseDups.map (fun v => cost (s.redDegree v))).sum

private theorem card_nodes (fs : List Face) (s : Inventory) :
    Nat.card (Nodes fs s) ≤ (vertices fs s).length := by
  classical
  rw [Nat.card_eq_fintype_card]
  have eq : Fintype.card (Nodes fs s)=(vertices fs s).toFinset.card :=
    Fintype.card_ofFinset (p := {x | x∈vertices fs s}) (vertices fs s).toFinset (fun _ => List.mem_toFinset)
  rw [eq]
  exact List.toFinset_card_le _

private theorem four (fs : List Face) (s : Inventory) (ok : replay (fs.flatMap Face.sides)=some s)
    (e : Edge) (pending : e∈s.pending) : 4≤Nat.card (Nodes fs s) := by
  classical
  have kept : e∈retained s := by simp [retained,pending]
  have cnt := (counted fs s ok e).1.mpr pending
  rw [incidentCount,spokes_read] at cnt
  have has : e∈(spokes fs (retained s)).map Prod.fst := List.count_pos_iff.mp (by omega)
  obtain ⟨⟨g,p⟩,sp,eq⟩ := List.mem_map.mp has
  change g=e at eq
  subst g
  let lo : Nodes fs s := ⟨.vertex e.lo,by simp [vertices,activeNames,List.mem_flatMap]; exact ⟨e,pending,by simp⟩⟩
  let hi : Nodes fs s := ⟨.vertex e.hi,by simp [vertices,activeNames,List.mem_flatMap]; exact ⟨e,pending,by simp⟩⟩
  let mid : Nodes fs s := ⟨.point e,by simp [vertices,kept]⟩
  let hub : Nodes fs s := ⟨.centre p,by simp [vertices]; exact ⟨e,sp⟩⟩
  let little : Finset (Nodes fs s) := {lo,hi,mid,hub}
  have diff : lo≠hi := by intro h; have eq := congrArg Subtype.val h; exact e.increasing.ne (Node.vertex.inj eq)
  have size : little.card=4 := by simp [little,lo,hi,mid,hub,Subtype.ext_iff,e.increasing.ne]
  have := little.card_le_univ
  rw [size] at this
  simpa [Nat.card_eq_fintype_card] using this

private theorem counter_sum (fs : List Face) (s : Inventory) :
    ∑ w : Nodes fs s, cost (value s w.val) ≤ activeCost s + (retained s).length + (spokes fs (retained s)).length := by
  classical
  let c := fun z : Node (Patch fs (retained s)) => cost (value s z)
  have bound (xs : List (Node (Patch fs (retained s)))) :
      ∑ i∈xs.toFinset, c i ≤ (xs.map c).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      by_cases exists_ : x∈xs.toFinset
      · simp [Finset.insert_eq_of_mem exists_]; omega
      · simp [Finset.sum_insert exists_,ih]
  have H := bound (vertices fs s)
  have eq : ∑ i∈(vertices fs s).toFinset, c i = ∑ w : Nodes fs s, c w.val :=
    Finset.sum_subtype (F := instFintypeNodes) _ (fun _ => List.mem_toFinset) c
  rw [eq] at H
  have one {T : Type} (xs : List T) : (xs.map (fun _ => cost 0)).sum=xs.length := by
    simp [show cost 0=1 from rfl]
  simpa only [c,vertices,List.map_append,List.map_map,List.sum_append,Function.comp_def,
    value,one,activeCost] using H

/-- Encoded overlay semantics. The permanent labels exist only in the
correctness relation; the actual code carries anonymous dart keys. -/
def Covered (fs : List Face) (s : Inventory) (bits : List Bool) : Prop :=
  (bits=[] ∧ vertices fs s=[]) ∨
  ∃ (n : Nat) (C : View) (tail : Fin n → Nodes fs s), Function.Surjective tail ∧
    MarkedPlane.decode bits=some C ∧ C.ribbon.length=n ∧
    (∀ a b, C.vertexKey a=C.vertexKey b ↔ tail a=tail b) ∧
    (∀ a, C.roles[a.val]?=some (role s (tail a).val).val ∧ C.counter a=value s (tail a).val) ∧
    ∀ a b, C.edgeBetween a b ↔ (shadow fs s).Adj (tail a) (tail b)

theorem prefix_code {v f : Nat} (C : ClosedTrace v f) (terminal : (f+1)+4=2*(v+1))
    (read todo : List Face) (perm : (read++todo).Perm (List.ofFn C.faces))
    (s : Inventory) (ok : replay (read.flatMap Face.sides)=some s) :
    ∃ bs : List Bool, Covered read s bs ∧
      bs.length ≤ 1218*(activeNames s).eraseDups.length + 2*activeCost s + 1 := by
  classical
  have sparse := SparseOverlay.retained_bound C terminal read todo perm s ok
  have span := Overlay.size read s ok
  have contact := contacts_bound read s ok
  have sp : (spokes read (retained s)).length ≤ 2*(retained s).length := by simpa [spokes] using contact
  by_cases empty : s.pending=[]
  · have nil : retained s=[] := List.length_eq_zero_iff.mp (by simpa [activeNames,empty] using sparse)
    exact ⟨[],.inl ⟨rfl,by simp [vertices,activeNames,spokes,contacts,nil,empty]⟩,by simp⟩
  · obtain ⟨e,open_⟩ := List.exists_mem_of_ne_nil _ empty
    have large := four read s ok e open_
    obtain ⟨n,bs,D,tail,onto,parsed,len,cnt,small,keys,roles,edges⟩ :=
      graph_code (shadow read s) (TraceOverlay.prefix_planar C terminal read todo perm ok) large
        (fun w => role s w.val) (fun w => value s w.val)
    have count := card_nodes read s
    have total := counter_sum read s
    refine ⟨bs,.inr ⟨n,D,tail,onto,parsed,len,keys,roles,edges⟩,?_⟩
    change n+12=6*Nat.card (Nodes read s) at cnt
    change bs.length ≤ 20*n+2*∑ w : Nodes read s, cost (value s w.val) + 1 at small
    omega

/-- One actual face permutation has short, decodable plane-overlay records
at all its cuts. The sole geometric ordering assumption is the weighted
separator theorem for the induced subgraphs of the sphere triangulation. -/
theorem bounded_codes_permuted {v f : Nat} (C : ClosedTrace v f) (terminal : (f+1)+4=2*(v+1))
    (red : List Edge) (redSide : ∀ i, ∀ a∈(C.faces i).sides, a.red=true → a.edge∈red)
    (total : ((List.range (v+1)).map (simpleDegree red)).sum ≤ 6*(v+1))
    (weighted : Separators (List.range (v+1)) (cofacial (List.ofFn C.faces)) (fun x => cost (simpleDegree red x))) :
    ∃ seq : List Face, seq.Perm (List.ofFn C.faces) ∧ ∀ prefix_ todo, seq=prefix_++todo → ∀ read : List Face, read.Perm prefix_ →
      ∃ s : Inventory, replay (read.flatMap Face.sides)=some s ∧
      ∃ bits : List Bool, Covered read s bits ∧ bits.length ≤ 1220*activeCost s+1 ∧
        activeCost s*activeCost s ≤ 220^2*(v+1) := by
  have names : ∀ F∈List.ofFn C.faces, ∀ x∈corners F, x∈List.range (v+1) := by
    intro F m x h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp m
    have A := C.bounded i
    have B := (C.faces i).xy
    have D := (C.faces i).yz
    simp [corners] at h
    simp; omega
  have pair (e) := (paired_iff_closed.mpr ⟨_,C.accepted,C.closed⟩) e
  have sides : (List.ofFn C.faces).flatMap Face.sides=sideTrace C.faces := by
    rw [List.ofFn_eq_map,List.flatMap_map]; rfl
  obtain ⟨seq,perm,order⟩ := face_order_permuted (List.range (v+1)) (List.ofFn C.faces) red
    List.nodup_range names (by simpa only [sides] using pair)
    (fun _ m => by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp m; exact redSide i) (by simpa using total) weighted
  refine ⟨seq,perm,?_⟩
  intro prefix_ todo cut read shuffled
  obtain ⟨s,ok,width⟩ := order prefix_ todo cut read shuffled
  have act : ∀ x∈(activeNames s).eraseDups, ∃ e∈s.pending,touches e x := by
    simp [activeNames,touches,List.mem_flatMap]
  have w := width _ (distinct_names _) act
  have dx (xs : List Nat) : xs.length ≤ (xs.map (fun u => cost (s.redDegree u))).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; unfold cost at *; omega
  have count : (activeNames s).eraseDups.length≤activeCost s := dx _
  obtain ⟨b,coverage,short⟩ := prefix_code C terminal read todo ((shuffled.append_right todo).trans (cut ▸ perm)) s ok
  refine ⟨s,ok,b,coverage,by omega,?_⟩
  simpa only [List.length_range,activeCost] using w

theorem bounded_codes {v f : Nat} (C : ClosedTrace v f) (terminal : (f+1)+4=2*(v+1))
    (red : List Edge) (redSide : ∀ i, ∀ a∈(C.faces i).sides, a.red=true → a.edge∈red)
    (total : ((List.range (v+1)).map (simpleDegree red)).sum ≤ 6*(v+1))
    (weighted : Separators (List.range (v+1)) (cofacial (List.ofFn C.faces)) (fun x => cost (simpleDegree red x))) :
    ∃ seq : List Face, seq.Perm (List.ofFn C.faces) ∧ ∀ read todo, seq=read++todo →
      ∃ s : Inventory, replay (read.flatMap Face.sides)=some s ∧
      ∃ bits : List Bool, Covered read s bits ∧ bits.length ≤ 1220*activeCost s+1 ∧
        activeCost s*activeCost s ≤ 220^2*(v+1) := by
  obtain ⟨seq,p,order⟩ := bounded_codes_permuted C terminal red redSide total weighted
  exact ⟨seq,p,fun read todo cut => order read todo cut read (.refl _)⟩

#print axioms bounded_codes
end Recognition.OverlayCoverage
