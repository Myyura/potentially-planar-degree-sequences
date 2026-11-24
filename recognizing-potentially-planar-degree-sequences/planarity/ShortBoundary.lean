import BoundaryState
import ResidualTable

/-! The full finite catalogue of allowed boundary states for an input
sequence. The separator is applied using degrees of the complete host,
which dominate all red degrees without any requirement on proposed colors. -/
namespace Recognition.ShortBoundary
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep PlanarDegrees.Topology Recognition.Outline Recognition.Overlay
open Recognition.OverlayCoverage Recognition.BoundaryState Recognition.QuotientDP

private theorem sum_degrees (n : Nat) (es : List Edge) :
    ((List.range n).map (simpleDegree es)).sum ≤ 2*es.length := by
  have touch (e : Edge) : ((List.range n).filter (touches e)).length ≤ 2 := by
    apply ((List.nodup_range (n := n)).filter _).length_le_of_subset (l₂ := [e.lo,e.hi])
    intro v m
    have t := (List.mem_filter.mp m).2
    simpa [touches] using t
  have cnt (e : Edge) (xs : List Nat) :
      (xs.map (fun v => (touches e v).toNat)).sum=(xs.filter (touches e)).length := by
    induction xs with
    | nil => rfl
    | cons v xs ih => cases h : touches e v <;> simp [h,ih,Nat.add_comm]
  induction es with
  | nil => change ((List.range n).map (fun _ => 0)).sum≤0; simp
  | cons e es ih =>
    have eq : simpleDegree (e::es) = fun v => simpleDegree es v + (touches e v).toNat := by
      funext v; cases h : touches e v <;> simp [simpleDegree,h]
    rw [eq,List.sum_map_add,cnt]
    have t := touch e
    simp only [List.length_cons]
    omega

theorem seen {v f} (C : ClosedTrace v f) (i : Fin (f+1)) {a : Event}
    (side : a∈(C.faces i).sides) : a.edge∈C.ledger.sealed := by
  have m : a.edge∈(sideTrace C.faces).map Event.edge :=
    List.mem_map.mpr ⟨a,List.mem_flatMap.mpr ⟨i,List.mem_finRange _,side⟩,rfl⟩
  have pos : 0<occurrences (sideTrace C.faces) a.edge := List.count_pos_iff.mpr m
  have := (paired_iff_closed.mpr ⟨_,C.accepted,C.closed⟩) a.edge
  exact ((replay_accurate C.accepted).sealed _).mpr (by omega)

theorem hostMass {v f} (C : ClosedTrace v f) (terminal : (f+1)+4=2*(v+1)) :
    ((List.range (v+1)).map (simpleDegree C.ledger.sealed)).sum ≤ 6*(v+1) := by
  obtain ⟨G,_,_⟩ := C.gluing
  have inc := G.incidence_count
  have sum := sum_degrees (v+1) C.ledger.sealed
  omega

theorem bounds {v f} (C : ClosedTrace v f) (read todo : List Face)
    (perm : (read++todo).Perm (List.ofFn C.faces)) {s} (ok : replay (read.flatMap Face.sides)=some s)
    {x : Nat} (h : live s x) : x<v+1 := by
  obtain ⟨e,em,t⟩ := List.any_eq_true.mp h
  have count := ((replay_accurate ok).pending e).mp em
  obtain ⟨a,m,eq⟩ := List.mem_map.mp (List.count_pos_iff.mp (by omega : 0<occurrences (read.flatMap Face.sides) e))
  obtain ⟨F,old,side⟩ := List.mem_flatMap.mp m
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (perm.mem_iff.mp (List.mem_append_left todo old))
  have z := C.bounded i
  have xy := (C.faces i).xy
  have yz := (C.faces i).yz
  subst e
  simp only [Face.sides,List.mem_cons,List.not_mem_nil,or_false] at side
  rcases side with rfl|rfl|rfl <;> simp [touches] at t <;> omega

def catalogue (ds : List Nat) :=
  BoundaryState.table ds.length (cutoff ds.length) (2*ds.length) (ResidualTable.table ds)

private theorem flat_limit {A B : Type} (f : A → List B) (xs : List A) (k : Nat)
    (cap : ∀ x, (f x).length≤k) : (xs.flatMap f).length≤xs.length*k := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
                    exact (Nat.add_le_add (cap a) ih).trans_eq (Nat.add_comm ..)

theorem catalogue_size (ds : List Nat) :
    (catalogue ds).length ≤ 2^(cutoff ds.length+1) *
      ((ds.length+1)*2^(4*(ds.sum.sqrt+1)) * ((ds.length+1)*(2*ds.length+1))) := by
  let n := ds.length
  let residual := ResidualTable.table ds
  have bound : (catalogue ds).length ≤ (words (cutoff n)).length *
      (residual.length*((n+1)*(2*n+1))) := by
    apply flat_limit
    intro bs
    apply flat_limit
    intro r
    have h := flat_limit (fun u => (List.range (2*n+1)).filterMap (fun f => decode n bs r u f))
      (List.range (n+1)) (2*n+1) (fun _ => (List.length_filterMap_le ..).trans_eq List.length_range)
    simpa only [List.length_range] using h
  have wh := word_count (cutoff n)
  dsimp [n] at wh bound
  exact bound.trans (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (ResidualTable.table_bound ds)))

/-- For every true prefix, its complete state occurs in the executable
catalogue up to the actual renaming relation used by the transition table.
The input histogram, used-vertex and face fields are enumerated literally. -/
theorem catalogued_permuted {v f : Nat} (C : ClosedTrace v f) (terminal : (f+1)+4=2*(v+1))
    (ds : List Nat) (size : ds.length=v+1)
    (weighted : Separators (List.range (v+1)) (cofacial (List.ofFn C.faces))
      (fun x => cost (simpleDegree C.ledger.sealed x))) :
    ∃ seq : List Face, seq.Perm (List.ofFn C.faces) ∧ ∀ prefix_ todo, seq=prefix_++todo → ∀ read : List Face, read.Perm prefix_ →
      ∃ s, replay (read.flatMap Face.sides)=some s ∧
        ∀ t : State ds.length, Model read s t → t.remaining ≤ (ds : Multiset Nat) →
          t.used≤ds.length → t.faces≤2*ds.length →
          ∃ d∈catalogue ds, Same d t := by
  obtain ⟨seq,p,all⟩ := bounded_codes_permuted C terminal C.ledger.sealed
    (fun i _ h _ => seen C i h) (hostMass C terminal) weighted
  refine ⟨seq,p,?_⟩
  intro prefix_ todo cut read shuffled
  obtain ⟨s,ok,bs,cov,hb,hw⟩ := all prefix_ todo cut read shuffled
  refine ⟨s,ok,?_⟩
  intro t M rem used faces
  have named (x) (h : live s x) : x<ds.length := size ▸ bounds C read todo ((shuffled.append_right todo).trans (cut ▸ p)) ok h
  obtain ⟨d,code,iso⟩ := state_round_trip cov ok named t M
  refine ⟨d,table_mem.mpr ⟨bs,t.remaining,t.used,t.faces,?_,(ResidualTable.mem_table ..).mpr rem,used,faces,code⟩,iso⟩
  rw [size]
  exact length_cut _ _ _ hb hw

theorem catalogued_prefixes {v f : Nat} (C : ClosedTrace v f) (terminal : (f+1)+4=2*(v+1))
    (ds : List Nat) (size : ds.length=v+1)
    (weighted : Separators (List.range (v+1)) (cofacial (List.ofFn C.faces))
      (fun x => cost (simpleDegree C.ledger.sealed x))) :
    ∃ seq : List Face, seq.Perm (List.ofFn C.faces) ∧ ∀ read todo, seq=read++todo →
      ∃ s, replay (read.flatMap Face.sides)=some s ∧
        ∀ t : State ds.length, Model read s t → t.remaining ≤ (ds : Multiset Nat) →
          t.used≤ds.length → t.faces≤2*ds.length →
          ∃ d∈catalogue ds, Same d t := by
  obtain ⟨seq,p,order⟩ := catalogued_permuted C terminal ds size weighted
  exact ⟨seq,p,fun read todo cut => order read todo cut read (.refl _)⟩

#print axioms catalogued_prefixes
#print axioms catalogue_size
end Recognition.ShortBoundary
