import Topology
import SparseBoundary.GraphEncoding
import SparseBoundary.GraphPerm
import SparseBoundary.GraphContractionCheck

/-! Recover the project's packed, labelled simple graph from a red edge
trace, and identify its vertex degrees with the replay counters. -/
namespace Recognition.Witness
open PlanarDegrees PlanarDegrees.Frontier PlanarDegrees.Topology SparseBoundary

def joins (e : Edge) (i j : Nat) : Bool :=
  (e.lo == i && e.hi == j) || (e.lo == j && e.hi == i)

def relation {n : Nat} (es : List Edge) (i j : Fin n) : Bool := es.any (joins · i.val j.val)

def graph (n : Nat) (es : List Edge) : Graph n := Graph.ofRelation (relation es)

theorem graph_adj {n : Nat} (es : List Edge) (i j : Fin n) :
    (graph n es).adj i j = true ↔ ∃ e ∈ es, joins e i.val j.val := by
  rw [graph,Graph.adj_ofRelation]
  · exact List.any_eq_true
  · intro a b
    unfold relation
    apply congrArg (fun f => es.any f)
    funext e; simp [joins,Bool.or_comm]
  · intro a
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨e,_,he⟩ := List.any_eq_true.mp h
    have := e.increasing
    simp [joins] at he; omega

private def other (e : Edge) (v : Nat) := if e.lo=v then e.hi else e.lo

private theorem other_spec {e : Edge} {v : Nat} (h : touches e v) :
    joins e v (other e v) := by
  simp [touches] at h
  rcases h with h|h <;> simp [joins,other,h, Nat.ne_of_lt e.increasing]

private theorem endpoints_unique {e d : Edge} {v w : Nat}
    (he : joins e v w) (hd : joins d v w) : e=d := by
  cases e with
  | mk l h lt =>
    cases d with
    | mk a b ab =>
      simp [joins] at he hd
      congr <;> omega

private def neighborNames (es : List Edge) (v : Nat) :=
  (es.filter (touches · v)).map (other · v)

private theorem mem_names {es : List Edge} {v w : Nat} :
    w ∈ neighborNames es v ↔ ∃ e ∈ es, joins e v w := by
  constructor
  · intro h
    obtain ⟨e,hin,rfl⟩ := List.mem_map.mp h
    obtain ⟨he,ht⟩ := List.mem_filter.mp hin
    exact ⟨e,he,other_spec ht⟩
  · rintro ⟨e,he,hj⟩
    simp [joins] at hj
    rcases hj with ⟨hl,hh⟩|⟨hl,hh⟩
    · exact List.mem_map.mpr ⟨e,List.mem_filter.mpr ⟨he,by simp [touches,hl]⟩,by simp [other,hl,hh]⟩
    · have ne := Nat.ne_of_lt e.increasing
      exact List.mem_map.mpr ⟨e,List.mem_filter.mpr ⟨he,by simp [touches,hh]⟩,by simpa [other,← hh,ne] using hl⟩

private theorem neighbor_unique (es : List Edge) (v : Nat) (nd : es.Nodup) :
    (neighborNames es v).Nodup := by
  induction es with
  | nil => simp [neighborNames]
  | cons e es ih =>
    obtain ⟨ne,nod⟩ := List.nodup_cons.mp nd
    by_cases ht : touches e v
    · simp only [neighborNames,List.filter_cons,ht,ite_true,List.map_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_,ih nod⟩
      intro h
      obtain ⟨d,hd,hj⟩ := mem_names.mp h
      exact ne ((endpoints_unique (other_spec ht) hj).symm ▸ hd)
    · simpa [neighborNames,ht] using ih nod

/-- The unordered red pairs are packed exactly once and each incident edge
contributes one to the degree of either endpoint. -/
theorem graph_degree (n : Nat) (es : List Edge) (nd : es.Nodup)
    (bound : ∀ e ∈ es, e.hi<n) (v : Fin n) :
    (graph n es).degree v = simpleDegree es v.val := by
  let actual := (List.finRange n).filter ((graph n es).adj v)
  have nd' : (actual.map Fin.val).Nodup :=
    List.pairwise_map.mpr (((List.nodup_finRange n).filter _).imp (fun h e => h (Fin.ext e)))
  have mem (w : Nat) : w ∈ actual.map Fin.val ↔ w ∈ neighborNames es v.val := by
    rw [mem_names]
    constructor
    · intro hs
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hs
      exact (graph_adj _ _ _).mp (List.mem_filter.mp hi).2
    · rintro ⟨e,he,hj⟩
      have hb := bound e he
      have lt := e.increasing
      have hw : w<n := by simp [joins] at hj; omega
      let i : Fin n := ⟨w,hw⟩
      exact List.mem_map.mpr ⟨i,List.mem_filter.mpr ⟨List.mem_finRange _,(graph_adj ..).mpr ⟨e,he,hj⟩⟩,rfl⟩
  have perm : (actual.map Fin.val).Perm (neighborNames es v.val) := by
    apply List.perm_iff_count.mpr
    intro w
    simp only [nd'.count,(neighbor_unique es v.val nd).count,mem]
  simpa only [actual,List.length_map,neighborNames,simpleDegree,List.countP_eq_length_filter,Graph.degree]
    using perm.length_eq

private theorem red_bound {v f : Nat} (C : ClosedTrace v f) :
    ∀ e ∈ reds (sideTrace C.faces), e.hi < v+1 := by
  intro e he
  have hn := reds_seen he
  have hm : e ∈ (sideTrace C.faces).map Event.edge := List.count_pos_iff.mp hn
  obtain ⟨ev,hm,eq⟩ := List.mem_map.mp hm
  obtain ⟨i,_,hs⟩ := List.mem_flatMap.mp hm
  have h := C.bounded i
  have ht := (C.faces i).yz
  simp only [Face.sides,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl|rfl|rfl <;> subst e <;> first | exact h | exact Nat.lt_trans ht h

def witnessGraph {v f : Nat} (C : ClosedTrace v f) : Graph (v+1) :=
  graph (v+1) (reds (sideTrace C.faces))

theorem witness_degree {v f : Nat} (C : ClosedTrace v f) (x : Fin (v+1)) :
    (witnessGraph C).degree x = C.ledger.redDegree x.val :=
  (graph_degree _ _ (reds_nodup _) (red_bound C) x).trans
    ((replay_accurate C.accepted).redDegree x.val).symm

/-- Terminal counters in permanent-name order. -/
def witnessDegrees {v f : Nat} (C : ClosedTrace v f) :=
  (List.range (v+1)).map C.ledger.redDegree

private theorem cast_degree {n m : Nat} (h : n=m) (G : Graph n) (x : Fin m) :
    (h ▸ G : Graph m).degree x = G.degree (Fin.cast h.symm x) := by
  subst m; rfl

theorem witness_realizes {v f : Nat} (C : ClosedTrace v f) :
    let len : (witnessDegrees C).length = v+1 := by simp [witnessDegrees]
    (len.symm ▸ witnessGraph C : Graph (witnessDegrees C).length).Realizes (witnessDegrees C) := by
  dsimp only
  have len : (witnessDegrees C).length=v+1 := by simp [witnessDegrees]
  intro x
  have hh := witness_degree C (Fin.cast len x)
  have val : (witnessDegrees C)[x.val] = C.ledger.redDegree x.val := by simp [witnessDegrees]
  exact ((cast_degree len.symm _ x).trans hh).trans val.symm

/-- A consumption check may close vertices in any order. Matching the input
as a multiset is sufficient to relabel the returned simple graph. -/
theorem graph_of_histogram {v f : Nat} (C : ClosedTrace v f) (ds : List Nat)
    (perm : (witnessDegrees C).Perm ds) : Graphic ds :=
  (graphic_perm perm).mp ⟨_, witness_realizes C⟩

/-- The triangle host keeps both red and blue edges. -/
def host {v f : Nat} (C : ClosedTrace v f) := graph (v+1) C.ledger.sealed

theorem red_subgraph {v f : Nat} (C : ClosedTrace v f) (i j : Fin (v+1))
    (h : (witnessGraph C).adj i j) : (host C).adj i j := by
  obtain ⟨edge,hr,linked⟩ := (graph_adj _ i j).mp h
  have seen := reds_seen hr
  have inv := replay_accurate C.accepted
  have cap := inv.cap edge
  have pending := inv.pending edge
  simp [C.closed] at pending
  exact (graph_adj _ i j).mpr ⟨edge,(inv.sealed edge).mpr (by omega),linked⟩

/-- Under the geometric-to-minor bridge for the host, edge deletion and
multiset relabelling deliver the project's exact potential-planarity predicate. -/
theorem planar_of_host {v f : Nat} (C : ClosedTrace v f) (ds : List Nat)
    (p : (witnessDegrees C).Perm ds) (hp : (host C).Planar) : Planaric ds := by
  have planar := Graph.planar_subgraph_map hp id (fun _ _ h => h) (red_subgraph C)
  have castPlanar {n m : Nat} (h : n=m) (G : Graph n) : G.Planar → (h ▸ G : Graph m).Planar := by
    subst m; exact id
  apply (planaric_perm p).mp
  have eq : v+1=(witnessDegrees C).length := by simp [witnessDegrees]
  exact ⟨eq ▸ witnessGraph C, witness_realizes C, castPlanar eq _ planar⟩

end Recognition.Witness
