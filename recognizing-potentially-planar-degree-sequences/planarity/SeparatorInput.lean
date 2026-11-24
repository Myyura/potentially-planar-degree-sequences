import ShortBoundary
import TracePlanarity

/-! The weighted separator theorem used in the paper. All planar hosts,
vertex costs, residual regions and balance constants are quantified here.
Its specialization to any actual triangular face certificate is proved below. -/
namespace Recognition.SeparatorInput
open SparseBoundary PlanarDegrees.Frontier PlanarDegrees.Topology Recognition.Witness
open Recognition.Outline

/-- Adjacency of graph labels regarded as natural numbers. -/
def adjacent (G : Graph n) (x y : Nat) : Prop :=
  ∃ a b : Fin n, a.val=x ∧ b.val=y ∧ G.adj a b=true

/-- The cost-and-weight planar separator theorem, in its induced-region
form, with cost c, weight c² and balance one half. The argument is a
published geometric theorem explicitly supplied to the algorithmic result. -/
def WeightedPlanarSeparator : Prop := ∀ {n : Nat} (G : Graph n), G.Planar →
  ∀ c : Nat → Nat, (∀ x<n, 0<c x) → Separators (List.range n) (adjacent G) c

private theorem face_edge {F : Face} {x y : Nat} (a : x∈corners F) (b : y∈corners F) (ne : x≠y) :
    ∃ e∈sideNames F,Witness.joins e x y=true := by
  simp only [corners,List.mem_cons,List.not_mem_nil,or_false] at a b
  obtain ⟨l,m,h,lm,mh,p,q,r⟩ := F
  simp only [sideNames,Face.sides,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]
  rcases a with rfl|rfl|rfl <;> rcases b with rfl|rfl|rfl <;> simp_all [joins]

theorem host {v f} (sep : WeightedPlanarSeparator) (C : ClosedTrace v f)
    (terminal : (f+1)+4=2*(v+1)) (c : Nat → Nat) (pos : ∀ x<v+1,0<c x) :
    Separators (List.range (v+1)) (cofacial (List.ofFn C.faces)) c := by
  obtain plan := TracePlanarity.host_planar C terminal
  intro xs sub nd non
  obtain ⟨cut,region,inc,nod,cost,half,apart⟩ := sep (Witness.host C) plan c pos xs sub nd non
  refine ⟨cut,region,inc,nod,cost,half,?_⟩
  intro x hx y hy xc yc meet
  by_cases eq : x=y
  · simp [eq]
  obtain ⟨F,mem,inside,both⟩ := meet
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
  obtain ⟨e,side,joins⟩ := face_edge inside both eq
  have seen : e∈(sideTrace C.faces).map Event.edge := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp side
    exact List.mem_map.mpr ⟨a,List.mem_flatMap.mpr ⟨i,List.mem_finRange i,ha⟩,rfl⟩
  have positive := List.count_pos_iff.mpr seen
  have paired := (paired_iff_closed.mpr ⟨_,C.accepted,C.closed⟩) e
  have twice : occurrences (sideTrace C.faces) e=2 := paired.resolve_left (by
    change _≠0; exact Nat.ne_of_gt positive)
  have keep := ((replay_accurate C.accepted).sealed e).mpr twice
  let a : Fin (v+1) := ⟨x,List.mem_range.mp (sub hx)⟩
  let b : Fin (v+1) := ⟨y,List.mem_range.mp (sub hy)⟩
  exact apart x hx y hy xc yc ⟨a,b,rfl,rfl,(graph_adj C.ledger.sealed a b).mpr ⟨e,keep,joins⟩⟩

end Recognition.SeparatorInput
