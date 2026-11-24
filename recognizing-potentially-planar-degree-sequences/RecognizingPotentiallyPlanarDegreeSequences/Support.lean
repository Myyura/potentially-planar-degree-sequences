import RecognizingPotentiallyPlanarDegreeSequences.SupportExists
import RecognizingPotentiallyPlanarDegreeSequences.SupportExpand
import SparseBoundary.GraphUnion

/-! The attained minimum/maximum identity of Lemma 3.1 for the ordinary
simple-graph realization predicate. Graph planarity throughout is the
existing library's no-`K₅`, no-`K₃,₃`-minor predicate (Wagner's criterion).
The signed score is important when a candidate has more loops than pairs. -/
namespace RecognizingPotentiallyPlanarDegreeSequences.Support
open SparseBoundary SparseBoundary.Graph RecognizingPotentiallyPlanarDegreeSequences.Budget
namespace Multi

def score (M : Multi n) : Int := (M.pairs : Int)-(M.loops : Int)

theorem cost_eq_edges_sub_score (M : Multi n) : (M.cost : Int)=(M.edges : Int)-M.score := by
  have eq := M.cost_identity; unfold score; omega

theorem feasible_iff_candidate {h : List Nat} {ell t : Nat} (enough : ell≤h.sum)
    (even : (h.sum+ell)%2=0) (pos : ∃ x∈h, 0<x) :
    Feasible h ell t ↔ ∃ C : Candidate h ell, C.graph.cost≤t := by
  refine ⟨normalize enough even,?_⟩
  rintro ⟨C,le⟩
  exact monotone pos (C.graph.realize C.planar C.capacity C.balance) le

/-- The optimizer is an actual multigraph. Its signed support score dominates
all the admissible `s(M)-λ(M)`, its cost is the least simple planar budget,
and every larger number of twos is feasible. -/
theorem support_minimum_formula (h : List Nat) (ell : Nat) (enough : ell≤h.sum)
    (even : (h.sum+ell)%2=0) (pos : ∃ x∈h, 0<x) :
    ∃ C : Candidate h ell,
      (∀ D : Candidate h ell, D.graph.score≤C.graph.score) ∧
      IsMinimum h ell C.graph.cost ∧
      (C.graph.cost : Int)=(((h.sum-ell)/2 : Nat) : Int)-C.graph.score ∧
      ∀ t, Feasible h ell t ↔ C.graph.cost≤t := by
  obtain ⟨S⟩ := candidate_exists h ell enough even
  obtain ⟨t,ht⟩ := exists_minimum ⟨_,S.graph.realize S.planar S.capacity S.balance⟩
  obtain ⟨C,ct⟩ := normalize enough even ht.1
  have best := C.graph.realize C.planar C.capacity C.balance
  have eq : C.graph.cost=t := Nat.le_antisymm ct (ht.2 _ best)
  refine ⟨C,?_,eq ▸ ht,?_,fun k => eq ▸ minimum_iff pos ht k⟩
  · intro D
    have dd := D.graph.realize D.planar D.capacity D.balance
    have lo := ht.2 _ dd
    have cd := C.graph.cost_eq_edges_sub_score
    have dd := D.graph.cost_eq_edges_sub_score
    have cb := C.balance; have db := D.balance; omega
  · have cb := C.balance
    have eqe : C.graph.edges=(h.sum-ell)/2 := by omega
    rw [←eqe]; exact C.graph.cost_eq_edges_sub_score

private theorem loops_le_edges (M : Multi n) : M.loops≤M.edges := by
  induction M with
  | nil => rfl
  | cons L r K ih => simp only [loops,edges]; omega

private theorem planaric_matching (k : Nat) : Planaric (List.replicate (2*k) 1) := by
  have edge : Planaric [1,1] := by
    let E : Graph 2 := ⟨1⟩
    exact ⟨E,by unfold Graph.Realizes; decide,planar_of_few_high E (by decide)⟩
  induction k with
  | zero =>
    let Z : Graph 0 := ⟨0⟩
    exact ⟨Z,fun i => i.elim0,planar_of_few_high Z (by decide)⟩
  | succ k ih =>
    rw [Nat.mul_succ,List.replicate_add]
    exact planaric_append ih edge

/-- If the available leaves already meet or exceed the core demands,
all remaining leaves pair off and the minimum is zero. -/
theorem excess_leaves (h : List Nat) (ell : Nat) (enough : h.sum≤ell)
    (even : (h.sum+ell)%2=0) : IsMinimum h ell 0 := by
  obtain ⟨C⟩ := candidate_exists h h.sum (Nat.le_refl _) (by omega)
  have coarse := C.graph.realize C.planar C.capacity C.balance
  have eqe := C.balance; have ident := C.graph.cost_identity; have hl := loops_le_edges C.graph
  have z : C.graph.cost=0 := by omega
  simp only [z,Feasible,List.replicate_zero,List.nil_append] at coarse
  let k := (ell-h.sum)/2
  have num : h.sum+2*k=ell := by dsimp [k]; omega
  have all := planaric_append coarse (planaric_matching k)
  refine ⟨?_,fun _ _ => Nat.zero_le _⟩
  simpa only [Feasible,List.replicate_zero,List.nil_append,List.append_assoc,←List.replicate_add,num] using all

end Multi
end RecognizingPotentiallyPlanarDegreeSequences.Support
