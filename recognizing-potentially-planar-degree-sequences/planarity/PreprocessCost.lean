import ShortBoundary

/-! Explicit catalogue cardinality and the number of actual decoding
attempts made by the nested generator, including unsuccessful attempts. -/
namespace Recognition.PreprocessCost
open Recognition.BoundaryState Recognition.ShortBoundary PlanarDegrees.Frontier

def probes (ds : List Nat) :=
  (words (cutoff ds.length)).length * ((ResidualTable.table ds).length *
    ((ds.length+1)*(2*ds.length+1)))

theorem probes_le (ds : List Nat) (mass : ds.sum≤6*ds.length) :
    probes ds ≤ 2^(268428*(ds.length.sqrt+1)) := by
  let n := ds.length
  let S := n.sqrt+1
  have positive : 0<S := by simp [S]
  have hi : n<S*S := Nat.lt_succ_sqrt n
  have cost : cutoff n+1 ≤ 268402*S := by
    have sq : (220^2*n).sqrt<220*S := Nat.sqrt_lt.mpr (by nlinarith)
    unfold cutoff
    omega
  have weight : 4*(ds.sum.sqrt+1) ≤ 16*S := by
    have sq : ds.sum.sqrt<3*S := Nat.sqrt_lt.mpr (by dsimp only [n] at hi; nlinarith)
    omega
  have p : S≤2^S := Nat.le_of_lt Nat.lt_two_pow_self
  have v : n+1≤2^(2*S) := by
    have sq := Nat.mul_le_mul p p
    rw [Nat.two_mul,Nat.pow_add]
    exact le_trans (by omega : n+1≤S*S) sq
  have f : 2*n+1≤2^(3*S) := by
    have h : 2*n+1 ≤ 2*2^(2*S) := by omega
    have unit : 2≤2^S := by have z := Nat.pow_le_pow_right (n := 2) (by decide) (show 1≤S by omega); simpa using z
    have := h.trans (Nat.mul_le_mul_right _ unit)
    rwa [← Nat.pow_add,show S+2*S=3*S by omega] at this
  have word : (words (cutoff n)).length ≤ 2^(268402*S) :=
    (Nat.le_of_lt (by have := word_count (cutoff n); omega : (words (cutoff n)).length<2^(cutoff n+1))).trans
      (Nat.pow_le_pow_right (by decide) cost)
  have hist : (ResidualTable.table ds).length ≤ 2^(2*S)*2^(16*S) :=
    (ResidualTable.table_bound _).trans (Nat.mul_le_mul v (Nat.pow_le_pow_right (by decide) weight))
  apply (Nat.mul_le_mul word (Nat.mul_le_mul hist (Nat.mul_le_mul v f))).trans
  simp only [← Nat.pow_add]
  apply Nat.pow_le_pow_right (by decide)
  dsimp [S,n]
  omega

theorem catalogue_le_probes (ds : List Nat) : (catalogue ds).length≤probes ds := by
  have cap {A B : Type} (xs : List A) (g : A → List B) (k : Nat) (h : ∀ x, (g x).length≤k) :
      (xs.flatMap g).length≤xs.length*k := by
    induction xs with
    | nil => simp
    | cons x xs ih => simpa [Nat.succ_mul,Nat.add_comm] using Nat.add_le_add (h x) ih
  apply cap
  intro bs
  apply cap
  intro r
  have limit := cap (List.range (ds.length+1))
    (fun u => (List.range (2*ds.length+1)).filterMap (fun j => decode ds.length bs r u j)) _
    (fun _ => (List.length_filterMap_le ..).trans_eq List.length_range)
  simpa only [List.length_range] using limit

theorem catalogue_single_exponential (ds : List Nat) (h : ds.sum≤6*ds.length) :
    (catalogue ds).length≤2^(268428*(ds.length.sqrt+1)) :=
  (catalogue_le_probes ds).trans (probes_le ds h)

#print axioms catalogue_single_exponential
end Recognition.PreprocessCost

namespace Recognition.PreprocessCost
open Recognition.BoundaryState Recognition.ShortBoundary Recognition.MarkedPlane PlanarDegrees.Frontier

abbrev Proposal := List Bool × Multiset Nat × Nat × Nat

def attempts (ds : List Nat) : List Proposal :=
  (words (cutoff ds.length)).flatMap fun bs => (ResidualTable.table ds).flatMap fun rem =>
    (List.range (ds.length+1)).flatMap fun u =>
      (List.range (2*ds.length+1)).map (fun f => (bs,rem,u,f))

/-- The number of calls includes each rejected bit string, not just the
population of accepted rows. -/
theorem exact_attempts (ds : List Nat) :
    (attempts ds).length=probes ds ∧ (attempts ds).filterMap (fun p => decode ds.length p.1 p.2.1 p.2.2.1 p.2.2.2) =
      catalogue ds := by
  have batch {A B : Type} (xs : List A) (g : A → List B) (k : Nat) (h : ∀ x, (g x).length=k) :
      (xs.flatMap g).length=xs.length*k := by
    induction xs with
    | nil => simp
    | cons a xs ih => simp [ih,h,Nat.succ_mul,Nat.add_comm]
  constructor
  · apply batch
    intro bs
    apply batch
    intro r
    have val := batch (List.range (ds.length+1))
      (fun u => (List.range (2*ds.length+1)).map (fun f => (bs,r,u,f))) (2*ds.length+1) (fun _ => by simp)
    simpa only [List.length_range] using val
  · simp only [catalogue,table,attempts,List.filterMap_flatMap,List.filterMap_map,Function.comp_def]

private theorem unique_length {k} (f : Fin k → Nat) (xs : List (Fin k)) :
    (unique f xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [unique]
  | cons a xs ih => rw [unique]; split <;> simp <;> omega

theorem decode_dimensions {bits : List Bool} {V : View} (parsed : MarkedPlane.decode bits=some V) :
    (activeReps V).length ≤ V.ribbon.length ∧ (OverlayRead.unions V V.ribbon.length).length ≤ V.ribbon.length^2 ∧
    6*V.ribbon.length+1≤bits.length ∧ ∀ x∈V.roles++V.values, x<2^bits.length := by
  have rep := (unique_length (fun i : Fin V.ribbon.length => (V.vertexKey i).val) _).trans (List.length_filter_le (fun i : Fin V.ribbon.length => OverlayRead.tag V i==0) (List.finRange _))
  have all (xs : List (Fin V.ribbon.length)) :
      (xs.flatMap fun i => (List.finRange V.ribbon.length).map (i,·)).length = xs.length*V.ribbon.length := by
    induction xs with
    | nil => simp
    | cons v vs ih => simp [ih,Nat.succ_mul,Nat.add_comm]
  obtain ⟨n,_,_,_,_,_,fields⟩ := decode_bounds parsed
  refine ⟨by simpa only [activeReps,List.length_finRange] using rep,?_,n,fields⟩
  unfold OverlayRead.unions
  apply (List.length_filter_le ..).trans
  simp [all,pow_two]

#print axioms exact_attempts
#print axioms decode_dimensions
end Recognition.PreprocessCost
