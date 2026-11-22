import Augmentation

/-! Exhaustive, fixed-length reference implementation of face recognition. -/
namespace Recognition.FaceSearch
open SparseBoundary PlanarDegrees.Frontier TraceCheck

private def allRows (w : Nat) : List (Record w) := do
  let x ← List.finRange (2^w)
  let y ← List.finRange (2^w)
  let z ← List.finRange (2^w)
  let xy ← [false,true]
  let xz ← [false,true]
  let yz ← [false,true]
  return ⟨BitVec.ofFin x,BitVec.ofFin y,BitVec.ofFin z,xy,xz,yz⟩

private theorem rows_complete {w} (r : Record w) : r ∈ allRows w := by
  obtain ⟨x,y,z,xy,xz,yz⟩ := r
  have bit (a : Bool) : a ∈ [false,true] := by cases a <;> simp
  unfold allRows
  simp only [List.bind_eq_flatMap,List.mem_flatMap,List.mem_finRange,true_and,
    List.pure_def,List.mem_singleton]
  exact ⟨x.toFin,y.toFin,z.toFin,xy,bit _,xz,bit _,yz,bit _,rfl⟩

private def vectors (xs : List α) : (m : Nat) → List (Vector α m)
  | 0 => [#v[]]
  | m+1 => (vectors xs m).flatMap fun v => xs.map v.push

private theorem covers (xs : List α) (h : ∀ x, x ∈ xs) (m : Nat) (v : Vector α m) :
    v ∈ vectors xs m := by
  induction m with
  | zero => simp [vectors,Vector.eq_empty (xs := v)]
  | succ m ih =>
    exact List.mem_flatMap.mpr ⟨v.pop,ih v.pop,List.mem_map.mpr ⟨v.back,h _,by simp⟩⟩

/-- An accepting record has exactly 2n−4 rows. The reference search uses
permanent labels and returns the first witness in the specified enumeration. -/
def findRows (x : Nat) (ds : List Nat) : Option (Records ds.length (2*(ds.length+1)-5)) :=
  (vectors (allRows (cost ds.length)) _).find? (verify (x::ds))

theorem findRows_iff (x : Nat) (ds : List Nat) (hn : 4≤ds.length+1) :
    (findRows x ds).isSome ↔ Planaric (x::ds) := by
  rw [Augment.face_certificate_iff x ds hn]
  constructor
  · intro yes
    obtain ⟨r,eq⟩ := Option.isSome_iff_exists.mp yes
    exact ⟨_,r,List.find?_some eq⟩
  · rintro ⟨f,r,yes⟩
    have count := (verify_sound _ r yes).2.1
    have eq : f=2*(ds.length+1)-5 := by omega
    subst f
    rw [findRows,List.isSome_find?]
    exact List.any_eq_true.mpr ⟨r,covers _ rows_complete _ _,yes⟩

/-- Both the returned graph and the final degree multiset belong to the
certificate that was selected by the executable search. -/
theorem found_graph {x : Nat} {ds : List Nat} {r} (h : findRows x ds=some r) :
    ∃ C : PlanarDegrees.Topology.ClosedTrace ds.length (2*(ds.length+1)-5),
      readGraph r=some (Witness.witnessGraph C) ∧
      (Witness.witnessDegrees C).Perm (x::ds) ∧ (Witness.witnessGraph C).Planar := by
  have yes := List.find?_some (p := verify (x::ds)) h
  obtain ⟨C,graph,perm,_⟩ := verify_recovers_witness _ r yes
  refine ⟨C,graph,perm,?_⟩
  exact Graph.planar_subgraph_map (TracePlanarity.host_planar C (verify_sound _ r yes).2.1)
    id (fun _ _ eq => eq) (Witness.red_subgraph C)

end Recognition.FaceSearch
