import WireCost

/-! The bit-string entry point can also write the individual, oriented
endpoint pairs. Each unordered edge appears once with its smaller label first. -/
namespace Recognition.WireOutput
open SparseBoundary LayerCost AlgorithmCost

theorem graph_sound {bs ds} {G : Graph ds.length} (hit : (WireCost.run bs).1=some ⟨ds,G⟩) :
    Wire.readDegrees bs=some ds ∧ ds≠[] ∧ G.Planar ∧ G.Realizes ds := by
  simp only [WireCost.run,(WireSearch.decode_work bs).1] at hit
  cases h : WireSearch.parse bs with
  | none => simp only [h] at hit;contradiction
  | some xs =>
    cases xs with
    | nil => simp only [h] at hit;contradiction
    | cons x xs =>
      simp only [h,Option.map_eq_some_iff] at hit
      obtain ⟨g,given,eq⟩:=hit
      cases eq
      exact ⟨((WireSearch.parse_exact ..).mp h).1,by simp,WireCost.construct_sound given⟩

private def emit (G : Graph n) (p : Fin n × Fin n) :=
  (if decide (p.1<p.2) && G.adj p.1 p.2 then some p else none,20*(n+1)^3)

def pairs (G : Graph n) : List (Fin n × Fin n) × Nat :=
  let grid := (List.finRange n).product (List.finRange n)
  let scan := collect (emit G) grid
  (scan.1,scan.2+4*(n+1)^2+1)

theorem pairs_eq (G : Graph n) : (pairs G).1=WireSearch.edges G := by
  simp only [pairs,collect_val,WireSearch.edges,emit,←List.filterMap_eq_filter]
  rfl

theorem pairs_cost (G : Graph n) : (pairs G).2≤32*(n+2)^5 := by
  have c:= collect_cost (emit G) ((List.finRange n).product (List.finRange n)) (20*(n+1)^3) (fun _ _ => le_rfl)
  have size : ((List.finRange n).product (List.finRange n)).length=n*n := by simp [List.product,List.length_flatMap]
  rw [size] at c
  apply (Nat.add_le_add_right (Nat.add_le_add_right c _) _).trans
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4)]

def run (bs : List Bool) : Option ((ds : List Nat) × List (Fin ds.length × Fin ds.length)) × Nat :=
  let found := WireCost.run bs
  match found.1 with
  | none => (none,found.2+1)
  | some ⟨ds,g⟩ =>
    let result := pairs g
    (some ⟨ds,result.1⟩,found.2+result.2+1)

theorem accepts (sep : SeparatorInput.WeightedPlanarSeparator) (bs : List Bool) :
    (run bs).1.isSome ↔ Wire.degreeLanguage Planaric bs := by
  rw [←WireCost.run_iff sep]
  cases h : (WireCost.run bs).1 <;> simp [run,h]

theorem sound {bs ds} {es : List (Fin ds.length × Fin ds.length)} (hit : (run bs).1=some ⟨ds,es⟩) :
    Wire.readDegrees bs=some ds ∧ ds≠[] ∧ es.Nodup ∧
      ∃ G : Graph ds.length,G.Planar ∧ G.Realizes ds ∧ ∀ i j,((i,j)∈es ↔ i<j ∧ G.adj i j=true) := by
  unfold run at hit
  cases h : (WireCost.run bs).1 with
  | none => simp only [h] at hit;contradiction
  | some witness =>
    obtain ⟨d,g⟩:=witness
    simp only [h,Option.some.injEq,pairs_eq] at hit
    cases hit
    obtain ⟨raw,non,p,deg⟩:=graph_sound h
    exact ⟨raw,non,WireSearch.edges_nodup _,g,p,deg,WireSearch.edges_spec g⟩

theorem cost (bs : List Bool) : (run bs).2≤6*bs.length+4+2^(6000002*((WireSearch.arity bs).sqrt+1)) := by
  let n:=WireSearch.arity bs
  have old:=WireCost.run_cost bs
  have small : Fits n 6000001 (2^(6000001*(n.sqrt+1))) := le_rfl
  have widen (c) (h : c≤6000002) : 2^(c*(n.sqrt+1))≤2^(6000002*(n.sqrt+1)) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ h)
  cases h : (WireCost.run bs).1 with
  | none =>
    simp only [run,h]
    have z:=widen 6000001 (by decide)
    dsimp only [n] at z;omega
  | some witness =>
    obtain ⟨ds,G⟩:=witness
    have size : n=ds.length := WireSearch.arity_eq bs (graph_sound h).1
    have result : Fits n 47 (pairs G).2 := by rw [size];exact (pairs_cost G).trans (polynomial ds.length 32 5)
    have b := small.plus result
    change _≤2^(6000002*(n.sqrt+1)) at b
    simp only [run,h]
    dsimp only [n] at b;omega

end Recognition.WireOutput
