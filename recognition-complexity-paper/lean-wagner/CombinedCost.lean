import AlgorithmCost
import IncidenceMeter
import OutputCost

/-! Assemble preprocessing, concrete metered triangle updates, coloured
incidence construction, quasipolynomial GI and labelled witness output into
one search. The scalar tariff equals its uncapped value at every comparison
between an actual proposal and an actual catalogue entry. -/
namespace Recognition.CombinedCost
open Recognition.QuotientDP Recognition.WitnessTable Recognition.AlgorithmCost
open Recognition.IncidenceMeter

def scalarFee (s t : State n) := min (scalar s t).2 (32*(n+2)^2)

def prepare (s t : State n) := (materialize s).2+(materialize t).2+scalarFee s t

def compare (I : GI) (s t : State n) : Bool × Nat :=
  let a := materialize s
  let b := materialize t
  let g := I.run a.1 b.1
  ((scalar s t).1 && g.1,a.2+b.2+scalarFee s t+g.2)

theorem compare_eq (I : GI) (s t : State n) : compare I s t=compareMeter I prepare s t := by
  simp only [compare,compareMeter,prepare,materialize_eq,scalar]

@[simp] theorem equals_detector (I : GI) (s t : State n) : (compare I s t).1=detector I s t := by
  rw [compare_eq,compareMeter_val]

theorem preparation (s t : State n) : prepare s t≤20100*(n+2)^8 := by
  have sFee := materialize_cost s
  have tFee := materialize_cost t
  have f : scalarFee s t≤32*(n+2)^2 := Nat.min_le_right .. 
  have power := Nat.pow_le_pow_right (n := n+2) (by omega) (by decide : 2≤8)
  dsimp only [prepare]; omega

private theorem decode_residual {n src r u k} {t : State n}
    (ok : BoundaryState.decode n src r u k=some t) : t.remaining=r := by
  unfold BoundaryState.decode at ok; split at ok
  · exact Option.some.inj ok ▸ rfl
  · cases h : MarkedPlane.decode src with
    | none => simp [h] at ok
    | some V =>
      simp only [h,Option.bind_some] at ok
      unfold BoundaryState.fromView at ok
      dsimp only at ok
      split at ok
      · contradiction
      · exact Option.some.inj ok ▸ rfl

theorem catalogue_residual (ds : List Nat) {t : State ds.length} (hit : t∈ShortBoundary.catalogue ds) :
    t.remaining.card≤ds.length := by
  obtain ⟨_,r,_,_,_,h,_,_,ok⟩ := BoundaryState.table_mem.mp hit
  rw [decode_residual ok]
  exact Multiset.card_le_card ((ResidualTable.mem_table ..).mp h)

theorem scalarFee_exact (ds : List Nat) {t : State ds.length} (hit : t∈ShortBoundary.catalogue ds)
    {e : Entry ds.length} (good : Good bound (ds : Multiset Nat) e) :
    scalarFee (prune e.raw) t=(scalar (prune e.raw) t).2 := by
  have r : e.raw.remaining≤(ds : Multiset Nat) := by rw [← FullDegrees.histogram good]; exact Multiset.le_add_right .. 
  exact Nat.min_eq_left (scalar_cost _ _ (Multiset.card_le_card r) (catalogue_residual ds hit))

/-- The tariff of every successful proposal examined in the next first-match
table scan equals the charge obtained from its full residual histograms. -/
theorem scanned_scalar (ds : List Nat) (cmp : State ds.length → State ds.length → Bool)
    {t : State ds.length} (hit : t∈ShortBoundary.catalogue ds) {e y : Entry ds.length}
    (before : e∈layer cmp (ShortBoundary.catalogue ds) bound (ds : Multiset Nat) k)
    (after : y∈next bound e) : scalarFee (prune y.raw) t=(scalar (prune y.raw) t).2 :=
  scalarFee_exact ds hit (next_sound _ _ _ _ (layer_sound _ _ _ _ _ _ before) after)

theorem initial_scalar (ds : List Nat) {t : State ds.length} (hit : t∈ShortBoundary.catalogue ds) :
    scalarFee (prune (init (ds : Multiset Nat)).raw) t=(scalar (prune (init (ds : Multiset Nat)).raw) t).2 :=
  scalarFee_exact ds hit (bound := 0) FullRun.init

/-- The loop calls the concrete metered triangle program once per proposal;
its return value and charge travel together through the list collector. -/
def measuredLayer (I : GI) (table : List (State n)) (bound : Nat) (target : Multiset Nat) :
    Nat → List (Entry n) × Nat
  | 0 => WitnessCost.store (compare I) table [init target]
  | k+1 =>
    let (past,c) := measuredLayer I table bound target k
    let (ys,a) := LayerCost.expand (fun e => LayerCost.collect (StepCost.charged bound e) (candidates n)) past
    let (out,b) := WitnessCost.store (compare I) table ys
    (out,c+a+b+1)

theorem measured_eq (I : GI) (table : List (State n)) (bound target k) :
    measuredLayer I table bound target k =
      WitnessCost.run (compare I) (fun e a => (StepCost.charged bound e a).2) table bound target k := by
  have one (e : Entry n) : LayerCost.collect (StepCost.charged bound e) (candidates n) =
      WitnessCost.propose (fun e a => (StepCost.charged bound e a).2) bound e := by
    unfold WitnessCost.propose
    congr 1; funext a; apply Prod.ext
    · exact StepCost.charged_val bound e a
    · rfl
  induction k with
  | zero => rfl
  | succ k ih => simp only [measuredLayer,WitnessCost.run,ih,one]

def search (I : GI) (x : Nat) (ds : List Nat) (f : Nat) :=
  let d := x::ds
  let catalogue := GeneratorCost.preprocess d
  let rows := measuredLayer I catalogue.1 (f+1) (d : Multiset Nat) (f+1)
  let out := OutputCost.finish d (f+1) rows.1
  (out.1,catalogue.2+rows.2+out.2)

theorem search_eq (I : GI) (x : Nat) (ds : List Nat) (f : Nat) :
    (search I x ds f).1 = realize (detector I) (ShortBoundary.catalogue (x::ds)) (x::ds) f := by
  simp only [search,measured_eq,WitnessCost.output,GeneratorCost.preprocess_eq,equals_detector]
  exact OutputCost.finish_eq .. 

theorem search_cost (I : GI) : ∃ C : Nat, ∀ x ds f,
    f+1≤2*(x::ds : List Nat).length → (x::ds).sum≤6*(x::ds).length →
    Fits (x::ds).length C (search I x ds f).2 := by
  obtain ⟨C,total⟩ := AlgorithmCost.search_cost I 20100 8
  refine ⟨max C 268957+1,?_⟩
  intro x ds f len mass
  have cmp : @compare I (n := (x::ds).length)=compareMeter I prepare := by funext s t; exact compare_eq I s t
  have first := total (x::ds) prepare preparation mass (f+1) (f+1) len
  have last := OutputCost.catalogue_cost x ds (detector I) f len mass
  unfold search
  dsimp only
  rw [measured_eq]
  apply Fits.plus
  · rwa [cmp]
  · simp only [WitnessCost.output,equals_detector,GeneratorCost.preprocess_eq]
    exact last

theorem large_reference (I : GI) (x : Nat) (ds : List Nat) (big : 4≤(x::ds).length)
    (mass : (x::ds).sum≤6*(x::ds).length) :
    (search I x ds (2*(x::ds).length-5)).1=MainResult.findWith (detector I) (x::ds) := by
  rw [search_eq]
  simp only [MainResult.findWith,List.length_cons] at *
  rw [ite_eq_right (Nat.not_lt.mpr mass),ite_eq_right (Nat.not_lt.mpr big)]

#print axioms search_eq
#print axioms search_cost
end Recognition.CombinedCost
