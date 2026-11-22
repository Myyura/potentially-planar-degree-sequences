import ElementaryRun
import LayoutMeter
import AlgorithmCost
import OutputCost
import SparseMeter
import BagMeter
import CombinedCost

/-! Measured elementary comparison on the finite catalogue. Every unsuccessful
size or width check has a bounded branch; only successful layout searches
trigger homomorphism tables. -/
namespace Recognition.ElementaryCost
open Finset StateIso QuotientDP ElementaryCompare ElementaryCoverage AlgorithmCost
open LayerCost WitnessTable

/-- Count all factor sums and products and one signed accumulation per
target subset. The empty target has at most one function from the pattern. -/
def bagWork (A : Colored k) (B : Colored l) : Nat :=
  if h : 0<l then
    ∑ Y∈(univ : Finset (Fin l)).powerset,
      (BagArithmetic.arithmetic (⟨0,h⟩ : Fin l) (List.finRange k) (BagHom.constraints A B Y)+2)
  else 2

theorem measured_bag (A : Colored k) (B : Colored l) :
    BagMeter.compare A B=(BagHom.compare A B (List.finRange k),bagWork A B) := by
  apply Prod.ext
  · exact BagMeter.compare_eq A B
  · simp only [BagMeter.compare,bagWork]
    by_cases pos : 0<l
    · simp only [dite_eq_left pos,BagMeter.subsets_cost]
    · simp only [dite_eq_right pos]

private theorem widen {n a b x : Nat} (h : Fits n a x) (le : a ≤ b) : Fits n b x :=
  h.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le))

private theorem scaled (d n k : Nat) (small : k≤budget n) :
    Fits n (d*6601) (2^(d*(k+1))) := by
  apply Nat.pow_le_pow_right (by decide)
  unfold budget at small
  calc d*(k+1) ≤ d*(6601*(n.sqrt+1)) := Nat.mul_le_mul_left _ (by omega)
       _ = d*6601*(n.sqrt+1) := by ring

private theorem bag_bound {A : Colored k} {B : Colored l} (n : Nat) (cap : k≤budget n)
    (room : l≤budget n) (D : BagHom.Layout A (width n)) : Fits n 5036600 (bagWork A B) := by
  rw [bagWork];split <;> rename_i pos
  · have arg := BagArithmetic.total_arithmetic A B (⟨0,pos⟩ : Fin l) (budget n) 84 cap room D
    let K:=budget n
    have big : (∑Y∈(univ : Finset (Fin l)).powerset,
      BagArithmetic.arithmetic (⟨0,pos⟩ : Fin l) (List.finRange k) (BagHom.constraints A B Y))≤2^(762*(K+1)) := arg
    have shift : 2^l*2 ≤ 2^(762*(K+1)) := by
      rw [←Nat.pow_succ]
      apply Nat.pow_le_pow_right (by decide);change l≤K at room;omega
    rw [sum_add_distrib];simp only [sum_const,card_powerset,card_univ,Fintype.card_fin,nsmul_eq_mul]
    have twice := Nat.add_le_add big shift
    have shrink : 2^(762*(K+1))+2^(762*(K+1))=2^(762*(K+1)+1) := by rw [Nat.pow_succ,Nat.mul_two]
    rw [shrink] at twice
    change _ ≤ 2^(5036600*(n.sqrt+1))
    apply twice.trans
    apply Nat.pow_le_pow_right (n:=2) (by decide)
    change 762*(6600*(n.sqrt+1)+1)+1≤5036600*(n.sqrt+1);omega
  · exact widen (constant n 2) (by decide)

/-- One explicit polynomial charge for preparing, reading and reindexing
the coloured graph and for fixed-size counter operations in a unit-cost
table-access model. The homomorphism sums and subset scans are metered
separately and depend on the actual visited order and computed bags. -/
def localFee (n : Nat) := 10000*(n+2)^32

private def referenceRetain (n : Nat) (t : State n) : Option (State n) × Nat :=
  if budget n < orderSize t then (none,localFee n)
  else
    let (p,c) := LayoutMeter.run (pattern t) (width n) (orderSize t)
    (if p.head?.isSome then some t else none, c + localFee n)

private theorem referenceRetain_val (t : State n) :
    (referenceRetain n t).1=if allowed (budget n) (width n) t then some t else none := by
  by_cases h : budget n < orderSize t
  · simp [referenceRetain,ElementaryCompare.allowed,h,Nat.not_le.mpr h]
  · simp [referenceRetain,ElementaryCompare.allowed,h,Nat.le_of_not_lt h,LayoutMeter.output,LayoutSearch.ordered]

private theorem referenceRetain_bound (t : State n) : Fits n 159999 (referenceRetain n t).2 := by
  have fee : Fits n 10096 (localFee n) := polynomial n 10000 32
  by_cases h : budget n < orderSize t
  · simp [referenceRetain,h];exact widen fee (by decide)
  · simp only [referenceRetain,ite_eq_right h]
    have real := LayoutMeter.single_exponential (pattern t) (width n)
    have p : Fits n (24*6601) (LayoutMeter.run (pattern t) (width n) (orderSize t)).2 :=
      real.trans (scaled 24 n _ (Nat.le_of_not_lt h))
    exact widen (p.plus fee) (by decide)

private def referenceComparison (x t : State n) : Bool × Nat :=
  if budget n < orderSize t then (false,localFee n)
  else
    let (tables,plan) := LayoutMeter.run (pattern t) (width n) (orderSize t)
    match tables.head? with
    | none => (false,plan+localFee n)
    | some xs =>
      if orderSize x≠orderSize t then (false,plan+localFee n)
      else (compareOrder x t xs,plan+localFee n*(bagWork (reindex (pattern t) xs) (pattern x)+1))

private theorem referenceComparison_eq (x t : State n) (cert : allowed (budget n) (width n) t=true) :
    (referenceComparison x t).1=compareWith (width n) x t := by
  obtain ⟨xs,ordered,same⟩:=allowed_branch x t cert
  have size:=of_decide_eq_true ((Bool.and_eq_true_iff.mp cert).1)
  change (LayoutSearch.pool (pattern t) (width n) (orderSize t)).head?=some xs at ordered
  simp only [referenceComparison,ite_eq_right (Nat.not_lt.mpr size),LayoutMeter.output,ordered,same]
  split <;> rename_i h
  · simp [compareOrder,ne_comm.mp h]
  · rfl

set_option maxHeartbeats 1000000 in
private theorem referenceComparison_bound (x t : State n) : Fits n 5099999 (referenceComparison x t).2 := by
  have fee : Fits n 10096 (localFee n) := polynomial n 10000 32
  by_cases cond : budget n < orderSize t
  · simp only [referenceComparison,ite_eq_left cond]
    exact widen fee (by decide)
  · have small:=Nat.le_of_not_lt cond
    let P:=LayoutMeter.run (pattern t) (width n) (orderSize t)
    have p : Fits n (24*6601) P.2 :=
      (LayoutMeter.single_exponential ..).trans (scaled 24 n _ small)
    have simple : Fits n 5099999 (P.2+localFee n) := widen (p.plus fee) (by decide)
    simp only [referenceComparison,ite_eq_right cond]
    rw [show LayoutMeter.run (pattern t) (width n) (orderSize t)=P from rfl]
    cases hit : P.1.head? with
    | none => exact simple
    | some xs =>
      by_cases different : orderSize x≠orderSize t
      · simpa only [ite_eq_left different] using simple
      · simp only [ite_eq_right different]
        have loc : LayoutSearch.ordered (pattern t) (width n)=some xs := by
          simpa only [P,LayoutMeter.output,LayoutSearch.ordered] using hit
        obtain ⟨D⟩:=order_layout loc
        have h := bag_bound (A:=reindex (pattern t) xs) (B:=pattern x) n small
          ((not_ne_iff.mp different).trans_le small) D
        have c := h.plus (show Fits n 0 1 by simp [Fits])
        exact widen (p.plus (fee.prod c)) (by decide)

private def filterPattern (n : Nat) (t : State n) (k : Nat) (A : Colored k) : Option (State n) × Nat :=
  if budget n<k then (none,localFee n)
  else
    let (p,c):=LayoutMeter.run A (width n) k
    (if p.head?.isSome then some t else none,c+localFee n)

def retain (n : Nat) (t : State n) := SparseMeter.run t (filterPattern n t)

private theorem retain_spec (t : State n) : retain n t =
    ((referenceRetain n t).1,SparseMeter.charge t+(referenceRetain n t).2) := by
  rw [retain,SparseMeter.run_eq];rfl

theorem retain_val (t : State n) :
    (retain n t).1=if ElementaryCompare.allowed (budget n) (width n) t then some t else none := by
  rw [retain_spec,← referenceRetain_val]

private theorem cache_bound (s : State n) : Fits n 12030 (SparseMeter.charge s) :=
  (SparseMeter.charge_cost s).trans (polynomial n 12000 10)

private theorem retain_bound (t : State n) : Fits n 160000 (retain n t).2 := by
  rw [retain_spec]; exact widen ((cache_bound t).plus (referenceRetain_bound t)) (by decide)

private def evaluate (n : Nat) (fields : Bool) (k : Nat) (B : Colored k) (l : Nat) (A : Colored l) : Bool × Nat :=
  if budget n<k then (false,localFee n)
  else
    let (pool,p):=LayoutMeter.run B (width n) k
    match pool.head? with
    | none => (false,p+localFee n)
    | some xs =>
      if l≠k then (false,p+localFee n)
      else
        let C:=reindex B xs
        let measured:=BagMeter.compare C A
        (decide (k=l) && fields && measured.1,p+localFee n*(measured.2+1))

/-- Materialize both compact incidence structures before probing a key.
The finite-width filter rejects malformed layouts without consulting GI. -/
def comparison (x t : State n) : Bool × Nat :=
  let fields:=IncidenceMeter.scalar t x
  let out:=SparseMeter.run t fun k B => SparseMeter.run x (evaluate n fields.1 k B)
  (out.1,CombinedCost.scalarFee x t+out.2)

private theorem comparison_spec (x t : State n) :
    comparison x t = ((referenceComparison x t).1,
      CombinedCost.scalarFee x t+(SparseMeter.charge t+(SparseMeter.charge x+(referenceComparison x t).2))) := by
  simp only [comparison,SparseMeter.run_eq,evaluate,measured_bag,referenceComparison,compareOrder,IncidenceMeter.scalar]
  by_cases tooBig : budget n < orderSize t
  · simp only [ite_eq_left tooBig]
  · simp only [ite_eq_right tooBig]
    cases result : (LayoutMeter.run (pattern t) (width n) (orderSize t)).1.head? <;> rfl

theorem comparison_eq (x t : State n) (cert : ElementaryCompare.allowed (budget n) (width n) t=true) :
    (comparison x t).1=compareWith (width n) x t := by rw [comparison_spec,←referenceComparison_eq x t cert]

theorem comparison_bound (x t : State n) : Fits n 5100000 (comparison x t).2 := by
  have sc : Fits n 38 (CombinedCost.scalarFee x t) :=
    (Nat.min_le_right ..).trans (polynomial n 32 2)
  have setup : Fits n 12032 (CombinedCost.scalarFee x t+SparseMeter.charge t+SparseMeter.charge x) :=
    widen ((sc.plus (cache_bound t)).plus (cache_bound x)) (by decide)
  rw [comparison_spec];dsimp only
  rw [←Nat.add_assoc,←Nat.add_assoc]
  exact widen (setup.plus (referenceComparison_bound x t)) (by decide)

/-- Filter the actual generated catalogue, charging every failed layout test. -/
def preprocess (ds : List Nat) :=
  let (raw,c) := GeneratorCost.preprocess ds
  let (ts,w) := collect (retain ds.length) raw
  (ts,c+w)

theorem preprocess_eq (ds : List Nat) : (preprocess ds).1=ElementaryRun.catalogue ds := by
  simp only [preprocess, collect_val, GeneratorCost.preprocess_eq, retain_val,
    ElementaryRun.catalogue]
  rw [←List.filterMap_eq_filter]
  rfl

private theorem one (n : Nat) : Fits n 0 1 := by simp [Fits]

private theorem two (n : Nat) : Fits n 1 2 := by
  change 2≤2^(1*(n.sqrt+1));rw [Nat.one_mul]
  exact Nat.one_lt_two_pow (by omega)

theorem preprocess_cost (ds : List Nat) (mass : ds.sum≤6*ds.length) :
    Fits ds.length 430000 (preprocess ds).2 := by
  let n:=ds.length
  let bound:=2^(160000*(n.sqrt+1))
  let ts:=(GeneratorCost.preprocess ds).1
  have t : Fits n 268428 ts.length := by
    simp only [ts,GeneratorCost.preprocess_eq]; exact PreprocessCost.catalogue_single_exponential ds mass
  have b : Fits n 160000 bound := Nat.le_refl _
  have c:=collect_cost (retain n) ts bound (fun a _ => retain_bound a)
  have h:=((t.prod (b.plus (one n))).plus (one n))
  have g : Fits n 271249 (GeneratorCost.preprocess ds).2 := GeneratorCost.preprocess_cost ds mass
  exact widen (g.plus (c.trans h)) (by decide)

private theorem layers_eq (ds : List Nat) (bound k : Nat) :
    layer (fun x t => (comparison x t).1) (ElementaryRun.catalogue ds) bound (ds : Multiset Nat) k =
    layer (compareWith (width ds.length)) (ElementaryRun.catalogue ds) bound (ds : Multiset Nat) k := by
  have heads (cs : List (Entry ds.length)) :
      index (fun x t => (comparison x t).1) (ElementaryRun.catalogue ds) cs =
      index (compareWith (width ds.length)) (ElementaryRun.catalogue ds) cs := by
    apply List.filterMap_congr
    intro t ht
    congr 1
    funext e
    exact comparison_eq _ _ (List.mem_filter.mp ht).2
  induction k with
  | zero => exact heads _
  | succ k ih => simp only [WitnessTable.layer,ih,heads]

/-- Compose the filtered table construction, all first-match comparisons,
triangle proposals and the final labelled graph reconstruction. -/
def search (x : Nat) (ds : List Nat) (f : Nat) :=
  let d:=x::ds
  let ts:=preprocess d
  let reached:=WitnessCost.run comparison (fun e a => (StepCost.charged (f+1) e a).2)
    ts.1 (f+1) (d : Multiset Nat) (f+1)
  let out:=OutputCost.finish d (f+1) reached.1
  (out.1,ts.2+reached.2+out.2)

theorem search_eq (x : Nat) (ds : List Nat) (f : Nat) :
    (search x ds f).1=realize (compareWith (width (x::ds).length))
      (ElementaryRun.catalogue (x::ds)) (x::ds) f := by
  simp only [search,preprocess_eq,WitnessCost.output,layers_eq,OutputCost.finish_eq]

theorem search_cost (x : Nat) (ds : List Nat) (f : Nat) (steps : f+1≤2*(x::ds).length)
    (mass : (x::ds).sum≤6*(x::ds).length) :
    Fits (x::ds).length 6000000 (search x ds f).2 := by
  let d:=x::ds
  let n:=d.length
  let T:=(preprocess d).1
  let u:=2^(5100000*(n.sqrt+1))
  have work:=StepCost.measured_work comparison T (f+1) (d : Multiset Nat) (f+1) u
    (show (d : Multiset Nat).card≤n by simp [n]) (fun a b => comparison_bound a b)
  have steps' : Fits n 5 (f+1+1) :=
    (show f+1+1≤2*(n+2)^1 by change f+1≤2*n at steps;simp only [pow_one];omega).trans (polynomial n 2 1)
  have tc : Fits n 268428 T.length := by
    dsimp only [T]; rw [preprocess_eq]
    exact (ElementaryRun.catalogue_length d).trans (PreprocessCost.catalogue_single_exponential d mass)
  have nodes := (tc.plus (two n)).pow 2
  have parts : Fits n 17 (n^3*8) :=
    (show n^3*8≤8*(n+2)^3 by nlinarith [Nat.zero_le n, Nat.zero_le (n^2)]).trans (polynomial n 8 3)
  have transition : Fits n 3012 (3000*(n+1)^4) :=
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : n+1≤n+2) _)).trans (polynomial n 3000 4)
  have cap : Fits n 5100000 (max u (3000*(n+1)^4)) := max_le (Nat.le_refl _) (widen transition (by decide))
  have rem := work.trans (steps'.prod (((nodes.prod (parts.plus (two n))).prod (cap.plus (constant n 8)))))
  have scan := OutputCost.realize_cost (fun a b => (comparison a b).1) T d f rfl steps
  have out : Fits n (268429+22*24) ((T.length+1)*(n+32)^24) :=
    (tc.plus (one n)).prod ((show Fits n 22 (n+32) from
       (show n+32≤ n+BoundaryState.cutoff n+32 by omega).trans (DecodeMeter.factors n)).pow 24)
  have inp:=preprocess_cost d mass
  simp only [search,WitnessCost.output]
  exact widen ((inp.plus rem).plus (scan.trans out)) (by decide)

theorem large_reference (x : Nat) (ds : List Nat) (big : 4≤(x::ds).length) (mass : (x::ds).sum≤6*(x::ds).length) :
    (search x ds (2*(x::ds).length-5)).1=ElementaryRun.find (x::ds) := by
  rw [search_eq];simp only [ElementaryRun.find,List.length_cons] at *
  rw [ite_eq_right (Nat.not_lt.mpr mass),ite_eq_right (Nat.not_lt.mpr big)]

theorem search_iff (sep : SeparatorInput.WeightedPlanarSeparator) (x : Nat) (ds : List Nat)
    (big : 4≤(x::ds).length) (mass : (x::ds).sum≤6*(x::ds).length) :
    ((search x ds (2*(x::ds).length-5)).1).isSome ↔ SparseBoundary.Planaric (x::ds) := by
  rw [large_reference x ds big mass,ElementaryRun.find_iff sep]

#print axioms search_cost
#print axioms search_iff
end Recognition.ElementaryCost
