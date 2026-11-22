import PreprocessCost
import WitnessTable
import VerifierCost

/-! A worst-case list-scan tariff for preprocessing a candidate, including
malformed candidates. The metered implementation freezes the whole state:
each of the four-index block entries is evaluated once. A pass billed for
every position also pays for paths terminated early by an option or a guard.
The unit of a cell tariff is one bounded word operation; the final factor
charges schoolbook bit operations at the stated word width. -/
namespace Recognition.DecodeMeter
open PlanarDegrees.Frontier Recognition.BoundaryState Recognition.PreprocessCost
open Recognition.MarkedPlane Recognition.OverlayRead Recognition.OrbitTable

/-- A positive polynomial written in terms of the name capacity, the decoded
dart count, and the input length. Kept symbolic to check the common degree
bound of the nested scans. -/
inductive Price where
  | names | darts | bits | lit (v : Nat)
  | add (a b : Price) | mul (a b : Price)
instance (n : Nat) : OfNat Price n := ⟨.lit n⟩
instance : Add Price := ⟨.add⟩
instance : Mul Price := ⟨.mul⟩

def Price.eval (n k b : Nat) : Price → Nat
  | .names => n | .darts => k | .bits => b | .lit v => v
  | .add x y => x.eval n k b+y.eval n k b
  | .mul x y => x.eval n k b*y.eval n k b

private def Price.weight : Price → Nat
  | .names | .darts | .bits | .lit _ => 1
  | .add x y => max x.weight y.weight + 1
  | .mul x y => x.weight + y.weight

private def Price.scalar : Price → Nat
  | .names | .darts | .bits => 1 | .lit v => v
  | .add x y | .mul x y => max x.scalar y.scalar

private theorem evaluate (P : Price) (n k b z : Nat) (hn : n≤z) (hk : k≤z) (hb : b≤z)
    (big : 2≤z) (constants : P.scalar≤z) : P.eval n k b≤z^P.weight := by
  induction P with
  | names => simpa [Price.eval,Price.weight] using hn
  | darts => simpa [Price.eval,Price.weight] using hk
  | bits => simpa [Price.eval,Price.weight] using hb
  | lit v => simpa [Price.eval,Price.weight,Price.scalar] using constants
  | mul a c ia ic =>
    simp only [Price.scalar,sup_le_iff] at constants
    simpa only [Price.weight,Nat.pow_add,Price.eval] using Nat.mul_le_mul (ia (by omega)) (ic (by omega))
  | add a c ia ic =>
    simp only [Price.scalar,sup_le_iff] at constants
    let w := max a.weight c.weight
    have lo := (ia (by omega)).trans (Nat.pow_le_pow_right (by omega : 0<z) (show a.weight≤w from le_max_left ..))
    have hi := (ic (by omega)).trans (Nat.pow_le_pow_right (by omega : 0<z) (show c.weight≤w from le_max_right ..))
    change a.eval n k b + c.eval n k b ≤ z^(w+1)
    rw [Nat.pow_succ]; nlinarith

/-- Includes the two indexed-bit chord scans, unary header and bit fields. -/
def parser := 32*(Price.bits+1)*(Price.bits+1)
private def merge := 2*(Price.darts+1)+(Price.darts+1)*(Price.darts+4)
private def orbit (generators : Price) := (Price.darts+1)*2 + generators*merge + Price.darts+4
/-- Compute one original mate by a linear match lookup. The two original
band maps and the cyclic successor recover the old rotation/edge pair. -/
private def mate := 4*(Price.darts+2)
private def turn := 2*mate + 8
private def vertexKey := (Price.darts+1)*(turn+3) + orbit Price.darts
private def counter := (Price.darts+1)*(2*vertexKey+Price.darts+6)
private def edge := (Price.darts+1)*(4*vertexKey+2*mate+2*Price.darts+12)
private def incidence := 2*edge+Price.darts+8
private def lookupSide := (Price.darts+1)*incidence + 2*Price.darts+6
private def hop := 2*vertexKey+2*Price.darts+8+(Price.darts+1)*(2*edge+3*Price.darts+10)
/-- A hub query scans all ordered pairs, then applies at most k² unions. -/
private def hubKey := (Price.darts+1)*(Price.darts+1)*(hop+5) + orbit (Price.darts*Price.darts)
private def connectedPins := (Price.darts+1)*(Price.darts+1)*(2*hubKey+2*edge+2*Price.darts+12)
private def lookupBlock := (Price.darts+1)*(Price.darts+1)*(2*incidence+connectedPins+8)+4*Price.darts+8
private def names := (Price.darts+1)*(Price.darts+1)*(vertexKey+Price.darts+6)
private def entries := (Price.names+1)*(Price.names+1)
private def dense := names + 2*entries*(lookupSide+6) + entries*entries*(lookupBlock+8) +
  (Price.names+1)*(counter+Price.darts+6)+32
/-- Bit width also covers sums of up to k binary counters, as well as dart,
array and slot addresses. -/
private def width := Price.bits+Price.darts+Price.names+16
def whole := (parser+dense)*width*width

/-- The two orbit tariffs dominate the charged operations on the exact
materialized union lists, even for a malformed graph view. -/
theorem orbit_charge {k : Nat} (es : List (Fin k × Fin k)) :
    VerifierCost.unionWork (List.finRange k) es (tabulate (List.finRange k) id) =
      es.length*merge.eval n k b+1 := by
  rw [VerifierCost.union_exact _ _ _ (by simp [tabulate])]
  rw [List.length_finRange]
  rfl

/-- Charge the parser even on a rejected proposal. On acceptance all dense
slots are frozen before the state is returned. -/
def candidate (n : Nat) (p : Proposal) : Option (QuotientDP.State n) × Nat :=
  let src := p.1
  let rest := p.2.1
  let used := p.2.2.1
  let faces := p.2.2.2
  if src=[] then (some (WitnessTable.freeze (blank n rest used faces)),whole.eval n 0 src.length)
  else match MarkedPlane.decode src with
    | none => (none,(parser*width*width).eval n 0 src.length)
    | some V => ((fromView n V rest used faces).map WitnessTable.freeze,whole.eval n V.ribbon.length src.length)

theorem candidate_result (n : Nat) (p : Proposal) :
    (candidate n p).1 = BoundaryState.decode n p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  unfold candidate BoundaryState.decode
  dsimp only
  split
  · simp
  · split
    · simp_all
    · next V h => rw [h]; cases q : fromView n V p.2.1 p.2.2.1 p.2.2.2 <;> simp [q]

theorem candidate_cost (n : Nat) (p : Proposal) :
    (candidate n p).2 ≤ (n+p.1.length+32)^128 := by
  have calcWhole (k : Nat) (valid : k≤p.1.length) :
      whole.eval n k p.1.length ≤ (n+p.1.length+32)^128 := by
    apply (evaluate whole n k p.1.length (n+p.1.length+32) (by omega) (by omega) (by omega) (by omega)
      (le_trans (by decide : whole.scalar≤32) (by omega))).trans
    exact Nat.pow_le_pow_right (by omega) (by decide)
  unfold candidate
  dsimp only
  split
  · exact calcWhole 0 (by omega)
  · split
    · apply (evaluate (parser*width*width) n 0 p.1.length (n+p.1.length+32)
        (by omega) (by omega) (by omega) (by omega) (le_trans (by decide : (parser*width*width).scalar≤32) (by omega))).trans
      exact Nat.pow_le_pow_right (by omega) (by decide)
    · next V ok =>
      have lim := (decode_bounds ok).1
      exact calcWhole _ (by omega)

private theorem src_size {ds : List Nat} {p : Proposal} (m : p∈attempts ds) : p.1.length≤cutoff ds.length := by
  simp only [attempts,List.mem_flatMap,List.mem_map,words_spec] at m
  obtain ⟨bs,size,_,_,_,_,_,_,rfl⟩ := m
  exact size

/-- The metered generator returns the frozen table and the sum of all
record charges, with an additional pass over the proposal sequence. -/
def run (ds : List Nat) : List (QuotientDP.State ds.length) × Nat :=
  let visited := (attempts ds).map (candidate ds.length)
  (visited.filterMap Prod.fst,(visited.map Prod.snd).sum+visited.length+1)

theorem returns_catalogue (ds : List Nat) : (run ds).1=ShortBoundary.catalogue ds := by
  rw [←(exact_attempts ds).2]
  simp [run,List.filterMap_map,Function.comp_def,candidate_result]

theorem factors (n : Nat) :
    n+cutoff n+32 ≤ 2^(22*(n.sqrt+1)) := by
  let S := n.sqrt+1
  have hi : n<S*S := Nat.lt_succ_sqrt n
  have pos : 0<S := by simp [S]
  have p : S≤2^S := Nat.le_of_lt Nat.lt_two_pow_self
  have square : S*S≤2^(2*S) := by
    rw [Nat.two_mul,Nat.pow_add]
    exact Nat.mul_le_mul p p
  have grow : S≤2^(2*S) := p.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have cut : cutoff n≤268401*S := by
    have w : (220^2*n).sqrt<220*S := Nat.sqrt_lt.mpr (by nlinarith)
    unfold cutoff
    omega
  have init : n+cutoff n+32 ≤ 2^20*2^(2*S) := by
    have yes : 0<2^(2*S) := Nat.two_pow_pos _
    norm_num
    omega
  rw [← Nat.pow_add] at init
  exact init.trans (Nat.pow_le_pow_right (by decide) (by change 20+2*S≤22*S; omega))

/-- Preprocessing under the specified list-scan and bit tariffs, including
every rejected code and all four-index state entries. -/
theorem runtime (ds : List Nat) (mass : ds.sum≤6*ds.length) :
    (run ds).2 ≤ 2^(271248*(ds.length.sqrt+1)) := by
  let S := ds.length.sqrt+1
  have pos : 0<S := by simp [S]
  let visits := (attempts ds).map (candidate ds.length)
  have count : visits.length≤2^(268428*S) := by
    simpa [visits,(exact_attempts ds).1] using probes_le ds mass
  have fee (u : Nat) (h : u∈visits.map Prod.snd) : u ≤ 2^(2816*S) := by
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
    have b := (Nat.add_le_add_right (Nat.add_le_add_left (src_size hp) ds.length) 32).trans (factors ds.length)
    have high := (candidate_cost ds.length p).trans (Nat.pow_le_pow_left b 128)
    rw [← Nat.pow_mul,show 22*(ds.length.sqrt+1)*128=2816*S by dsimp [S]; omega] at high
    exact high
  have sum := List.sum_le_length_nsmul (visits.map Prod.snd) _ fee
  simp only [List.length_map,smul_eq_mul] at sum
  have base : (visits.map Prod.snd).sum ≤ 2^(271244*S) := by
    have val := sum.trans (Nat.mul_le_mul_right _ count)
    rwa [← Nat.pow_add,show 268428*S+2816*S=271244*S by omega] at val
  have cnt := count.trans (Nat.pow_le_pow_right (by decide) (show 268428*S≤271244*S by omega))
  change (visits.map Prod.snd).sum+visits.length+1≤_
  have grow : 271244*S+2≤271248*S := by omega
  apply le_trans _ (Nat.pow_le_pow_right (by decide) grow)
  rw [Nat.pow_add]
  have positive : 0<2^(271244*S) := Nat.two_pow_pos _
  omega

#print axioms runtime
#print axioms returns_catalogue
end Recognition.DecodeMeter

namespace Recognition.DecodeMeter
open Recognition.MarkedPlane

/-- A counter is assembled by summing entries in one vertex orbit. The
bound also holds on accepted strings whose decoded maps are invalid. -/
theorem counter_bits {bs : List Bool} {C : View} (ok : MarkedPlane.decode bs=some C)
    (i : Fin C.ribbon.length) : C.counter i < 2^(bs.length+C.ribbon.length+1) := by
  have fields := (PreprocessCost.decode_dimensions ok).2.2.2
  have bound (j : Fin C.ribbon.length) : C.values[j.val]?.getD 0≤2^bs.length := by
    cases h : C.values[j.val]? with
    | none => simp
    | some v =>
      have m : v∈C.values := List.mem_of_getElem? h
      exact Nat.le_of_lt (fields v (List.mem_append_right _ m))
  have term (j : Fin C.ribbon.length) : (if C.vertexKey j=C.vertexKey i then C.values[j.val]?.getD 0 else 0)≤2^bs.length := by
    split
    · exact bound _
    · exact Nat.zero_le _
  have sum : C.counter i≤C.ribbon.length*2^bs.length := by
    simpa only [View.counter,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using
      Finset.sum_le_sum (s := (Finset.univ : Finset (Fin C.ribbon.length))) (fun j _ => term j)
  have h := sum.trans (Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.lt_two_pow_self (n := C.ribbon.length))))
  rw [←Nat.pow_add,Nat.add_comm C.ribbon.length bs.length] at h
  rw [Nat.pow_succ]
  have positive := Nat.two_pow_pos (bs.length+C.ribbon.length)
  omega

#print axioms counter_bits
end Recognition.DecodeMeter
