import DecodeMeter

/-! Producing the domain of decoder calls. Both nested tree enumerators
share their recursive tail once, even when several different leading
symbols use it. The metered program constructs the histograms once and
shares each residual multiset and bit string across its proposal tuples. -/
namespace Recognition.GeneratorCost
open PlanarDegrees.Frontier PreprocessCost BoundaryState

def bitWords : Nat → List (List Bool) × Nat
  | 0 => ([[]],1)
  | k+1 =>
    let (xs,w) := bitWords k
    ([] :: (xs.map (false :: ·) ++ xs.map (true :: ·)), w+8*(xs.length+1))

theorem bitWords_eq (k) : (bitWords k).1=words k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [bitWords,words,ih]

theorem bitWords_cost (k) : (bitWords k).2≤8*(k+1)*(words k).length := by
  induction k with
  | zero => decide
  | succ k ih =>
    have pos : 0 < (words k).length := by
      have inL := (words_spec [] k).2 (by simp)
      exact List.length_pos_of_mem inL
    simp only [bitWords,bitWords_eq,words,List.length_cons,List.length_append,List.length_map]
    nlinarith

def vectors : List Nat → List (List Nat) × Nat
  | [] => ([[]],1)
  | m::ms =>
    let (tail,w) := vectors ms
    let xs := (List.range (m+1)).flatMap fun v => tail.map (v :: ·)
    (xs,w+8*((m+1)*(tail.length+1)))

theorem vectors_eq (ms) : (vectors ms).1=residuals ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [vectors,residuals,ih]

private theorem copies {A B} (xs : List A) (f : A → List B) (m : Nat) (len : ∀x, (f x).length=m) :
    (xs.flatMap f).length=xs.length*m := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih,len,Nat.add_mul,Nat.add_comm]

private theorem choices (m) (ms) : (residuals (m::ms)).length=(m+1)*(residuals ms).length := by
  rw [residuals]
  rw [copies _ _ (residuals ms).length (by simp),List.length_range]

private theorem choices_pos (ms) : 0<(residuals ms).length := by
  induction ms with
  | nil => decide
  | cons m ms ih => rw [choices]; positivity

theorem vectors_cost (ms) : (vectors ms).2≤16*(ms.length+1)*(residuals ms).length := by
  induction ms with
  | nil => decide
  | cons m ms ih =>
    have pos := choices_pos ms
    rw [choices]
    simp only [vectors,vectors_eq,List.length_cons]
    nlinarith [Nat.mul_le_mul_left (16*(ms.length+1)) (Nat.le_mul_of_pos_left (residuals ms).length (Nat.succ_pos m)),
      Nat.mul_le_mul_left (m+1) pos.le, Nat.mul_le_mul_left (m+1) (show 1≤(residuals ms).length by omega)]

private theorem counts_len (S : Multiset Nat) (i l : Nat) : (ResidualTable.counts S i l).length=l := by
  induction l generalizing i with
  | zero => rfl
  | succ l ih => simp [ResidualTable.counts,ih]

/-- Each histogram occurrence scan uses at most n input comparisons and
each output vector has T+1 multiplicity slots. Reconstructing its multiset
copies at most n entries per slot. -/
def histograms (ds : List Nat) : List (Multiset Nat) × Nat :=
  let (xs,w) := vectors (ResidualTable.counts (ds : Multiset Nat) 0 (ds.sum+1))
  (xs.map (ResidualTable.unpack 0),w+8*(ds.sum+2)*(ds.length+1)*(xs.length+1))

theorem histograms_eq (ds) : (histograms ds).1=ResidualTable.table ds := by
  simp [histograms,ResidualTable.table,vectors_eq]

theorem histograms_cost (ds) : (histograms ds).2 ≤
    32*(ds.sum+2)*(ds.length+1)*((ResidualTable.table ds).length+1) := by
  let ms := ResidualTable.counts (ds : Multiset Nat) 0 (ds.sum+1)
  have h := vectors_cost ms
  have len : ms.length=ds.sum+1 := counts_len .. 
  rw [len] at h
  change (vectors ms).2+8*(ds.sum+2)*(ds.length+1)*((vectors ms).1.length+1)≤_
  rw [vectors_eq]
  simp only [ResidualTable.table,List.length_map]
  change _ ≤ 32*(ds.sum+2)*(ds.length+1)*((residuals ms).length+1)
  nlinarith [Nat.mul_le_mul_left (16*(ds.sum+2)) (Nat.le_mul_of_pos_left (residuals ms).length (Nat.succ_pos ds.length))]

/-- Allocate the tuple list. Append copies in the three surrounding
flatMaps and each input-loop pass are all included in the tuple tariff. -/
def generate (ds : List Nat) : List Proposal × Nat :=
  let (bs,w) := bitWords (cutoff ds.length)
  let (rs,h) := histograms ds
  let xs := bs.flatMap fun b => rs.flatMap fun r =>
    (List.range (ds.length+1)).flatMap fun u =>
    (List.range (2*ds.length+1)).map fun f => (b,r,u,f)
  (xs,(w+h+16*(xs.length+1))*(ds.sum+ds.length+cutoff ds.length+32)^2)

theorem generate_eq (ds) : (generate ds).1=attempts ds := by
  simp [generate,attempts,bitWords_eq,histograms_eq]

private theorem dimensions (ds) :
    (words (cutoff ds.length)).length ≤ probes ds ∧ (ResidualTable.table ds).length ≤ probes ds := by
  let b := (words (cutoff ds.length)).length
  let r := (ResidualTable.table ds).length
  have hb : 0<b := List.length_pos_of_mem ((words_spec [] _).2 (by simp))
  have hr : 0<r := List.length_pos_of_mem ((ResidualTable.mem_table ds 0).2 (by simp))
  have v : 0<((ds.length+1)*(2*ds.length+1)) := by positivity
  change b ≤ b*(r*_) ∧ r ≤ b*(r*_)
  constructor
  · exact Nat.le_mul_of_pos_right b (Nat.mul_pos hr v)
  · exact (Nat.le_mul_of_pos_right r v).trans (Nat.le_mul_of_pos_left _ hb)

theorem generation_cost (ds : List Nat) (mass : ds.sum≤6*ds.length) :
    (generate ds).2 ≤ 2^(268556*(ds.length.sqrt+1)) := by
  let n := ds.length
  let S := n.sqrt+1
  have pos : 0<S := by simp [S]
  let z := ds.sum+n+cutoff n+32
  have zpos : 32≤z := by dsimp [z]; omega
  have budget := DecodeMeter.factors n
  have twoS : 8≤2^(3*S) := by
    exact (show 8=2^3 by decide).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have scale : z≤2^(25*S) := by
    have big : z ≤ 8*(n+cutoff n+32) := by dsimp [z,n]; omega
    apply big.trans (Nat.mul_le_mul twoS budget |>.trans ?_)
    rw [← Nat.pow_add]
    exact Nat.pow_le_pow_right (by decide) (by change 3*S+22*S≤25*S; omega)
  let P := probes ds+1
  have num : P≤2^(268429*S) := by
    have c := probes_le ds mass
    have p : 0<2^(268428*S) := Nat.two_pow_pos _
    have a : P≤2^(268428*S+1) := by dsimp [P,S,n] at *; rw [Nat.pow_succ]; omega
    exact a.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have dim := dimensions ds
  have w : (bitWords (cutoff n)).2 ≤ z^2*P := by
    apply (bitWords_cost _).trans
    rw [pow_two]
    exact Nat.mul_le_mul (Nat.mul_le_mul (by omega : 8≤z) (by dsimp [z]; omega)) (by dsimp [P,n]; omega)
  have h : (histograms ds).2≤z^3*P := by
    apply (histograms_cost ds).trans
    rw [pow_succ,pow_two]
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul zpos (by dsimp [z,n]; omega)) (by dsimp [z,n]; omega)) (by dsimp [P]; omega)
  have extra : 16*P≤z^3*P := by
    apply Nat.mul_le_mul_right
    exact (show 16≤32^3 by decide).trans (Nat.pow_le_pow_left zpos _)
  have w' := w.trans (Nat.mul_le_mul_right P (Nat.pow_le_pow_right (by omega) (by decide : 2≤3)))
  have total : (generate ds).2≤P*z^5*3 := by
    change ((bitWords (cutoff n)).2+(histograms ds).2+16*((generate ds).1.length+1))*z^2≤_
    rw [generate_eq,(exact_attempts ds).1]
    change (_+_+16*P)*z^2≤_
    have tr : (bitWords (cutoff n)).2+(histograms ds).2+16*P≤3*(z^3*P) := by omega
    apply (Nat.mul_le_mul_right _ tr).trans
    ring_nf
    rfl
  apply total.trans
  have v := Nat.mul_le_mul num (Nat.pow_le_pow_left scale 5)
  rw [← Nat.pow_mul,← Nat.pow_add,show 268429*S+25*S*5=268554*S by omega] at v
  have lo : 3≤2^(2*S) := (show 3≤2^2 by decide).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have last := Nat.mul_le_mul v lo
  rw [←Nat.pow_add,show 268554*S+2*S=268556*S by omega] at last
  exact last

/-- Complete preprocessing uses the produced tuple list and charges both its
construction and its consumption. -/
def preprocess (ds : List Nat) : List (QuotientDP.State ds.length) × Nat :=
  let (xs,g) := generate ds
  let visited := xs.map (DecodeMeter.candidate ds.length)
  (visited.filterMap Prod.fst,g+((visited.map Prod.snd).sum+visited.length+1))

theorem preprocess_eq (ds : List Nat) : (preprocess ds).1=ShortBoundary.catalogue ds := by
  simpa [preprocess,DecodeMeter.run,generate_eq] using DecodeMeter.returns_catalogue ds

theorem preprocess_cost (ds : List Nat) (mass : ds.sum≤6*ds.length) :
    (preprocess ds).2≤2^(271249*(ds.length.sqrt+1)) := by
  let S := ds.length.sqrt+1
  have pos : 0<S := by simp [S]
  have bound := generation_cost ds mass
  have g : (generate ds).2≤2^(271248*S) := bound.trans (Nat.pow_le_pow_right (by decide) (by change 268556*S≤271248*S; omega))
  have h := DecodeMeter.runtime ds mass
  simp only [preprocess,generate_eq]
  change (generate ds).2+(DecodeMeter.run ds).2≤_
  have c : (generate ds).2+(DecodeMeter.run ds).2 ≤ 2^(271248*S+1) := by
    rw [Nat.pow_succ]
    change (DecodeMeter.run ds).2≤2^(271248*S) at h
    omega
  exact c.trans (Nat.pow_le_pow_right (by decide) (by change 271248*S+1≤271249*S; omega))

#print axioms preprocess_eq
#print axioms preprocess_cost

end Recognition.GeneratorCost
