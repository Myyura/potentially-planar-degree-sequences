import CombinedCost

/-! A fast isomorphism routine can accept ordinary dense integer colours,
numbered below the sum of the two graph orders. A joint palette retains
equalities across the two sides, even when the parsed frontier contains
large counter labels. -/
namespace Recognition.RankColors
open StateIso

def palette (A : Colored n) (B : Colored m) := (List.ofFn A.color)++(List.ofFn B.color)

def ranked (A : Colored n) (p : List Nat) : Colored n :=
  let c := Vector.ofFn (fun i => p.idxOf (A.color i))
  ⟨fun i => c[i.val],A.edge⟩

private theorem rank_eq {p : List Nat} {x y : Nat} (hx : x∈p) (hy : y∈p) :
    p.idxOf x=p.idxOf y ↔ x=y := by
  constructor
  · intro h
    have lt := List.idxOf_lt_length_of_mem hx
    calc
      x = p[p.idxOf x] := (List.getElem_idxOf lt).symm
      _ = p[p.idxOf y]'(List.idxOf_lt_length_of_mem hy) := by simp only [h]
      _ = y := List.getElem_idxOf (List.idxOf_lt_length_of_mem hy)
  · rintro rfl; rfl

theorem iso_iff (A : Colored n) (B : Colored m) : Iso (ranked A (palette A B)) (ranked B (palette A B)) ↔ Iso A B := by
  have left (i) : A.color i∈palette A B := List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  have right (j) : B.color j∈palette A B := List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
  simp only [Iso,ranked,Vector.getElem_ofFn,Fin.eta,rank_eq (left _) (right _)]

theorem bounded (A : Colored n) (B : Colored m) :
    (∀i,(ranked A (palette A B)).color i<n+m) ∧ (∀j,(ranked B (palette A B)).color j<n+m) := by
  have l : (palette A B).length=n+m := by simp [palette]
  constructor
  · intro i
    have mem : A.color i∈palette A B := List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    simpa [ranked,l] using List.idxOf_lt_length_of_mem mem
  · intro j
    have mem : B.color j∈palette A B := List.mem_append_right _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
    simpa [ranked,l] using List.idxOf_lt_length_of_mem mem

/-- Only tests on bounded colours must satisfy the GI theorem. Charges for
palette construction and ranking are additional word-comparison charges. -/
structure BoundedGI where
  run : ∀ {n m : Nat}, Colored n → Colored m → Bool × Nat
  correct : ∀ {n m} (A : Colored n) (B : Colored m),
    (∀i,A.color i<n+m) → (∀j,B.color j<n+m) → ((run A B).1=true ↔ Iso A B)
  coeff : Nat
  power : Nat
  time : ∀ {n m} (A : Colored n) (B : Colored m),
    (∀i,A.color i<n+m) → (∀j,B.color j<n+m) → (run A B).2≤2^(coeff*((n+m+2).log2+1)^power)

def test (I : BoundedGI) (A : Colored n) (B : Colored m) : Bool × Nat :=
  let p := palette A B
  let g := I.run (ranked A p) (ranked B p)
  (g.1,g.2+8*(n+m+2)^2)

theorem tariff (d c u : Nat) :
    2^(c*(u.log2+1)^d) + 8*u^2 ≤ 2^((c+8)*(u.log2+1)^(d+1)) := by
  let t := u.log2+1
  have tpos : 0<t := Nat.succ_pos _
  have ppos : 0<t^d := pow_pos tpos _
  have tmax := Nat.lt_log2_self (n:=u)
  have p : 8*u^2 ≤ 2^(3+2*t) := by
    rw [Nat.pow_add,Nat.mul_comm 2 t,Nat.pow_mul]; exact Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left tmax.le 2)
  change 2^(c*t^d)+8*u^2 ≤ 2^((c+8)*t^(d+1))
  have e : c*t^d ≤ (c+7)*t^(d+1) := by rw [Nat.pow_succ]; nlinarith [Nat.mul_le_mul_left (c*t^d) (show 1≤t from tpos)]
  have g : 3+2*t ≤ (c+7)*t^(d+1) := by rw [Nat.pow_succ]; nlinarith [Nat.mul_le_mul_right t (show 1≤t^d from ppos),Nat.zero_le (c*t^d*t)]
  have first := Nat.pow_le_pow_right (n:=2) (by decide) e
  have second := p.trans (Nat.pow_le_pow_right (n:=2) (by decide) g)
  apply (Nat.add_le_add first second).trans
  rw [←Nat.mul_two,←Nat.pow_succ]
  apply Nat.pow_le_pow_right (by decide)
  have h := pow_pos tpos (d+1)
  nlinarith

def algorithm (I : BoundedGI) : AlgorithmCost.GI where
  run := test I
  correct A B := ((I.correct _ _ (bounded A B).1 (bounded A B).2).trans (iso_iff A B))
  coeff := I.coeff+8
  power := I.power+1
  time A B := (Nat.add_le_add_right (I.time _ _ (bounded A B).1 (bounded A B).2) _).trans
    (tariff _ _ _)

/-- Even a malformed-but-decodable catalogue key supplies finite binary
counters of length controlled by the bit-string cutoff. -/
theorem catalogue_counter (ds : List Nat) {t : QuotientDP.State ds.length}
    (hit : t∈ShortBoundary.catalogue ds) (x : Fin ds.length) :
    t.current x<2^(2*BoundaryState.cutoff ds.length+1) := by
  obtain ⟨bs,_,_,_,len,_,_,_,dec⟩ := BoundaryState.table_mem.mp hit
  unfold BoundaryState.decode at dec
  split at dec
  · obtain rfl := Option.some.inj dec
    exact Nat.two_pow_pos _
  · cases h : MarkedPlane.decode bs with
    | none => simp [h] at dec
    | some V =>
      simp only [h,Option.bind_some] at dec
      unfold BoundaryState.fromView at dec
      dsimp only at dec
      split at dec
      · contradiction
      obtain rfl := Option.some.inj dec
      change ((BoundaryState.activeReps V)[x.val]?.map V.counter).getD 0<_
      cases eq : (BoundaryState.activeReps V)[x.val]? with
      | none => exact Nat.two_pow_pos _
      | some i =>
        have dim := (PreprocessCost.decode_dimensions h).2.2.1
        exact (DecodeMeter.counter_bits h i).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

theorem history_counter {fs U} {s : QuotientDP.State n} (run : QuotientDP.FullRun bound target fs U s)
    (x : Fin n) : s.current x≤3*fs.length := by
  induction run with
  | init => rfl
  | @step past U s t prev a eligible ok ih =>
    unfold QuotientDP.fullAdvance at ok
    split at ok
    · obtain rfl := Option.some.inj ok
      have three : QuotientDP.tally (QuotientDP.contributing s a x)≤3 :=
        (List.length_filter_le ..).trans_eq List.length_finRange
      change s.current x+QuotientDP.tally _≤3*(a::past).length
      simp only [List.length_cons,Nat.mul_succ]; omega
    · contradiction

/-- Each natural comparison used during joint ranking can be expanded to
a number of bit comparisons polynomial in the host order. The polynomial
factor is itself absorbed by the same single-exponential time bound. -/
def comparisonWidth (n : Nat) := 2*BoundaryState.cutoff n+6*n+8

private theorem colorBound (s : QuotientDP.State n) (i : Fin (StateIncidence.names s).length)
    {b : Nat} (h : ∀ x,s.current x<2^b) : (StateIncidence.graph s).color i<2^(b+3) := by
  change StateIncidence.tint s _<_
  cases keyEq : (StateIncidence.names s).get i with
  | inl x => have g := h x; have p := Nat.two_pow_pos b; simp only [StateIncidence.tint,Nat.pow_add]; norm_num; omega
  | inr e => cases j : s.pending e <;> cases k : s.sealed e <;> simp [StateIncidence.tint,j,k,Nat.pow_add]; all_goals have p := Nat.two_pow_pos b; omega

theorem compared_labels (ds : List Nat) {t : QuotientDP.State ds.length}
    (key : t∈ShortBoundary.catalogue ds) {fs U} {s : QuotientDP.State ds.length}
    (run : QuotientDP.FullRun bound target fs U s) (steps : fs.length≤2*ds.length) :
    (∀i, (StateIncidence.graph t).color i<2^(comparisonWidth ds.length)) ∧
    (∀i, (StateIncidence.graph (QuotientDP.prune s)).color i<2^(comparisonWidth ds.length)) := by
  constructor
  · intro i
    apply (colorBound t i (catalogue_counter ds key)).trans_le
    exact Nat.pow_le_pow_right (by decide) (by dsimp [comparisonWidth]; omega)
  · have h (x) : (QuotientDP.prune s).current x<2^(6*ds.length+1) := by
      apply Nat.lt_of_le_of_lt _ (Nat.lt_two_pow_self (n:=6*ds.length+1))
      have a := history_counter run x
      dsimp [QuotientDP.prune]; split <;> omega
    intro i
    exact (colorBound _ i h).trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [comparisonWidth]; omega))

theorem bit_expansion {n C x : Nat} (charge : AlgorithmCost.Fits n C x) :
    AlgorithmCost.Fits n (C+(536820+3*1)) (x*comparisonWidth n) := by
  have bound : (220^2*n).sqrt≤220*(n+1) := by
    apply Nat.le_of_lt_succ
    apply Nat.sqrt_lt.mpr; nlinarith [Nat.zero_le (n^2)]
  have p : comparisonWidth n≤536820*(n+2)^1 := by
    simp only [comparisonWidth,BoundaryState.cutoff,pow_one]; omega
  exact charge.prod (p.trans (AlgorithmCost.polynomial n 536820 1))

/-- An accepting output, and the single-exponential running-time conclusion,
for one and the same supplied finite-colour routine. -/
theorem paper_route (I : BoundedGI) (sep : SeparatorInput.WeightedPlanarSeparator) :
    (∀ ds, (MainResult.findWith (AlgorithmCost.detector (algorithm I)) ds).isSome ↔ SparseBoundary.Planaric ds) ∧
    ∃ C : Nat, ∀ x ds f, f+1≤2*(x::ds : List Nat).length → (x::ds).sum≤6*(x::ds).length →
      AlgorithmCost.Fits (x::ds).length C (CombinedCost.search (algorithm I) x ds f).2 :=
  ⟨AlgorithmCost.output_iff (algorithm I) sep,CombinedCost.search_cost (algorithm I)⟩

#print axioms paper_route
end Recognition.RankColors
