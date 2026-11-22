import MainResult
import StepCost
import GeneratorCost

/-! The caller supplies a coloured directed graph-isomorphism routine and
its quasipolynomial word-operation bound. The induced state comparator,
the witness-carrying recurrence, the number of catalogue probes and the
absorption of every fixed polylogarithm into the square-root exponent are
made explicit here. -/
namespace Recognition.AlgorithmCost
open Recognition.QuotientDP Recognition.StateIncidence

/-- Uniform over all graph orders at most a fixed polynomial in n.
The double integer square root also gives a strict sub-square-root bound. -/
theorem log_power (n g p d : Nat) (hg : g≤(n+2)^p) :
    (g.log2+1)^d ≤ ((p+1)*(4*(d+1)))^d * (n.sqrt.sqrt+2) := by
  let t := (n+2).log2
  let b := 4*(d+1)
  let k := t / b
  have bp : 0<b := by dsimp [b]; omega
  have tmax : n+2 < 2^(t+1) := Nat.lt_log2_self
  have one : 1<2^(t+1) := Nat.one_lt_two_pow (by omega)
  have lg : g.log2+1 ≤ (p+1)*(t+1) := by
    by_cases gz : g=0
    · subst g; exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    have less : g<2^((p+1)*(t+1)) := by
      rw [Nat.mul_comm, Nat.pow_mul,Nat.pow_succ]
      have z := Nat.pow_le_pow_left tmax.le p
      exact hg.trans_lt (z.trans_lt ((Nat.lt_mul_iff_one_lt_right (by positivity)).mpr one))
    exact (Nat.log2_lt gz).mpr less
  have residual := Nat.mod_lt t bp
  have division := Nat.mod_add_div t b
  have chunk : t+1≤b*(k+1) := by dsimp [k]; rw [Nat.mul_add]; omega
  have small : k+1≤2^k := Nat.lt_two_pow_self
  have power : (g.log2+1)^d ≤ ((p+1)*b)^d*2^(k*d) := by
    rw [Nat.pow_mul,←Nat.mul_pow]
    apply Nat.pow_le_pow_left _ _
    calc
      _ ≤ (p+1)*(b*(k+1)) := lg.trans (Nat.mul_le_mul_left _ chunk)
      _ ≤ (p+1)*(b*(2^k)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ small)
      _ = _ := (Nat.mul_assoc ..).symm
  have four : (2^(k*d))^4 ≤ n+2 := by
    rw [←Nat.pow_mul]
    apply (Nat.pow_le_pow_right (n:=2) (by decide) ?_).trans ((Nat.le_log2 (by omega : n+2≠0)).mp (by rfl))
    change k*d*4≤t
    calc
      _ ≤ b*k := by dsimp [b]; nlinarith
      _ ≤ t := by simpa [k,Nat.mul_comm] using Nat.div_mul_le_self t b
  have sq := Nat.lt_succ_sqrt n
  have qq := Nat.lt_succ_sqrt n.sqrt
  change n<(n.sqrt+1)*(n.sqrt+1) at sq
  change n.sqrt<(n.sqrt.sqrt+1)*(n.sqrt.sqrt+1) at qq
  have upper : n+2≤(n.sqrt.sqrt+2)^4 := by
    have first : n<(n.sqrt.sqrt+1)^4 := by
      have both := Nat.mul_self_le_mul_self (by omega : n.sqrt+1≤(n.sqrt.sqrt+1)*(n.sqrt.sqrt+1))
      nlinarith
    nlinarith [Nat.zero_le n.sqrt.sqrt,Nat.zero_le (n.sqrt.sqrt^2),Nat.zero_le (n.sqrt.sqrt^3)]
  exact power.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_iff_left (by decide : 4≠0)).mp (four.trans upper)))

/-- For any fixed denominator, the fourth-root bound is eventually at most
that fraction of the square root. -/
theorem negligible (C denominator : Nat) :
    ∃ N : Nat, ∀ n≥N, denominator*C*(n.sqrt.sqrt+2)≤n.sqrt := by
  let a := denominator*C+2
  refine ⟨(2*a)^4,?_⟩
  intro n h
  have qa : 2*a≤n.sqrt.sqrt := Nat.le_sqrt.mpr (Nat.le_sqrt.mpr (by nlinarith))
  have hq := Nat.sqrt_le n.sqrt
  dsimp [a] at qa
  nlinarith [Nat.mul_le_mul_right n.sqrt.sqrt qa]

theorem names_size (s : State n) : (names s).length≤n+n^2 := by
  have lhs := List.length_filter_le (hasVertex s) (List.finRange n)
  let es := (List.finRange n).flatMap (fun x => (List.finRange n).map (x,·))
  have len : es.length=n^2 := by simp [es,List.length_flatMap,pow_two]
  have rhs := (List.length_filter_le (hasSide s) es).trans_eq len
  simpa only [names,List.length_append,List.length_map,List.length_finRange,es] using Nat.add_le_add lhs rhs

/-- Exact semantic and cost contracts for the external GI algorithm.
The admissible cost includes the two graph orders, with fixed coefficient
and fixed power in the logarithmic exponent. -/
structure GI where
  run : ∀ {a b : Nat}, StateIso.Colored a → StateIso.Colored b → Bool × Nat
  correct : ∀ {a b} (A : StateIso.Colored a) (B : StateIso.Colored b), (run A B).1=true ↔ StateIso.Iso A B
  coeff : Nat
  power : Nat
  time : ∀ {a b} (A : StateIso.Colored a) (B : StateIso.Colored b),
    (run A B).2≤2^(coeff*((a+b+2).log2+1)^power)

def detector (I : GI) : MainResult.Comparator := compareUsing (fun A B => (I.run A B).1)

theorem detector_exact (I : GI) (a b : State n) : detector I a b=true ↔ Same a b :=
  compareUsing_iff _ I.correct a b

theorem output_iff (I : GI) (sep : SeparatorInput.WeightedPlanarSeparator) (ds : List Nat) :
    (MainResult.findWith (detector I) ds).isSome ↔ SparseBoundary.Planaric ds :=
  MainResult.findWith_iff _ (detector_exact I) sep ds

def logFactor (I : GI) := I.coeff*((3+1)*(4*(I.power+1)))^I.power

theorem gi_cost (I : GI) (s t : State n) :
    (I.run (graph s) (graph t)).2 ≤ 2^(logFactor I * (n.sqrt.sqrt+2)) := by
  have input : (names s).length + (names t).length+2≤(n+2)^3 := by
    nlinarith [names_size s,names_size t,Nat.zero_le (n^3)]
  have val := (I.time (graph s) (graph t))
  apply val.trans
  apply Nat.pow_le_pow_right (by decide)
  simpa only [logFactor,Nat.mul_assoc] using Nat.mul_le_mul_left I.coeff (log_power n _ 3 I.power input)

/-- The scalar and graph preparation charges are kept explicit; callers may
materialize the incidence tables before handing them to the GI routine. -/
def compareMeter (I : GI) (prepare : State n → State n → Nat) (s t : State n) : Bool × Nat :=
  let v := I.run (graph s) (graph t)
  (decide (s.remaining=t.remaining ∧ s.used=t.used ∧ s.faces=t.faces) && v.1,prepare s t+v.2)

@[simp] theorem compareMeter_val (I : GI) (prepare : State n → State n → Nat) (s t : State n) :
    (compareMeter I prepare s t).1=detector I s t := rfl

/-- An integer bound by a single exponential of the square root. -/
def Fits (n c x : Nat) := x≤2^(c*(n.sqrt+1))

private theorem unit (n) : Fits n 1 2 := by
  change 2≤2^(1*(n.sqrt+1)); rw [Nat.one_mul]; exact Nat.one_lt_two_pow (by omega)

theorem Fits.prod {n a b x y} (hx : Fits n a x) (hy : Fits n b y) : Fits n (a+b) (x*y) := by
  unfold Fits at *; rw [Nat.add_mul,Nat.pow_add]; exact Nat.mul_le_mul hx hy

theorem Fits.plus {n a b x y} (hx : Fits n a x) (hy : Fits n b y) : Fits n (max a b+1) (x+y) := by
  have base (i) (le : i≤max a b) : 2^(i*(n.sqrt+1))≤2^(max a b*(n.sqrt+1)) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ le)
  have h := (base a (Nat.le_max_left ..)); have k := base b (Nat.le_max_right ..)
  have h₁ := (show x≤_ from hx).trans h; have h₂ := (show y≤_ from hy).trans k
  have f : Fits n (max a b+1) (2^(max a b*(n.sqrt+1))*2) := Fits.prod (show Fits n (max a b) _ from Nat.le_refl _) (unit n)
  exact (show x+y≤2^(max a b*(n.sqrt+1))*2 by omega).trans f

theorem Fits.pow {n a x} (e : Nat) (h : Fits n a x) : Fits n (a*e) (x^e) := by
  unfold Fits at *; rw [show a*e*(n.sqrt+1)=(a*(n.sqrt+1))*e by ring,Nat.pow_mul]
  exact Nat.pow_le_pow_left h _

theorem constant (n c : Nat) : Fits n c c := by
  apply (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_right (by decide) ?_)
  exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

theorem order (n : Nat) : Fits n 3 (n+2) := by
  have sq := Nat.lt_succ_sqrt n
  have pow : n.sqrt+1 ≤ 2^(n.sqrt+1) := Nat.le_of_lt Nat.lt_two_pow_self
  have h : Fits n 2 (n+1) := by
    change n+1≤2^(2*(n.sqrt+1))
    rw [Nat.two_mul,Nat.pow_add]
    exact (show n+1≤(n.sqrt+1)*(n.sqrt+1) from sq).trans (Nat.mul_le_mul pow pow)
  have k := Fits.plus h (show Fits n 0 1 by simp [Fits])
  simpa [Nat.max_def] using k

theorem polynomial (n k d : Nat) : Fits n (k+3*d) (k*(n+2)^d) :=
  (constant n k).prod ((order n).pow d)

private theorem gi_fits (I : GI) (s t : State n) : Fits n (2*logFactor I) (I.run (graph s) (graph t)).2 := by
  apply (gi_cost ..).trans (Nat.pow_le_pow_right (by decide) ?_)
  have zero := Nat.sqrt_le_self n.sqrt
  nlinarith [Nat.mul_le_mul_left (logFactor I) zero]

/-- A quasipolynomial coloured-GI cost, including a polynomial preprocessing
charge on each comparison, is subexponential in the original input order. -/
theorem compare_fits (I : GI) {n} (prepare : State n → State n → Nat) (K D : Nat)
    (charge : ∀ s t, prepare s t≤K*(n+2)^D) (s t : State n) :
    Fits n (max (K+3*D) (2*logFactor I)+1) (compareMeter I prepare s t).2 :=
  Fits.plus ((charge s t).trans (polynomial n K D)) (gi_fits I s t)

/-- The sum of actual catalogue-construction and full witness-table charges,
including all rejected states and triangle proposals. The constants depend
only on the supplied fixed GI and preparation exponents. -/
theorem search_cost (I : GI) (K D : Nat) :
    ∃ C : Nat, ∀ ds : List Nat, ∀ prepare : State ds.length → State ds.length → Nat,
    (∀ s t, prepare s t≤K*(ds.length+2)^D) → ds.sum≤6*ds.length →
    ∀ bound k, k≤2*ds.length →
      Fits ds.length C ((GeneratorCost.preprocess ds).2+
        (WitnessCost.run (compareMeter I prepare) (fun e a => (StepCost.charged bound e a).2)
          (GeneratorCost.preprocess ds).1 bound (ds : Multiset Nat) k).2) := by
  let A := max (K+3*D) (2*logFactor I)+1
  let P := max A (3000+3*4)
  refine ⟨max 271249 ((2+3) + ((max 268428 1+1)*2 + (max (8+3*3) 1+1) + (max P 8+1)))+1,?_⟩
  intro ds prep fee mass bound k steps
  let n := ds.length
  let T := (GeneratorCost.preprocess ds).1
  let u := 2^(A*(n.sqrt+1))
  have compares (s t : State n) : (compareMeter I prep s t).2≤u := compare_fits I prep K D fee s t
  have work := StepCost.measured_work (compareMeter I prep) T bound (ds : Multiset Nat) k u
    (show (ds : Multiset Nat).card≤n by simp [n]) compares
  have steps' : Fits n (2+3) (k+1) :=
    (show k+1≤2*(n+2)^1 by simp only [n,pow_one]; omega).trans (polynomial n 2 1)
  have tc : Fits n 268428 T.length := by
    dsimp [T]; rw [GeneratorCost.preprocess_eq]; exact PreprocessCost.catalogue_single_exponential ds mass
  have nodes := (tc.plus (unit n)).pow 2
  have parts : Fits n (8+3*3) (n^3*8) :=
    (show n^3*8≤8*(n+2)^3 by nlinarith [Nat.zero_le n, Nat.zero_le (n^2)]).trans (polynomial n 8 3)
  have transition : Fits n (3000+3*4) (3000*(n+1)^4) := (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : n+1≤n+2) _)).trans (polynomial n 3000 4)
  have maxCost : Fits n P (max u (3000*(n+1)^4)) := by
    apply max_le
    · apply Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_max_left ..))
    · apply transition.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.le_max_right ..)))
  exact Fits.plus (GeneratorCost.preprocess_cost ds mass)
    (work.trans (steps'.prod (((nodes.prod (parts.plus (unit n))).prod (maxCost.plus (constant n 8))))))

#print axioms output_iff
#print axioms search_cost
end Recognition.AlgorithmCost
