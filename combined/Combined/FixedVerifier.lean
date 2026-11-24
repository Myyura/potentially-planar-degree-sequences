import Combined.Budget
import RawVerifierResult
import UnaryHardness

/-! Positive certificates for the budget languages on unary fields and on
binary tagged degree fields. The binary parser checks degrees against the
order *after* adding the twos. A raw bit certificate supplies the packed
simple graph, forward rotation and inverse rotation. -/
namespace Combined.FixedVerifier
open Recognition SparseBoundary

/-- Unary degree input for the strong reduction. -/
def Language (budget : Nat → Nat) (input : List Bool) : Prop :=
  ∃ h, Wire.fields input=some h ∧ Budget.Feasible h 0 (budget h.length)

def BinaryLanguage (budget : Nat → Nat) (input : List Bool) : Prop :=
  ∃ h, Wire.readDegrees input=some h ∧ Budget.Feasible h 0 (budget h.length)

inductive Rule where
 | fixed (r : Nat)
 | linear

/-- `linear` uses the promised threshold on a multiple of 29 and extends
the verifier to all other orders by natural division. -/
def Rule.budget : Rule → Nat → Nat
 | .fixed r,_ => r
 | .linear,n => n/29-1

def Rule.constant : Rule → Nat
 | .fixed r => r
 | .linear => 0

theorem Rule.bound (q : Rule) (n : Nat) : q.budget n≤n+q.constant := by
  cases q with
  | fixed r => simp [Rule.budget,Rule.constant]
  | linear => simp [Rule.budget,Rule.constant]; omega

inductive Encoding where | unary | binary

def accepts (e : Encoding) (q : Rule) (input : List Bool) : Prop :=
  match e with | .unary => Language q.budget input | .binary => BinaryLanguage q.budget input

def parsed (e : Encoding) (q : Rule) (s : List Bool) : Option (List Nat) × Nat :=
  match e with
  | .unary => UnaryHardness.readMeter s
  | .binary =>
    let tags := WireSearch.countTags s
    let row := WireSearch.scan (tags.1+q.budget tags.1) s
    (row.1,tags.2+row.2+tags.1+4)

private theorem unary_arity {s : List Bool} {d : List Nat} (h : Wire.fields s=some d) : d.length≤s.length := by
  induction s generalizing d with
  | nil => simp [Wire.fields] at h; subst d; simp
  | cons b bs ih =>
    cases hr : Wire.fields bs with
    | none => cases b <;> simp [Wire.fields,hr] at h
    | some v =>
      have small := ih hr
      cases b <;> cases v <;> simp [Wire.fields,hr] at h <;> subst d <;> simp at * <;> omega

private theorem parsed_length {s : List Bool} {h : List Nat} (e : Encoding) (q : Rule)
    (ok : (parsed e q s).1=some h) : h.length≤s.length := by
  cases e with
  | unary => exact unary_arity (((UnaryHardness.readMeter_spec s).1.symm.trans ok))
  | binary =>
    have raw := ((WireSearch.reads _ s h).mp ok).1
    exact (WireSearch.arity_eq s raw) ▸ (WireSearch.count_tags s).2.2

private theorem parser_work (e : Encoding) (q : Rule) (s : List Bool) : (parsed e q s).2≤7*s.length+6 := by
  cases e with
  | unary => simp only [parsed,(UnaryHardness.readMeter_spec s).2]; omega
  | binary =>
    have t := WireSearch.count_tags s
    have w := WireSearch.scan_charge ((WireSearch.countTags s).1+q.budget (WireSearch.countTags s).1) s
    dsimp only [parsed]; omega

def row (q : Rule) (h : List Nat) := List.replicate (q.budget h.length) 2++h

private theorem parser_exact (e : Encoding) (q : Rule) (s : List Bool) :
    accepts e q s ↔ ∃ h, (parsed e q s).1=some h ∧ Planaric (row q h) := by
  cases e with
  | unary => simp [accepts,Language,parsed,(UnaryHardness.readMeter_spec s).1,Budget.Feasible,row]
  | binary =>
    simp only [accepts,BinaryLanguage,Budget.Feasible,List.replicate_zero,List.append_nil]
    constructor
    · rintro ⟨h,raw,plan⟩
      refine ⟨h,(WireSearch.reads _ s h).mpr ⟨raw,?_⟩,plan⟩
      intro x hx
      have good := WireSearch.degrees_fit plan x (List.mem_append_right _ hx)
      rw [(WireSearch.count_tags s).1,WireSearch.arity_eq s raw]
      simpa [Nat.add_comm] using good
    · rintro ⟨h,sc,plan⟩; exact ⟨h,((WireSearch.reads _ s h).mp sc).1,plan⟩

/-- Costed verifier. The short preprocessing term allows a degree-list length
scan, computation of the fixed or linear budget, and materializing the two-prefix. -/
def run (e : Encoding) (q : Rule) (s w : List Bool) : ComplexityCost.Meter Bool :=
  let read := parsed e q s
  match read.1 with
  | none => ⟨false,read.2+1⟩
  | some h =>
    let checked := RawVerifierResult.run (row q h) w
    ⟨checked.value,read.2+2*h.length+3*q.budget h.length+checked.work+5⟩

/-- Exact polynomial bound on the number of bits in an accepting certificate. -/
theorem certificate (e : Encoding) (q : Rule) (s : List Bool) :
    accepts e q s ↔ ∃ w : List Bool, w.length≤5*(2*s.length+q.constant+1)^3 ∧ (run e q s w).value=true := by
  rw [parser_exact]
  cases result : (parsed e q s).1 with
  | none => simp [run,result]
  | some h =>
    simp only [Option.some.injEq,exists_eq_left']
    have small := parsed_length e q result
    have k := q.bound h.length
    have size : (row q h).length+1≤2*s.length+q.constant+1 := by simp [row]; omega
    constructor
    · intro plan
      obtain ⟨w,len,ok⟩ := (RawWire.bounded_certificate _).mp plan
      exact ⟨w,len.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left size _)),by simpa [run,result,RawVerifierResult.run_value] using ok⟩
    · rintro ⟨w,_,ok⟩
      exact (RawWire.verify_iff _).mp ⟨w,by simpa [run,result,RawVerifierResult.run_value] using ok⟩

/-- Includes all malformed inputs and all overlength certificates. -/
theorem work (e : Encoding) (q : Rule) (s w : List Bool) :
    (run e q s w).work≤w.length+20*(s.length+q.constant+2)+61000*(2*s.length+q.constant+4)^8 := by
  have parse := parser_work e q s
  cases result : (parsed e q s).1 with
  | none => simp only [run,result]; omega
  | some h =>
    have sz := parsed_length e q result; have k := q.bound h.length
    have actual := RawVerifierResult.run_work (row q h) w
    have size : (row q h).length≤2*s.length+q.constant := by simp [row]; omega
    have power := Nat.pow_le_pow_left (Nat.add_le_add_right size 4) 8
    simp only [run,result]; omega

/-- Both encodings have a polynomially bounded witness and a polynomial-time
positive verifier; the additive `w.length` pays for arbitrary rejected witnesses. -/
theorem polynomial_verifier (e : Encoding) (q : Rule) :
    ∃ P Q : Polynomial Nat,
      (∀ s, accepts e q s ↔ ∃ w : List Bool, w.length≤P.eval s.length ∧ (run e q s w).value=true) ∧
      ∀ s w, (run e q s w).work≤w.length+Q.eval s.length := by
  let z := (Polynomial.X : Polynomial Nat)
  let c := Polynomial.C q.constant
  refine ⟨5*(2*z+c+1)^3, Polynomial.C 20*(z+c+2)+Polynomial.C 61000*(2*z+c+4)^8,?_,?_⟩
  · intro s; simpa [z,c] using certificate e q s
  · intro s w; simpa [z,c,Nat.add_assoc] using work e q s w

end Combined.FixedVerifier
