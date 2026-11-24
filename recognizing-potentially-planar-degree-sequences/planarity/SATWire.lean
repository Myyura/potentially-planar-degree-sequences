import SATReduction
import Mathlib.Tactic.GCongr

/-! Total bitstring reduction for CNF formulas. A zero word ends a clause.
Word 1 + 2v + p encodes variable v and Boolean polarity p. Words use the
same little-endian tagged binary encoding as the target degree list. -/
namespace Recognition.SATBridge
open Hardness.Cert SparseBoundary Reduction

private def word (l : Nat × Bool) := (2*l.1+l.2.toNat)+1
private def literal (v : Nat) : Nat × Bool := (v/2,decide (v%2=1))

def satCode (x : SatTy.denote) : List Bool :=
  Wire.degrees (x.flatMap fun c => c.map word ++ [0])

def readClauses : List Nat → Option SatTy.denote
  | [] => some []
  | 0 :: rest => (readClauses rest).map ([] :: ·)
  | (v+1) :: rest => do
    let c::cs ← readClauses rest | none
    return (literal v :: c)::cs

def readSAT (bs : List Bool) := (Wire.readDegrees bs).bind readClauses

private theorem read_clause (c : List (Nat × Bool)) (rest : List Nat) :
    readClauses (c.map word ++ 0 :: rest) = (readClauses rest).map (c :: ·) := by
  induction c with
  | nil => rfl
  | cons l cs ih =>
    obtain ⟨v,p⟩ := l
    simp only [List.map_cons,List.cons_append,word,readClauses,ih]
    cases ans : readClauses rest with
    | none => rfl
    | some form => cases p <;> simp [literal,show (2*v)/2 = v by omega,show (2*v+1)/2=v by omega]

theorem read_satCode (x : SatTy.denote) : readSAT (satCode x) = some x := by
  rw [readSAT,satCode,Wire.degrees_round_trip]
  change readClauses _ = _
  induction x with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatMap_cons,List.append_assoc,List.singleton_append,read_clause,ih]; rfl

def SATLanguage (bs : List Bool) := ∃ x, readSAT bs = some x ∧ Concrete.SAT x

def satWire (bs : List Bool) :=
  match readSAT bs with
  | none => Wire.degrees malformedOutput
  | some x => Wire.reduceBits (Wire.sourceCode (instanceOfSAT x))

/-- SAT and ordinary potentially planar degree sequences, on a common bit alphabet. -/
theorem sat_wire_iff (bs : List Bool) :
    Wire.degreeLanguage Planaric (satWire bs) ↔ SATLanguage bs := by
  cases h : readSAT bs with
  | none =>
    simp only [satWire,h,Wire.degreeLanguage,Wire.degrees_round_trip,Option.some.injEq,
      exists_eq_left',SATLanguage,reduceCtorEq,false_and,exists_const]
    simp [Promise.malformed_no]
  | some x =>
    simpa [satWire,h,SATLanguage] using
      (Wagner.planaric_bit_reduction (Wire.sourceCode (instanceOfSAT x))).trans (sat_iff_unary x).symm

private def wordSize (ws : List Nat) := (ws.map Nat.size).sum + ws.length

private theorem growing_word (v : Nat) (b : Bool) : (2*v+b.toNat).size ≤ v.size+1 := by
  apply Nat.size_le.mpr
  have := Nat.lt_size_self v
  rw [pow_succ]
  cases b <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

private theorem read_words_size (bs : List Bool) (ws : List Nat) (h : Wire.readDegrees bs = some ws) :
    wordSize ws ≤ bs.length := by
  induction bs using List.twoStepInduction generalizing ws with
  | nil => simp [Wire.readDegrees] at h; subst ws; decide
  | singleton b =>
    cases b <;> simp [Wire.readDegrees] at h
    subst ws; decide
  | cons_cons b v rest ih ihTail =>
    cases b with
    | false =>
      cases hr : Wire.readDegrees (v::rest) with
      | none => simp [Wire.readDegrees,hr] at h
      | some ys =>
        simp only [Wire.readDegrees,hr,Option.map_some,Option.some.injEq] at h
        subst ws
        have := ihTail v ys hr
        simp only [wordSize,List.map_cons,List.sum_cons,List.length_cons,Nat.size_zero] at *
        omega
    | true =>
      cases hr : Wire.readDegrees rest with
      | none => simp [Wire.readDegrees,hr] at h
      | some ys =>
        cases ys with
        | nil => simp [Wire.readDegrees,hr] at h
        | cons a t =>
          simp [Wire.readDegrees,hr] at h
          subst ws
          have := ih (a::t) hr
          have := growing_word a v
          simp only [wordSize,List.map_cons,List.sum_cons,List.length_cons] at *
          omega

private theorem parsed_clause_size (ws : List Nat) (x : SatTy.denote) (h : readClauses ws = some x) :
    SatTy.size x ≤ 4*wordSize ws+1 := by
  induction ws generalizing x with
  | nil => simp [readClauses] at h; subst x; decide
  | cons n ns ih =>
    cases ans : readClauses ns with
    | none => cases n <;> simp [readClauses,ans] at h
    | some ys =>
      have prior := ih ys ans
      cases n with
      | zero =>
        simp [readClauses,ans] at h; subst x
        simp only [Ty.size_list,List.map_cons,List.sum_cons,List.length_cons,List.map_nil,
          List.sum_nil,List.length_nil,Nat.size_zero,wordSize] at prior ⊢
        omega
      | succ v =>
        cases ys with
        | nil => simp [readClauses,ans] at h
        | cons c cs =>
          simp [readClauses,ans] at h; subst x
          have := Nat.size_le_size (show v/2 ≤ v+1 by omega)
          simp only [Ty.size_list,Ty.size_pair,Ty.size_nat,Ty.size_bool,List.map_cons,
            List.sum_cons,List.length_cons,literal,wordSize] at prior ⊢
          omega

theorem read_sat_size (bs : List Bool) {x : SatTy.denote} (h : readSAT bs = some x) :
    SatTy.size x ≤ 4*bs.length+1 := by
  cases hr : Wire.readDegrees bs with
  | none => simp [readSAT,hr] at h
  | some ws =>
    have hc : readClauses ws = some x := by simpa [readSAT,hr] using h
    have := read_words_size bs ws hr
    have := parsed_clause_size ws x hc
    omega

theorem wire_prefix_polynomial :
    ∃ C d, ∀ bs x, readSAT bs = some x →
      satToThree.code.cost x + ComplexityCost.unarySize (instanceOfSAT x)
      ≤ 11 + C*(4*bs.length+2)^d := by
  obtain ⟨C,d,bound⟩ := sat_prefix_polynomial
  refine ⟨C,d,fun bs x h => (bound x).trans ?_⟩
  have len := read_sat_size bs h
  exact Nat.add_le_add_left (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) d)) 11

/-- One polynomial controls the length of the actual emitted degree bitstring,
including the fixed rejection output for malformed CNF syntax. -/
theorem sat_output_polynomial : ∃ C d : Nat, ∀ bs : List Bool,
    (satWire bs).length ≤ 13*(3^57*(5*(12+C*(4*bs.length+2)^d)+6)^73+6) := by
  obtain ⟨C,d,prefixBound⟩ := wire_prefix_polynomial
  refine ⟨C,d,fun bs => ?_⟩
  cases ok : readSAT bs with
  | none =>
    simp only [satWire,ok]
    have fallback : (Wire.degrees malformedOutput).length ≤ 78 :=
      (Wire.degrees_length _).trans (by decide)
    omega
  | some x =>
    simp only [satWire,ok]
    apply (Wire.wire_length _).trans
    have h := prefixBound bs x ok
    rw [Wire.source_length]
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega

private theorem work_mono {u v : Nat} (h : u ≤ v) : ComplexityCost.workBound u ≤ ComplexityCost.workBound v := by
  let s (t : Nat) := 5*t+3
  let n (t : Nat) := 3^57*(s t)^73
  let l (t : Nat) := 13+7*t+t*(6+3*t)
  let w (t : Nat) := 100*(s t+t+1) +
    9*(6*s t+10+(s t+1)*(12*s t+12)+4*(s t+1)) + (57+36*s t)*l (n t)
  change w u ≤ w v
  dsimp only [w,l,n,s]
  gcongr

/-- Combined accounting for the SAT interpreter and the degree compiler on
a parsed input. The fixed expression workBound is polynomial in its argument. -/
theorem compiler_work_polynomial :
    ∃ C d, ∀ bs x, readSAT bs = some x →
      let P := 11 + C*(4*bs.length+2)^d
      satToThree.code.cost x + (ComplexityCost.compile (instanceOfSAT x)).work ≤
        P + ComplexityCost.workBound P := by
  obtain ⟨C,d,bound⟩ := wire_prefix_polynomial
  refine ⟨C,d,fun bs x read => ?_⟩
  have parts := bound bs x read
  have graph := ComplexityCost.compile_work (instanceOfSAT x)
  dsimp only
  exact Nat.add_le_add (by omega) (graph.trans (work_mono (by omega)))

end Recognition.SATBridge
