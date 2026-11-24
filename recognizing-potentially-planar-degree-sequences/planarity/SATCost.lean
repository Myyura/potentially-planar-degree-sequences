import SATWire
import RawWire

/-! The all-bit-string SAT reduction with parsing, the certified prefix
interpreter, unary-target conversion, the degree compiler and actual output
writing included in the same charge. -/
namespace Recognition.SATCost
open Hardness.Cert SATBridge SparseBoundary Reduction

/-- Charge each parsed tagged digit for the available input-bit width,
covering the shift and addition even on malformed suffixes. -/
def words : List Bool → Option (List Nat) × Nat
  | [] => (some [],1)
  | false::bs =>
    let p := words bs
    (p.1.map (0::·),p.2+2)
  | [true] => (none,1)
  | true::v::bs =>
    let p := words bs
    (p.1.bind (fun ws => match ws with
      | a::t => some ((2*a+v.toNat)::t) | _ => none),p.2+bs.length+5)

@[simp] theorem words_value (bs : List Bool) : (words bs).1=Wire.readDegrees bs := by
  induction bs using List.twoStepInduction with
  | nil => rfl
  | singleton x => cases x <;> rfl
  | cons_cons x y bs ih iz =>
    cases x <;> simp [words,Wire.readDegrees,ih,iz]
    cases z : Wire.readDegrees bs with
    | none => rfl
    | some ws => cases ws <;> rfl

theorem words_fee (bs : List Bool) : (words bs).2≤4*(bs.length+1)^2 := by
  induction bs using List.twoStepInduction with
  | nil => decide
  | singleton x => cases x <;> decide
  | cons_cons x y bs ih iz =>
    have z := iz y
    cases x
    · change (words (y::bs)).2+2≤_; simp only [List.length_cons] at z ⊢; ring_nf at z ⊢; omega
    · change (words bs).2+bs.length+5≤_; simp only [List.length_cons]; nlinarith

theorem words_count {bs ws} (h : Wire.readDegrees bs=some ws) : ws.length≤bs.length := by
  induction bs using List.twoStepInduction generalizing ws with
  | nil => simp [Wire.readDegrees] at h; subst ws; rfl
  | singleton b => cases b <;> simp [Wire.readDegrees] at h; subst ws; rfl
  | cons_cons b v bs ih iz =>
    cases b
    · cases old : Wire.readDegrees (v::bs) with
      | none => simp [Wire.readDegrees,old] at h
      | some ys => simp [Wire.readDegrees,old] at h; subst ws; simpa using iz v old
    · cases old : Wire.readDegrees bs with
      | none => simp [Wire.readDegrees,old] at h
      | some ys =>
        cases ys with
        | nil => simp [Wire.readDegrees,old] at h
        | cons a l => simp [Wire.readDegrees,old] at h; subst ws
                      have s := ih old; simp only [List.length_cons] at *; omega

def clauses (width : Nat) : List Nat → Option SatTy.denote × Nat
  | [] => (some [],1)
  | 0::xs =>
    let r := clauses width xs
    (r.1.map ([]::·),r.2+width+5)
  | (w+1)::xs =>
    let r := clauses width xs
    (r.1.bind (fun f => match f with
      | c::cs => some (((w/2,decide (w%2=1))::c)::cs) | _ => none),r.2+width+5)

@[simp] theorem clauses_value (w : Nat) (xs : List Nat) : (clauses w xs).1=readClauses xs := by
  induction xs with
  | nil => rfl
  | cons v xs ih => cases v <;> simp only [clauses,readClauses,ih]; rfl

theorem clauses_fee (w : Nat) (xs : List Nat) : (clauses w xs).2=xs.length*(w+5)+1 := by
  induction xs with
  | nil => simp [clauses]
  | cons v xs ih => cases v <;> simp [clauses,ih,Nat.succ_mul] <;> omega

def parse (bs : List Bool) : Option SatTy.denote × Nat :=
  let p := words bs
  match p.1 with
  | none => (none,p.2+1)
  | some xs =>
    let c := clauses bs.length xs
    (c.1,p.2+c.2+1)

@[simp] theorem parse_value (bs : List Bool) : (parse bs).1=readSAT bs := by
  simp only [parse,words_value,clauses_value,readSAT]
  cases Wire.readDegrees bs <;> rfl

theorem parse_fee (bs : List Bool) : (parse bs).2≤10*(bs.length+2)^2 := by
  have p := words_fee bs
  simp only [parse,words_value,clauses_fee]
  cases h : Wire.readDegrees bs with
  | none => dsimp; ring_nf at p ⊢; omega
  | some xs =>
    have s := Nat.mul_le_mul_right (bs.length+5) (words_count h)
    dsimp; nlinarith [Nat.zero_le (bs.length^2)]

/-- Emit each tagged binary field, charging the shift and bit extraction
by the length of the remaining suffix, plus the three list operations. -/
def field (n : Nat) : List Bool × Nat :=
  if n=0 then ([false],1) else
    let p := field (n/2)
    (true::decide (n%2=1)::p.1,p.2+p.1.length+5)
termination_by n
decreasing_by omega

@[simp] theorem field_value (n : Nat) : (field n).1=Wire.bin n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [field,Wire.bin]; split
    · rfl
    · simp [ih (n/2) (by omega)]

theorem field_fee (n : Nat) : (field n).2≤2*(Wire.bin n).length^2 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [field,Wire.bin]; split
    · decide
    · have old := ih (n/2) (by omega)
      simp only [field_value,List.length_cons]; nlinarith

def emit : List Nat → List Bool × Nat
  | [] => ([],1)
  | x::xs =>
    let a := field x
    let b := emit xs
    (a.1++b.1,a.2+b.2+a.1.length+2)

@[simp] theorem emitted (xs : List Nat) : (emit xs).1=Wire.degrees xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [emit,field_value,ih,Wire.degrees,List.flatMap_cons]

theorem emission_fee (xs : List Nat) : (emit xs).2≤4*((Wire.degrees xs).length+1)^2 := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    have a := field_fee x
    have pos : 0<(Wire.bin x).length := by rw [Wire.bin]; split <;> simp
    change _ ≤ 4*((Wire.bin x++Wire.degrees xs).length+1)^2
    simp only [emit,field_value,List.length_append]
    nlinarith [Nat.zero_le ((Wire.bin x).length*(Wire.degrees xs).length),Nat.zero_le ((Wire.bin x).length^2)]

/-- On a valid parse, evaluate the certified interpreter once, read its
unary output, compile the resulting instance and emit all degree fields. -/
def run (bs : List Bool) : List Bool × Nat :=
  let parsed := parse bs
  match parsed.1 with
  | none =>
    let b := emit malformedOutput
    (b.1,parsed.2+b.2+1)
  | some x =>
    let y := satToThree.code.eval x
    let I := importPartition (decodeNumberTargetUnary y)
    let compiled := ComplexityCost.compile I
    let out := emit compiled.value
    (out.1,parsed.2+satToThree.code.cost x+20*(NumberTargetUnaryTy.size y+1)+compiled.work+out.2+1)

theorem run_value (bs : List Bool) : (run bs).1=satWire bs := by
  simp only [run,parse_value,satWire,emitted,ComplexityCost.compile_value]
  cases readSAT bs with
  | none => rfl
  | some x => simp [Wire.reduceBits,Wire.reduceRow,Wire.source_round_trip,instanceOfSAT]

private def Poly (f : Nat → Nat) := ∃ C d : Nat, ∀ n, f n≤C*(n+1)^d

private theorem cn (a : Nat) : Poly (fun _ => a) := ⟨a,0,by simp⟩
private theorem identity : Poly (fun n => n) := ⟨1,1,by simp⟩

private theorem add {f g} (a : Poly f) (b : Poly g) : Poly (fun n => f n+g n) := by
  obtain ⟨c,i,F⟩ := a; obtain ⟨e,j,G⟩ := b
  refine ⟨c+e,max i j,fun n => ?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add ((F n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_left ..))))
    ((G n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.le_max_right ..))))

private theorem mul {f g} (a : Poly f) (b : Poly g) : Poly (fun n => f n*g n) := by
  obtain ⟨c,i,F⟩ := a; obtain ⟨e,j,G⟩ := b
  refine ⟨c*e,i+j,fun n => ?_⟩
  apply (Nat.mul_le_mul (F n) (G n)).trans_eq; rw [Nat.pow_add]; ring

private theorem power {f} (i : Nat) (h : Poly f) : Poly (fun n => (f n)^i) := by
  obtain ⟨c,j,F⟩ := h
  exact ⟨c^i,j*i,fun n => (Nat.pow_le_pow_left (F n) i).trans_eq (by rw [Nat.mul_pow,Nat.pow_mul])⟩

private theorem work_poly {f} (good : Poly f) : Poly (fun n => ComplexityCost.workBound (f n)) := by
  let S (n) := 5*f n+3
  let N (n) := 3^57*(S n)^73
  have hs : Poly S := add (mul (cn 5) good) (cn 3)
  have hn : Poly N := mul (cn _) (power 73 hs)
  change Poly (fun n => 100*(S n+f n+1) +
    9*(6*S n+10+(S n+1)*(12*S n+12)+4*(S n+1)) +
    (57+36*S n)*(13+7*N n+N n*(6+3*N n)))
  let s1 := add hs (cn 1)
  let s2 := add (mul (cn 12) hs) (cn 12)
  let term1 := mul (cn 100) (add (add hs good) (cn 1))
  let term2 := mul (cn 9) (add (add (add (mul (cn 6) hs) (cn 10)) (mul s1 s2)) (mul (cn 4) s1))
  let nl := add (add (cn 13) (mul (cn 7) hn)) (mul hn (add (cn 6) (mul (cn 3) hn)))
  exact add (add term1 term2) (mul (add (cn 57) (mul (cn 36) hs)) nl)

/-- The metered bitstring map is polynomial in the number of input bits on
all inputs, including malformed CNF syntax. -/
theorem run_work : ∃ C d : Nat, ∀ bs : List Bool, (run bs).2≤C*(bs.length+1)^d := by
  obtain ⟨A,d,build⟩ := compiler_work_polynomial
  obtain ⟨B,j,out⟩ := sat_output_polynomial
  obtain ⟨E,k,target⟩ := satToThree.code.cost_size_le_polyBound
  let offset (L : Nat) := 4*L+2
  let P (L) := 11+A*(offset L)^d
  let U (L) := E*(offset L)^k
  let W (L) := 13*(3^57*(5*(12+B*(offset L)^j)+6)^73+6)
  let cap (L : Nat) := 10*(L+2)^2 + (P L + ComplexityCost.workBound (P L)) +
    20*(U L+1)+4*(W L+1)^2+1
  have off : Poly offset := add (mul (cn 4) identity) (cn 2)
  have hp : Poly P := add (cn 11) (mul (cn A) (power d off))
  have hu : Poly U := mul (cn E) (power k off)
  have hw : Poly W := by
    dsimp only [W]
    let x := add (cn 12) (mul (cn B) (power j off))
    exact mul (cn 13) (add (mul (cn (3^57)) (power 73 (add (mul (cn 5) x) (cn 6)))) (cn 6))
  have poly : Poly cap := by
    dsimp only [cap]
    let p1 := mul (cn 10) (power 2 (add identity (cn 2)))
    let p2 := add hp (work_poly hp)
    let p3 := mul (cn 20) (add hu (cn 1))
    let p4 := mul (cn 4) (power 2 (add hw (cn 1)))
    exact add (add (add (add p1 p2) p3) p4) (cn 1)
  obtain ⟨C,r,hcap⟩ := poly
  refine ⟨C,r,fun bs => le_trans ?_ (hcap bs.length)⟩
  let L := bs.length
  have parsing := parse_fee bs
  have outputBound : (satWire bs).length≤W L := out bs
  have write (row : List Nat) (eq : Wire.degrees row=satWire bs) :
      (emit row).2≤4*(W L+1)^2 := by
    have same := emission_fee row
    rw [eq] at same
    exact same.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right outputBound 1) _))
  simp only [run,parse_value]
  cases h : readSAT bs with
  | none =>
    have e := write malformedOutput (by simp [satWire,h])
    change _≤cap L
    dsimp only [cap]
    dsimp only [L] at e ⊢; omega
  | some x =>
    let y := satToThree.code.eval x
    let I := instanceOfSAT x
    have fromSource : Wire.degrees (ComplexityCost.compile I).value=satWire bs := by
      simp [I,satWire,h,Wire.reduceBits,Wire.reduceRow,Wire.source_round_trip,ComplexityCost.compile_value]
    have output := write _ fromSource
    have b : satToThree.code.cost x + (ComplexityCost.compile I).work ≤ P L + ComplexityCost.workBound (P L) := build bs x h
    have e := target x
    change satToThree.code.cost x + NumberTargetUnaryTy.size y≤E*(SatTy.size x+1)^k at e
    have sl := read_sat_size bs h
    have z : NumberTargetUnaryTy.size y≤U L := (Nat.le_add_left ..).trans (e.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by change SatTy.size x+1≤4*bs.length+2; omega) _)))
    change _ ≤ cap L
    change (parse bs).2+satToThree.code.cost x+20*(NumberTargetUnaryTy.size y+1)+(ComplexityCost.compile I).work+
      (emit (ComplexityCost.compile I).value).2+1 ≤ 10*(L+2)^2+(P L+ComplexityCost.workBound (P L))+20*(U L+1)+4*(W L+1)^2+1
    dsimp only [L] at *; omega

/-- One binary reduction, charged polynomial and equivalent to the language
of polynomial-length concrete planar-rotation certificates. -/
theorem reduction :
    (∃ C d : Nat, ∀ bs : List Bool, (run bs).2≤C*(bs.length+1)^d) ∧
    ∀ bs : List Bool, SATLanguage bs ↔
      ∃ ds, Wire.readDegrees (run bs).1=some ds ∧ ds≠[] ∧ ∃ cert : List Bool,
        cert.length≤5*(ds.length+1)^3 ∧ RawWire.verify ds cert=true :=
  ⟨run_work,fun bs => run_value bs ▸ RawWire.sat_wire bs⟩

#print axioms reduction
end Recognition.SATCost
