import RawVerifierRotation
import HardnessResult

/-! An end-to-end metered verifier for ordinary, potentially planar rows.
Its bit is exactly that of the original verifier on every candidate
certificate. An overlength candidate is charged for the length scan only. -/
namespace Recognition.RawVerifierResult
open SparseBoundary ComplexityCost RotationVerifier RawVerifierData

/-- The two dense tables, degree comparison and orbit checker return both
the answers examined below and their incurred costs. -/
def onRaw (ds : List Nat) (C : Raw ds.length) : Meter Bool :=
  let ed:=enumerate C.graph
  let f:=readTable C.graph C.next ed.value
  let g:=readTable C.graph C.prev ed.value
  let base:=ed.work+f.work+g.work+3
  match f.value,g.value with
  | some a,some b =>
    let deg:=degrees ds C.graph
    let rot:=RawVerifierRotation.check ed.value a b
    ⟨deg.value && rot.value,base+deg.work+rot.work+1⟩
  | _,_ => ⟨false,base⟩

theorem raw_value (ds : List Nat) (C : Raw ds.length) : (onRaw ds C).value=verify ds C := by
  rw [←assembled]
  unfold onRaw
  simp only [enumerate_value]
  cases (readTable C.graph C.next (darts C.graph)).value <;>
    cases (readTable C.graph C.prev (darts C.graph)).value <;> simp [RawVerifierRotation.check_value]

theorem raw_work (ds : List Nat) (C : Raw ds.length) :
    (onRaw ds C).work≤60000*(ds.length+4)^8 := by
  let n:=ds.length
  let xs:=darts C.graph
  let m:=xs.length
  have size : m≤n*n := dart_count C.graph
  have dim : m+4≤(n+4)^2 := by nlinarith
  have scale : (m+4)^4≤(n+4)^8 := by
    simpa only [←pow_mul] using Nat.pow_le_pow_left dim 4
  have fourth : (n+2)^4≤(n+4)^8 := by
    have base : n+2≤(n+4)^2 := by nlinarith
    simpa only [←pow_mul] using Nat.pow_le_pow_left base 4
  have band : ∀ a,(readTable C.graph a xs).work≤32*(n+4)^8 := by
    intro a
    apply (table_work _ _ _).trans
    change m*(adjFee n+n*n+7)+1≤_
    calc
      _ ≤ (n*n)*(adjFee n+n*n+7)+1 := by gcongr
      _ ≤ 32*(n+2)^4 := by unfold adjFee;ring_nf;omega
      _ ≤ _ := Nat.mul_le_mul_left _ fourth
  have e := (enumerate_work C.graph).trans (Nat.mul_le_mul_left 24 fourth)
  have deg := (degrees_work ds C.graph).trans (Nat.mul_le_mul_left 24 fourth)
  have a:=band C.next;have b:=band C.prev
  unfold onRaw
  simp only [enumerate_value]
  change (match (readTable C.graph C.next xs).value,(readTable C.graph C.prev xs).value with
    | some u,some v => (⟨(degrees ds C.graph).value && (RawVerifierRotation.check xs u v).value,
      (enumerate C.graph).work+(readTable C.graph C.next xs).work+(readTable C.graph C.prev xs).work+3+
        (degrees ds C.graph).work+(RawVerifierRotation.check xs u v).work+1⟩ : Meter Bool)
    | _,_ => ⟨false,(enumerate C.graph).work+(readTable C.graph C.next xs).work+
        (readTable C.graph C.prev xs).work+3⟩).work≤60000*(n+4)^8
  have pos : 0<(n+4)^8 := pow_pos (by omega) _
  cases lf : (readTable C.graph C.next xs).value with
  | none => dsimp;omega
  | some u =>
    cases lg : (readTable C.graph C.prev xs).value with
    | none => dsimp;omega
    | some v =>
      have lu := (table_length _ _ lf).le
      have lv := (table_length _ _ lg).le
      have cc := (RawVerifierRotation.check_work xs u v lu lv).trans
        ((RawVerifierRotation.polynomial m).trans (Nat.mul_le_mul_left 40000 scale))
      dsimp only;omega

/-- The bounded raw parser is invoked only after inspecting the actual
certificate length. Every failure branch returns its own accumulated cost. -/
def run (ds : List Nat) (w : List Bool) : Meter Bool :=
  let entry:=ds.length+w.length+12
  if w.length≤5*(ds.length+1)^3 then
    let read:=RawWire.chargedDecode ds.length w
    match read.1 with
    | none => ⟨false,entry+read.2+1⟩
    | some C =>
      let checked:=onRaw ds C
      ⟨checked.value,entry+read.2+checked.work+1⟩
  else ⟨false,entry⟩

theorem run_value (ds : List Nat) (w : List Bool) :
    (run ds w).value=RawWire.verify ds w := by
  simp only [run,RawWire.verify,RawWire.charged_value]
  split
  · cases RawWire.decode ds.length w <;> simp [raw_value]
  · rfl

theorem run_work (ds : List Nat) (w : List Bool) :
    (run ds w).work≤ds.length+w.length+13+61000*(ds.length+4)^8 := by
  unfold run
  split
  next bound =>
    have raw := (RawWire.charged_budget ds.length w).trans
      ((RawWire.parser_polynomial ds.length w.length bound).trans
      (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (show ds.length+2≤ds.length+4 by omega) 8)))
    dsimp only
    cases h : (RawWire.chargedDecode ds.length w).1 with
    | none => dsimp;omega
    | some C => have checked:=raw_work ds C;dsimp only;omega
  · dsimp;omega

def wire (input w : List Bool) : Meter Bool :=
  let read:=WireSearch.decode input
  match read.1 with
  | some (x::xs) =>
    let checked:=run (x::xs) w
    ⟨checked.value,read.2+checked.work+2⟩
  | _ => ⟨false,read.2+2⟩

theorem wire_value (input w : List Bool) :
    (wire input w).value=HardnessResult.check input w := by
  simp only [wire,HardnessResult.check,(WireSearch.decode_work input).1]
  cases WireSearch.parse input with
  | none => rfl
  | some ds => cases ds <;> simp [run_value]

/-- Arbitrary malformed or overlong certificates are included. The separate
linear certificate term pays for rejecting a long bit string. -/
theorem wire_work (input w : List Bool) :
    (wire input w).work≤w.length+7*input.length+17+61000*(input.length+4)^8 := by
  have parsed:=WireSearch.decode_work input
  simp only [wire,parsed.1]
  cases h : WireSearch.parse input with
  | none => dsimp;omega
  | some ds =>
    have raw := ((WireSearch.parse_exact input ds).mp h).1
    have sz := (WireSearch.count_tags input).2.2
    rw [WireSearch.arity_eq input raw] at sz
    cases ds with
    | nil => dsimp;omega
    | cons x xs =>
      have ok := run_work (x::xs) w
      have pow:=Nat.pow_le_pow_left (Nat.add_le_add_right sz 4) 8
      dsimp only;omega

theorem positive_certificate (input : List Bool) : Wire.degreeLanguage Planaric input ↔
    ∃ w : List Bool,w.length≤5*(input.length+1)^3 ∧ (wire input w).value=true := by
  simp only [wire_value,HardnessResult.positive_certificate]

end Recognition.RawVerifierResult
