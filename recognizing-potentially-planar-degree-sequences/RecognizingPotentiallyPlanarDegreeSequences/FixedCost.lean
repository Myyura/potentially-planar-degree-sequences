import RecognizingPotentiallyPlanarDegreeSequences.FixedVerifier
import RecognizingPotentiallyPlanarDegreeSequences.FixedGraphic
import RecognizingPotentiallyPlanarDegreeSequences.FixedLabels
import UnaryHardness

/-! An explicit unary-output reduction from bit-string SAT. The meter uses
the source compiler's charged list model. Later degree arithmetic and
table lookups are charged conservatively even for unary integers. -/
namespace RecognizingPotentiallyPlanarDegreeSequences.FixedCost
open Recognition SparseBoundary FixedBudget Polynomial

/-- The binary SAT compiler and the checked decoder share the local result. -/
def source (input : List Bool) : List Nat × Nat :=
  let b := SATCost.run input
  let parsed := WireSearch.decode b.1
  (parsed.1.getD [], b.2+parsed.2+1)

theorem source_spec (input : List Bool) :
    Reduction.TableValid (source input).1 ∧ Graphic (source input).1 ∧
    (SATBridge.SATLanguage input ↔ Planaric (source input).1) ∧
    (source input).1.length ≤ (SATBridge.satWire input).length := by
  obtain ⟨d,raw,valid,connected,iff,_⟩ := HardnessResult.restricted input
  have read := (WireSearch.parse_exact ..).mpr ⟨raw,fun _ h => (valid.2.2 _ h).2.le⟩
  have v : (source input).1=d := by simp only [source,(WireSearch.decode_work _).1,SATCost.run_value,read];rfl
  obtain ⟨G,hr,_⟩ := connected.2
  rw [v]
  exact ⟨valid,⟨G,hr⟩,iff,WireSearch.arity_eq _ raw ▸ (WireSearch.count_tags _).2.2⟩

theorem source_polynomial : ∃ P : Polynomial Nat, ∀ s : List Bool,
    (source s).1.length+(source s).2+1 ≤ P.eval s.length := by
  obtain ⟨a,i,bin⟩ := SATCost.run_work
  obtain ⟨b,j,out⟩ := SATBridge.sat_output_polynomial
  let Z := (X : Polynomial Nat)
  let B := 13*(3^57*(5*(12+C b*(4*Z+2)^j)+6)^73+6)
  refine ⟨C a*(Z+1)^i+7*B+4,fun s => ?_⟩
  have n := (source_spec s).2.2.2
  have work := (WireSearch.decode_work (SATCost.run s).1).2
  rw [SATCost.run_value] at work
  have old := bin s
  have len := out s
  change (source s).1.length+((SATCost.run s).2+(WireSearch.decode (SATCost.run s).1).2+1)+1 ≤ _
  rw [SATCost.run_value]
  simp [B,Z]
  omega

private def doubleRows : List Nat → List Nat × Nat
  | [] => ([],1)
  | x::xs => let z := doubleRows xs; (2*x::z.1,z.2+2*x+3)

private theorem doubleRows_spec (ds : List Nat) :
    (doubleRows ds).1=ds.map (2*·) ∧ (doubleRows ds).2=1+2*ds.sum+3*ds.length := by
  induction ds with
  | nil => simp [doubleRows]
  | cons x xs ih => simp [doubleRows,ih.1,ih.2];omega

/-- Build a full face layer, charging the doubled fields, length scan,
append traversal, new cubic fields and arithmetic on the lengths. -/
def fill (ds : List Nat) : List Nat × Nat :=
  let d := doubleRows ds
  let m := 2*ds.length-4
  (d.1++List.replicate m 3,d.2+8*(ds.length+1)+4*m+4)

@[simp] theorem fill_value (ds : List Nat) : (fill ds).1=full ds := by simp [fill,full,(doubleRows_spec ds).1]
theorem fill_work {ds : List Nat} (v : Reduction.TableValid ds) : (fill ds).2≤40*(ds.length+1) := by
  have := v.2.1
  simp only [fill,(doubleRows_spec ds).2]
  omega

/-- Padding depth is a constant for the fixed-budget reduction, and zero
for the linear-budget reduction. -/
def pad (ds : List Nat) : Nat → List Nat × Nat
  | 0 => (ds,1)
  | j+1 => let x := pad ds j; let y := fill x.1; (y.1,x.2+y.2+1)

theorem pad_spec {ds : List Nat} (v : Reduction.TableValid ds) (g : Graphic ds) (j : Nat) :
    Reduction.TableValid (pad ds j).1 ∧ Graphic (pad ds j).1 ∧
    (Planaric (pad ds j).1 ↔ Planaric ds) ∧ j+3 ≤ (pad ds j).1.length ∧
    (pad ds j).1.length+(pad ds j).2+1 ≤ 64^j*(ds.length+2) := by
  induction j with
  | zero => simp only [pad,Nat.zero_add,pow_zero,one_mul,iff_self]
            exact ⟨v,g,True.intro,by have := v.1;omega,by omega⟩
  | succ j ih =>
    obtain ⟨dv,dg,iff,low,cost⟩ := ih
    have fw := fill_work dv
    have hn := dv.1
    simp only [pad,fill_value]
    refine ⟨full_valid dv,full_graphic dv dg,(planaric_full_iff dv).trans iff,?_,?_⟩
    · rw [full_length];omega
    · rw [full_length,pow_succ]
      calc
        _ ≤ 64*((pad ds j).1.length+(pad ds j).2+1) := by omega
        _ ≤ 64*(64^j*(ds.length+2)) := Nat.mul_le_mul_left _ cost
        _ = _ := by ring

/-- Scan precisely the advertised indices. Each lookup and membership test
may traverse its entire list. With these lists and their natural entries
bounded by the supplied width, one quadratic charge covers both comparisons
and the degree increment in unary. -/
private def rows (width : Nat) (ds U : List Nat) : List Nat → List Nat × Nat
  | [] => ([],1)
  | i::is =>
    let z := rows width ds U is
    ((2*(ds[i]?.getD 0)+3*(U.contains i).toNat)::z.1,z.2+16*(width+1)^2)

private theorem rows_spec (w : Nat) (ds U I : List Nat) :
    (rows w ds U I).1 = I.map (fun i => 2*(ds[i]?.getD 0)+3*(U.contains i).toNat) ∧
    (rows w ds U I).2=1+I.length*(16*(w+1)^2) := by
  induction I with
  | nil => simp [rows]
  | cons i is h => simp [rows,h.1,h.2,Nat.succ_mul];omega

/-- The list lengths and operands of every marked-row lookup fit the
actual width used in the per-index charge. -/
theorem row_operands_bounded {d : List Nat} {r : Nat} (v : Reduction.TableValid d) (hr : r≤d.length) :
    let a := full (full d)
    let U := marks d.length r
    let width := a.length+2*r+d.length+4
    a.length≤width ∧ U.length≤width ∧ (∀ x∈a, x≤width) ∧
    (∀ i∈U, i≤width) ∧ (∀ i∈List.range a.length, i≤width) := by
  dsimp only
  have len : (marks d.length r).length=2*r := by simp [marks,Nat.two_mul]
  refine ⟨by omega,by omega,?_,?_,?_⟩
  · intro x hx
    have := ((full_valid (full_valid v)).2.2 x hx).2
    omega
  · intro i hi
    have := marks_bounded hr hi
    omega
  · intro i hi
    have := List.mem_range.mp hi
    omega

/-- The polynomial meter includes creating the two ranges of marked labels,
enumerating the old indices, writing the last cubic generation and appending. -/
def makeCore (d : List Nat) (r : Nat) : List Nat × Nat :=
  let x := fill d
  let y := fill x.1
  let n := d.length
  let N := y.1.length
  let b := 2*N-4+2*r
  let width := N+2*r+n+4
  let old := rows width y.1 (marks n r) (List.range N)
  (old.1++List.replicate b 3,x.2+y.2+old.2+16*(width+1)^2+4*b+8)

@[simp] theorem makeCore_value (d : List Nat) (r : Nat) : (makeCore d r).1=core d r := by
  simp only [makeCore,fill_value,core,oldRow,(rows_spec ..).1]
  rfl

theorem makeCore_bound {d : List Nat} {r : Nat} (v : Reduction.TableValid d) (fit : r≤d.length) :
    (makeCore d r).2 ≤ 1000000*(d.length+2)^3 := by
  have h1 := full_length d
  have h2 := full_length (full d)
  have f1 := fill_work v
  have f2 := fill_work (full_valid v)
  have le1 : (full d).length ≤ 3*d.length := by omega
  have le2 : (full (full d)).length ≤ 9*d.length := by omega
  simp only [makeCore,fill_value,(rows_spec ..).2,List.length_range]
  have size : (full (full d)).length+2*r+d.length+4+1 ≤ 12*(d.length+2) := by omega
  calc
    _ ≤ 40*(d.length+1)+40*(3*d.length+1)+(1+9*d.length*(16*(12*(d.length+2))^2))+
          16*(12*(d.length+2))^2+4*(2*(9*d.length)+2*d.length)+8 := by
      gcongr <;> omega
    _ ≤ _ := by ring_nf;omega

/-- Emit actual unary fields, terminated by zero bits, as in the source
archive. Writing a field and linking it to the suffix is charged twice. -/
private def emit : List Nat → List Bool × Nat
  | [] => ([],1)
  | x::xs => let y := emit xs; (List.replicate x true ++ false::y.1,y.2+2*x+3)

private theorem emit_spec (ds : List Nat) :
    (emit ds).1=Wire.unary ds ∧ (emit ds).2=1+2*ds.sum+3*ds.length := by
  induction ds with
  | nil => simp [emit,Wire.unary]
  | cons x xs h =>
    constructor
    · simp [emit,Wire.unary,h.1,List.append_assoc]
    · simp [emit,h.2];omega

/-- Source-side number of pairs. The linear verifier instead obtains that
number from the order of the emitted core. -/
def sourceBudget : FixedVerifier.Rule → Nat → Nat
  | .fixed r, _ => r
  | .linear, n => n-3

/-- One program for fixed and linear targets. The only budgeting functions
used below are a fixed constant and subtraction of three from the row length. -/
def run (rounds : Nat) (schedule : FixedVerifier.Rule) (s : List Bool) : List Bool × Nat :=
  let src := source s
  let d := pad src.1 rounds
  let r := sourceBudget schedule d.1.length
  let h := makeCore d.1 r
  let o := emit h.1
  (o.1,src.2+d.2+h.2+o.2+3*d.1.length+2*r+8)

def padded (j : Nat) (s : List Bool) := (pad (source s).1 j).1

theorem run_fields (j : Nat) (schedule : FixedVerifier.Rule) (s : List Bool) :
    (run j schedule s).1 = Wire.unary (core (padded j s) (sourceBudget schedule (padded j s).length)) := by
  simp only [run,padded,makeCore_value,(emit_spec _).1]

theorem padded_spec (j : Nat) (s : List Bool) :
    Reduction.TableValid (padded j s) ∧ Graphic (padded j s) ∧
      (SATBridge.SATLanguage s ↔ Planaric (padded j s)) ∧ j+3≤(padded j s).length := by
  obtain ⟨v,g,h,_⟩ := source_spec s
  obtain ⟨vv,gg,e,low,_⟩ := pad_spec v g j
  exact ⟨vv,gg,h.trans e.symm,low⟩

theorem run_length (j : Nat) (q : FixedVerifier.Rule) (s : List Bool)
    (fit : sourceBudget q (padded j s).length+3≤(padded j s).length) :
    (run j q s).1.length+12 = 7*(core (padded j s) (sourceBudget q (padded j s).length)).length := by
  rw [run_fields,Wire.unary_length]
  have := core_euler (padded_spec j s).1 fit
  omega

theorem run_polynomial (j : Nat) (q : FixedVerifier.Rule)
    (fit : ∀ s, sourceBudget q (padded j s).length+3≤(padded j s).length) :
    ∃ P : Polynomial Nat, ∀ s : List Bool, (run j q s).2+(run j q s).1.length ≤ P.eval s.length := by
  obtain ⟨F,hF⟩ := source_polynomial
  let B : Polynomial Nat := C (64^j)*(F+2)
  refine ⟨1000000*(B+2)^3+10000*(B+2)+F+100,fun s => ?_⟩
  let d := padded j s
  let r := sourceBudget q d.length
  have src := source_spec s
  have cap := hF s
  have ps := pad_spec src.1 src.2.1 j
  have val : Reduction.TableValid d := ps.1
  have range : r+3≤d.length := fit s
  have nb : d.length+(pad (source s).1 j).2+1≤B.eval s.length := by
    simp [B]; exact ps.2.2.2.2.trans (Nat.mul_le_mul_left _ (by omega))
  have make := makeCore_bound val (by omega : r≤d.length)
  have len := core_length r val
  have sums := core_euler val range
  have wire := run_length j q s range
  change _ +12=7*(core d r).length at wire
  have fee := (emit_spec (core d r)).2
  have df : (pad (source s).1 j).1=d := rfl
  change (source s).2+(pad (source s).1 j).2+(makeCore d r).2+
    (emit (makeCore d r).1).2+3*d.length+2*r+8+(run j q s).1.length ≤ _
  rw [makeCore_value,fee]
  simp only [eval_add,eval_mul,eval_pow]
  simp
  have wide : d.length≤B.eval s.length := by omega
  have big : 1000000*(d.length+2)^3≤1000000*(B.eval s.length+2)^3 := by gcongr
  omega

end RecognizingPotentiallyPlanarDegreeSequences.FixedCost
