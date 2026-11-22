import EliminationResult
import SATCost
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Metered construction for an arbitrary list of prescribed unordered pairs.
An input pair is supplied with its smaller endpoint first. As in ComplexityCost,
one visit covers a constant-size word kernel; membership scans use the length of
the scanned list. The output consists of the actual binary fields, including
their delimiters. -/
namespace Recognition.PrescriptionCost

open Reduction ComplexityCost EliminationResult
open Polynomial

/-- First free colour, including the work of every membership scan attempted.
Candidates are the integers from zero through the number of blocked colours. -/
private def firstFree (used : List Nat) : List Nat → Meter (Option Nat)
  | [] => ⟨none,1⟩
  | k::ks =>
    if used.contains k then
      let tail := firstFree used ks
      ⟨tail.value,tail.work+used.length+2⟩
    else ⟨some k,used.length+2⟩

private theorem firstFree_value (used ks : List Nat) :
    (firstFree used ks).value = ks.find? (fun k => !(used.contains k)) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => by_cases h : k ∈ used <;> simp [firstFree,List.find?,h,ih]

private theorem firstFree_cost (used ks : List Nat) :
    (firstFree used ks).work ≤ 1+ks.length*(used.length+2) := by
  induction ks with
  | nil => simp [firstFree]
  | cons k ks ih => by_cases h : k ∈ used <;> simp [firstFree,h,Nat.succ_mul] <;> omega

/-- Both incidence scans traverse all previously coloured edges. The copied
left list and both the colour map and candidate range are charged separately. -/
private def paintPass : List (Nat × Nat) → Meter (List Edge)
  | [] => ⟨[],1⟩
  | p::ps =>
    let tail := paintPass ps
    let incident := fun v => tail.value.filter fun e => e.left == v || e.right == v
    let left := incident p.1
    let right := incident p.2
    let blocked := (left++right).map Edge.color
    let free := firstFree blocked (List.range (blocked.length+1))
    ⟨⟨p.1,p.2,free.value.getD 0⟩::tail.value,
      tail.work+2*(tail.value.length+1)+(left.length+1)+3*(blocked.length+2)+free.work+1⟩

private theorem paint_value (rows : List (Nat × Nat)) : (paintPass rows).value = paint rows := by
  induction rows with
  | nil => rfl
  | cons p ps ih => simp only [paintPass,paint,ih,firstFree_value]; rfl

private theorem paint_length (rows : List (Nat × Nat)) : (paint rows).length=rows.length := by
  induction rows with
  | nil => rfl
  | cons p ps ih => simp [paint,ih]

private theorem paint_cost (rows : List (Nat × Nat)) (cap : Nat) (h : rows.length≤cap) :
    (paintPass rows).work ≤ 1+rows.length*(20*(cap+1)^2) := by
  induction rows with
  | nil => simp [paintPass]
  | cons p ps ih =>
    have small : ps.length≤cap := by simp at h; omega
    let tail := (paintPass ps).value
    let inc (v : Nat) := tail.filter fun e => e.left == v || e.right == v
    let blocked := (inc p.1 ++ inc p.2).map Edge.color
    have len : tail.length=ps.length := by simp [tail,paint_value,paint_length]
    have left : (inc p.1).length≤cap := (List.length_filter_le ..).trans (len ▸ small)
    have right : (inc p.2).length≤cap := (List.length_filter_le ..).trans (len ▸ small)
    have nb : blocked.length≤2*cap := by simp [blocked]; omega
    have fee := firstFree_cost blocked (List.range (blocked.length+1))
    rw [List.length_range] at fee
    have bound := Nat.mul_le_mul (Nat.add_le_add_right nb 1) (Nat.add_le_add_right nb 2)
    change (paintPass ps).work+2*(tail.length+1)+((inc p.1).length+1)+3*(blocked.length+2)+
      (firstFree blocked (List.range (blocked.length+1))).work+1 ≤ _
    simp only [List.length_cons,Nat.succ_mul]
    nlinarith [ih small]

private def colourTests (ms : List Mark) (w : Nat) : List Nat → Meter (List Test)
  | [] => ⟨[],1⟩
  | c::cs =>
    let group := ms.filter (·.edge.color == c)
    let head := addressTests w group
    let tail := colourTests ms w cs
    ⟨head.value++tail.value,ms.length+1+head.work+head.value.length+1+tail.work+1⟩

private theorem colourTests_value (ms : List Mark) (w : Nat) (cs : List Nat) :
    (colourTests ms w cs).value = cs.flatMap
      (fun c => classTests w (ms.filter (·.edge.color == c))) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [colourTests,addressTests_value,ih,List.flatMap_cons]

private theorem colourTests_cost (ms : List Mark) (w : Nat) (cs : List Nat) :
    (colourTests ms w cs).work ≤ 1+cs.length*(ms.length+10+w*(2*ms.length+16)) := by
  induction cs with
  | nil => simp [colourTests]
  | cons c cs ih =>
    let group := ms.filter (·.edge.color == c)
    have size : group.length≤ms.length := List.length_filter_le ..
    have fee := addressTests_work w group
    have scale := Nat.mul_le_mul_left w (show 2*group.length+12≤2*ms.length+12 by omega)
    simp only [colourTests,addressTests_value,classTests_length,List.length_cons]
    change ms.length+1+(addressTests w group).work+(2+4*w)+1+(colourTests ms w cs).work+1 ≤ _
    rw [Nat.succ_mul]
    nlinarith

private def prepare (s k : Nat) (es : List Edge) : Meter (List Test) :=
  let base := fullOrder s
  let ms := es.zipIdx.map fun (e,j) => Mark.mk e (base+j)
  let body := colourTests ms (bitWidth s) (List.range k)
  ⟨[full,full,full]++body.value,2*(es.length+1)+(k+1)+body.work+7⟩

private theorem prepare_value (I : Prescription) :
    (prepare I.degrees.length I.colours I.edges).value = allLayers I := by
  simp only [prepare,colourTests_value,allLayers,tests,matchingClass,markers]

private theorem prepare_cost (s k : Nat) (es : List Edge) :
    (prepare s k es).work ≤ 2*(es.length+1)+(k+1)+
      (1+k*(es.length+10+(s+1)*(2*es.length+16)))+7 := by
  let ms := es.zipIdx.map fun (e,j) => Mark.mk e (fullOrder s+j)
  have h := colourTests_cost ms (bitWidth s) (List.range k)
  have len : ms.length=es.length := by simp [ms]
  rw [len,List.length_range] at h
  have lenBits : bitWidth s≤s+1 := Nat.succ_le_succ (Nat.log2_le_self s)
  change 2*(es.length+1)+(k+1)+(colourTests ms (bitWidth s) (List.range k)).work+7 ≤ _
  gcongr
  exact h.trans (by gcongr)

private theorem schedule_length (I : Prescription) :
    (allLayers I).length = 3+I.colours*(2+4*bitWidth I.degrees.length) := by
  let s := I.degrees.length
  have h (cs : List Nat) : (cs.flatMap (fun c => classTests (bitWidth s) (matchingClass I c))).length =
      cs.length*(2+4*bitWidth s) := by
    induction cs with
    | nil => simp
    | cons c cs ih => simp [ih,classTests_length,Nat.succ_mul,Nat.add_comm]
  simp only [allLayers,List.length_append,tests]
  rw [h]; simp [s]

/-- The input and intermediate edge lists here have no proof fields. In
particular the program can be run before applying the correctness theorem. -/
private def compileRows (ds : List Nat) (es : List Edge) (k : Nat) : Meter (List Nat) :=
  let s := ds.length
  let m := es.length
  let inspect := s+m+4
  if s=4 ∨ es=[] then ⟨ds,inspect⟩
  else if m≤3*s-6 then
    let qs := prepare s k es
    let built := applyLayers ⟨ds,0⟩ qs.value
    ⟨built.value.degrees,inspect+qs.work+built.work+1⟩
  else ⟨malformedOutput,inspect+7⟩

private theorem compileRows_value (I : Prescription) :
    (compileRows I.degrees I.edges I.colours).value = EliminationResult.compile I := by
  simp [compileRows,EliminationResult.compile,prepare_value,applyLayers_value,output]
  split <;> simp_all
  split <;> simp_all

private def maxOrder (k : Nat) (x : Nat) := 3^(3+6*k)*x^(8*k+1)
private def prepBound (k x : Nat) := 2*(x+1)+(k+1)+(1+k*(x+10+(x+1)*(2*x+16)))+7
private def roundsBound (k x : Nat) := 3+k*(2+4*(x+1))
private def perLayer (n : Nat) := 13+7*n+n*(6+3*n)

private theorem compileRows_work (I : Prescription) (x : Nat)
    (s : I.degrees.length≤x) (m : I.edges.length≤x)
    (four : 4≤I.degrees.length) (total : I.degrees.sum+12=6*I.degrees.length)
    (range : ∀ a∈I.degrees, 3≤a ∧ a<I.degrees.length) :
    (compileRows I.degrees I.edges I.colours).work ≤
      2*x+12+prepBound I.colours x + roundsBound I.colours x*perLayer (maxOrder I.colours x) := by
  simp only [compileRows]
  split
  · dsimp; omega
  split
  next special possible =>
    have hv : BaseValid I := ⟨⟨by omega,total,range⟩,possible⟩
    have ready := compilation_run I hv
    have fee := applyLayers_work ready
    have outputSize := output_polynomial I (by omega)
    have cap : (output I).length≤maxOrder I.colours x := outputSize.trans (by unfold maxOrder; gcongr)
    have fee' : (applyLayers ⟨I.degrees,0⟩ (allLayers I)).work ≤
        1+(allLayers I).length*perLayer (output I).length := fee
    have q : (allLayers I).length≤roundsBound I.colours x := by
      rw [schedule_length]; unfold roundsBound bitWidth
      have := Nat.log2_le_self I.degrees.length
      gcongr; omega
    have fc := fee'.trans (Nat.add_le_add_left
      (Nat.mul_le_mul q (show perLayer (output I).length≤perLayer (maxOrder I.colours x) by
        unfold perLayer; gcongr)) 1)
    have pc : (prepare I.degrees.length I.colours I.edges).work≤prepBound I.colours x :=
      (prepare_cost ..).trans (by unfold prepBound; gcongr)
    dsimp only
    rw [prepare_value]
    omega
  · dsimp; omega

private theorem compiled_mass (I : Prescription) (four : 4≤I.degrees.length)
    (total : I.degrees.sum+12=6*I.degrees.length)
    (range : ∀ a∈I.degrees, 3≤a ∧ a<I.degrees.length) :
    (EliminationResult.compile I).sum+12=6*(EliminationResult.compile I).length := by
  unfold EliminationResult.compile
  split
  · exact total
  split
  next special possible =>
    exact (output_valid I ⟨⟨by omega,total,range⟩,possible⟩).2.1
  · decide

/-- Compile the uncoloured graph, then physically write the ordinary binary
degree list. Bounds and well-formedness of a prescription occur only in the
theorems, not as inputs to this computation. -/
def run (ds : List Nat) (rows : List (Nat × Nat)) (c : Nat) : Meter (List Bool) :=
  let coloured := paintPass rows
  let compiled := compileRows ds coloured.value (2*c-1)
  let written := SATCost.emit compiled.value
  ⟨written.1, coloured.work+compiled.work+written.2+2⟩

theorem run_value (ds rows c) (ordered) (nd) (deg) :
    (run ds rows c).value =
      Wire.degrees (EliminationResult.compile (ofPairs ds rows c ordered nd deg)) := by
  let I := ofPairs ds rows c ordered nd deg
  simp only [run,paint_value,SATCost.emitted]
  change Wire.degrees (compileRows I.degrees I.edges I.colours).value = _
  rw [compileRows_value]

/-- A single explicit polynomial per maximum prescribed degree. Its variable
counts the entries of the input row and of the pair list; each entry needs at
least one word in an explicit encoding. -/
noncomputable def workPolynomial (c : Nat) : Polynomial Nat :=
  let k := 2*c-1
  let x := (X : Polynomial Nat)
  let n := C (3^(3+6*k)) * x^(8*k+1)
  let prepareCost := 2*(x+1)+(C k+1)+(1+C k*(x+10+(x+1)*(2*x+16)))+7
  let allSteps := (3+C k*(2+4*(x+1)))*(13+7*n+n*(6+3*n))
  (1+x*(20*(x+1)^2))+(2*x+12+prepareCost+allSteps)+4*(13*n+1)^2+2

theorem polynomial_work (ds : List Nat) (rows : List (Nat × Nat)) (c : Nat) (ordered : ∀ p ∈ rows, p.1 < p.2 ∧ p.2 < ds.length)
    (nd : rows.Nodup) (deg : ∀ v, incidence rows v ≤ c) (four : 4≤ds.length)
    (total : ds.sum+12=6*ds.length) (range : ∀ a∈ds, 3≤a ∧ a<ds.length) :
    (run ds rows c).work ≤ (workPolynomial c).eval (ds.length+rows.length) := by
  let I := ofPairs ds rows c ordered nd deg
  let x := ds.length+rows.length
  let k := 2*c-1
  have size : I.degrees.length≤x := Nat.le_add_right ..
  have m : I.edges.length≤x := by
    change (paint rows).length≤ds.length+rows.length
    rw [paint_length]; omega
  have m' : rows.length≤x := Nat.le_add_left ..
  have paintCost := (paint_cost rows x m').trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ m') 1)
  have compCost := compileRows_work I x size m four total range
  have cap : (EliminationResult.compile I).length≤maxOrder k x :=
    (compile_polynomial I four).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left size _))
  have mass := compiled_mass I four total range
  have bits := Wire.degrees_length (EliminationResult.compile I)
  have encoded : (Wire.degrees (EliminationResult.compile I)).length≤13*maxOrder k x := by omega
  have emission := (SATCost.emission_fee (EliminationResult.compile I)).trans
    (show 4*((Wire.degrees (EliminationResult.compile I)).length+1)^2≤4*(13*maxOrder k x+1)^2 by gcongr)
  simp only [run,paint_value]
  change (paintPass rows).work+(compileRows I.degrees I.edges I.colours).work+
      (SATCost.emit (compileRows I.degrees I.edges I.colours).value).2+2 ≤ _
  rw [compileRows_value]
  apply (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add paintCost compCost) emission) 2).trans_eq
  simp [workPolynomial,prepBound,roundsBound,perLayer,maxOrder,I,ofPairs,k,x]


theorem uncoloured_compiler (ds : List Nat) (rows : List (Nat × Nat)) (c : Nat)
    (ordered : ∀ p∈rows, p.1<p.2 ∧ p.2<ds.length) (nd : rows.Nodup)
    (deg : ∀ v, incidence rows v ≤ c) (four : 4 ≤ ds.length) (total : ds.sum+12=6*ds.length)
    (range : ∀ a∈ds, 3≤a ∧ a<ds.length) :
    (run ds rows c).work ≤ (workPolynomial c).eval (ds.length+rows.length) ∧
    ((∃ xs, Wire.readDegrees (run ds rows c).value=some xs ∧ SparseBoundary.Planaric xs) ↔
     ∃ K : SparseBoundary.Graph ds.length, K.Realizes ds ∧ K.Planar ∧
       ∀ p∈rows, SourceConverse.natAdj K p.1 p.2=true) := by
  refine ⟨polynomial_work ds rows c ordered nd deg four total range, ?_⟩
  rw [run_value ds rows c ordered nd deg, Wire.degrees_round_trip]
  simpa only [Option.some.injEq,exists_eq_left'] using
    uncoloured_iff ds rows c ordered nd deg four total range

end Recognition.PrescriptionCost
