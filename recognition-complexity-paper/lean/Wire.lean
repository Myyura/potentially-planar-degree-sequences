import StackedReduction

/-! Unary 3-PARTITION and explicit binary degree lists on a common bit alphabet.
Every bit string is assigned a reduction output, including malformed syntax. -/
namespace Recognition.Wire
open SparseBoundary Reduction Transfer

def unary (xs : List Nat) := xs.flatMap (fun n => List.replicate n true ++ [false])

def fields : List Bool → Option (List Nat)
  | [] => some []
  | false::xs => (fields xs).map (0::·)
  | true::xs => do
    let n::ns ← fields xs | none
    return (n+1)::ns

private theorem read_unary_field (a : Nat) (xs : List Bool) :
    fields (List.replicate a true ++ false::xs) = (fields xs).map (a::·) := by
  induction a with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ,List.cons_append,fields,ih]
    cases fields xs <;> rfl

theorem fields_unary (xs : List Nat) : fields (unary xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change fields ((List.replicate x true ++ [false]) ++ unary xs) = _
    rw [List.append_assoc, List.singleton_append,read_unary_field,ih]; rfl

theorem unary_length (xs : List Nat) : (unary xs).length = xs.sum+xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change ((List.replicate x true ++ [false]) ++ unary xs).length = _
    simp only [List.length_append, List.length_replicate,List.length_nil,List.sum_cons,List.length_cons,ih]
    omega

private theorem fields_sound {bits xs} (h : fields bits = some xs) : unary xs = bits := by
  induction bits generalizing xs with
  | nil => simp [fields] at h; subst xs; rfl
  | cons b bs ih =>
    cases b <;> cases hh : fields bs with
    | none => simp [fields,hh] at h
    | some ys =>
      have prev := ih hh
      first
      | simp [fields,hh] at h; subst xs; exact congrArg (false::·) prev
      | cases ys with
        | nil => simp [fields,hh] at h
        | cons n ns =>
          simp [fields,hh] at h
          subst xs
          change (List.replicate (n+1) true ++ [false]) ++ unary ns = _
          simpa [List.replicate_succ,unary,List.append_assoc] using congrArg (true::·) prev

def sourceCode (I : Instance) := unary (I.bins::I.capacity::I.weights)

def source : List Bool → Option Instance := fun bs => do
  let m::B::weights ← fields bs | none
  return ⟨weights,m,B⟩

theorem source_round_trip (I : Instance) : source (sourceCode I) = some I := by
  simp [source,sourceCode,fields_unary]

theorem source_sound {bs I} (ok : source bs = some I) : sourceCode I = bs := by
  cases hh : fields bs with
  | none => simp [source,hh] at ok
  | some xs =>
    obtain _|⟨m,_|⟨B,ws⟩⟩ := xs <;> simp [source,hh] at ok
    subst I
    exact fields_sound hh

theorem source_length (I : Instance) : (sourceCode I).length = ComplexityCost.unarySize I + 1 := by
  rw [sourceCode,unary_length]; simp [ComplexityCost.unarySize]; omega

/-- A zero tag terminates an entry. Each low-order data bit has a one tag. -/
def bin (n : Nat) : List Bool :=
  if n = 0 then [false] else true :: decide (n%2 = 1) :: bin (n/2)
termination_by n
decreasing_by omega

def degrees (d : List Nat) := d.flatMap bin

def readDegrees : List Bool → Option (List Nat)
  | [] => some []
  | false::xs => (readDegrees xs).map (0::·)
  | [true] => none
  | true::b::xs => do
    let n::ns ← readDegrees xs | none
    return (2*n+b.toNat)::ns

private theorem bin_rest (n : Nat) (rest : List Bool) :
    readDegrees (bin n ++ rest) = (readDegrees rest).map (n::·) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [bin]
    split
    · rename_i hn; subst n; rfl
    · rename_i hn
      simp only [List.cons_append,readDegrees,ih (n/2) (by omega)]
      cases hh : readDegrees rest with
      | none => rfl
      | some ns =>
        by_cases bit : n%2=1 <;> simp [bit] <;> omega

theorem degrees_round_trip (d : List Nat) : readDegrees (degrees d) = some d := by
  induction d with
  | nil => rfl
  | cons x xs ih => change readDegrees (bin x ++ degrees xs) = _; rw [bin_rest,ih]; rfl

private theorem bin_length (n : Nat) : (bin n).length ≤ 2*n+1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [bin]; split
    · simp_all
    · have := ih (n/2) (by omega)
      simp only [List.length_cons]; omega

theorem degrees_length (d : List Nat) : (degrees d).length ≤ 2*d.sum+d.length := by
  induction d with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    change (bin x ++ degrees xs).length ≤ _
    simp only [List.length_append,List.sum_cons,List.length_cons]
    have := bin_length x; omega

def reduceRow (bs : List Bool) : List Nat := (source bs).elim malformedOutput reduceInstance
def reduceBits (bs : List Bool) := degrees (reduceRow bs)

def UnaryThreePartition (bs : List Bool) := ∃ I, source bs = some I ∧ Valid I ∧ ThreePartition I

def degreeLanguage (P : List Nat → Prop) (bs : List Bool) :=
  ∃ d, readDegrees bs = some d ∧ d ≠ [] ∧ P d

theorem reduceRow_valid (bs : List Bool) : TableValid (reduceRow bs) := by
  cases h : source bs with
  | none => change TableValid ((source bs).elim _ _); rw [h]; change TableValid [5,5,5,3,3,3]; unfold TableValid; decide
  | some I => simpa [reduceRow,h] using reduce_promise I

theorem wire_iff (P : List Nat → Prop) (bad : ¬ P malformedOutput)
    (eqv : ∀ I, P (reduceInstance I) ↔ Valid I ∧ ThreePartition I) (bs : List Bool) :
    degreeLanguage P (reduceBits bs) ↔ UnaryThreePartition bs := by
  have non : reduceRow bs ≠ [] := by
    intro e; have h := (reduceRow_valid bs).1; rw [e] at h; contradiction
  simp only [degreeLanguage,reduceBits,degrees_round_trip,Option.some.injEq,exists_eq_left']
  change (reduceRow bs ≠ [] ∧ P (reduceRow bs)) ↔ _
  rw [and_iff_right non]
  cases h : source bs with
  | none => simp [UnaryThreePartition,reduceRow,h,bad]
  | some I => simpa [UnaryThreePartition,reduceRow,h] using eqv I

theorem wire_stacked (bs : List Bool) :
    degreeLanguage HasStackedRealization (reduceBits bs) ↔ UnaryThreePartition bs :=
  wire_iff _ (fun ⟨R,_⟩ => malformed_no_map ⟨R⟩) stacked_reduction_iff bs

theorem wire_planaric (inwards : HardnessConverse.TightEmbedding)
    (bs : List Bool) : degreeLanguage Planaric (reduceBits bs) ↔ UnaryThreePartition bs :=
  wire_iff _ Promise.malformed_no (reduction_iff inwards) bs

/-- A bound on the actual number of output bits, even for invalid strings. -/
theorem wire_length (bs : List Bool) :
    (reduceBits bs).length ≤ 13*(3^57*(5*bs.length+6)^73 + 6) := by
  have v := (reduceRow_valid bs).2.1
  have len : (reduceRow bs).length ≤ 3^57*(5*bs.length+6)^73 + 6 := by
    cases h : source bs with
    | none => simp [reduceRow,h,malformedOutput]
    | some I =>
      by_cases valid : Valid I
      · have sz := source_length I
        rw [source_sound h] at sz
        have ord : (sourceTable I).length ≤ 5*bs.length+6 := by
          rw [source_order]; unfold skeletonOrder ComplexityCost.unarySize at *; omega
        simp only [reduceRow,h,Option.elim,reduce_valid I valid]
        exact Nat.le_trans (encoded_polynomial I) (Nat.le_trans
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ord _)) (Nat.le_add_right ..))
      · simp [reduceRow,h,reduce_invalid I valid]
  have written := degrees_length (reduceRow bs)
  change (degrees (reduceRow bs)).length ≤ _
  omega
end Recognition.Wire
