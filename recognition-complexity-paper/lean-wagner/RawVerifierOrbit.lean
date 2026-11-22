import OrbitTable
import ComplexityCost
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-! List-cell accounting for every lookup and union in the rotation verifier.
Comparing two dart labels takes a bounded number of word operations. -/
namespace Recognition.RawVerifierOrbit
open Recognition.ComplexityCost Recognition.OrbitTable
variable {D : Type} [DecidableEq D]

def read (R : Rows D) (x : D) : Meter D :=
  match R with
  | [] => ⟨x,1⟩
  | (u,v)::tail =>
    if x=u then ⟨v,2⟩ else let q := read tail x; ⟨q.value,q.work+2⟩

theorem read_value (R : Rows D) (x : D) : (read R x).value = key R x := by
  induction R with
  | nil => rfl
  | cons p tail ih =>
    rcases p with ⟨u,v⟩
    by_cases h : x=u
    · simp [read,key,List.lookup,h]
    · simp [read,key,List.lookup,h,ih,beq_eq_false_iff_ne.mpr h]

theorem read_work (R : Rows D) (x : D) : (read R x).work ≤ 8*(R.length+1) := by
  induction R with
  | nil => simp [read]
  | cons p tail ih => rcases p with ⟨u,v⟩; simp only [read,List.length_cons]; split <;> simp only <;> omega

private def rows (R : Rows D) (a b : D) : List D → Meter (Rows D)
  | [] => ⟨[],1⟩
  | x::xs =>
    let label := read R x
    let rest := rows R a b xs
    ⟨(x,if label.value=b then a else label.value)::rest.value,label.work+rest.work+3⟩

private theorem rows_val (R : Rows D) (a b : D) (xs : List D) :
    (rows R a b xs).value=tabulate xs (fun x => let t := key R x; if t=b then a else t) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [rows,tabulate,read_value] at ih ⊢; exact ih

private theorem rows_cost (R : Rows D) (a b : D) (xs : List D) :
    (rows R a b xs).work ≤ xs.length*(8*(R.length+1)+3)+1 := by
  induction xs with
  | nil => simp [rows]
  | cons x xs ih =>
    simp only [rows,List.length_cons,Nat.add_mul,one_mul]
    have fee := read_work R x
    omega

private def union (xs : List D) (R : Rows D) (e : D × D) : Meter (Rows D) :=
  let a := read R e.1
  let b := read R e.2
  let s := rows R a.value b.value xs
  ⟨s.value,a.work+b.work+s.work+1⟩

private theorem union_val (xs : List D) (R : Rows D) (e : D × D) :
    (union xs R e).value = merge xs R e := by simp [union,rows_val,read_value,merge]

private theorem union_fee (xs : List D) (R : Rows D) (e : D × D) (h : R.length=xs.length) :
    (union xs R e).work+1 ≤ 20*(xs.length+2)^2 := by
  have a := read_work R e.1
  have b := read_work R e.2
  have q := rows_cost R (read R e.1).value (read R e.2).value xs
  rw [h] at a b q
  simp only [union]; nlinarith [Nat.zero_le (xs.length^2)]

private def unions (xs : List D) (R : Rows D) : Rows D → Meter (Rows D)
  | [] => ⟨R,1⟩
  | e::es =>
    let first := union xs R e
    let tail := unions xs first.value es
    ⟨tail.value,first.work+tail.work+1⟩

private theorem unions_val (xs : List D) (es R : Rows D) :
    (unions xs R es).value=es.foldl (merge xs) R := by
  induction es generalizing R with
  | nil => rfl
  | cons e es ih => simp [unions,ih,union_val]

private theorem unions_fee (xs : List D) (es R : Rows D) (h : R.length=xs.length) :
    (unions xs R es).work ≤ es.length*(20*(xs.length+2)^2)+1 := by
  induction es generalizing R with
  | nil => simp [unions]
  | cons e es ih =>
    have tail := ih (union xs R e).value (by simp [union_val,merge,tabulate])
    have start := union_fee xs R e h
    simp only [unions,List.length_cons,Nat.add_mul,one_mul]; omega

private def identityRows : List D → Meter (Rows D)
  | [] => ⟨[],1⟩
  | x::xs => let rest := identityRows xs; ⟨(x,x)::rest.value,rest.work+2⟩

omit [DecidableEq D] in
private theorem identity_spec (xs : List D) : (identityRows xs).value=tabulate xs id ∧
    (identityRows xs).work=2*xs.length+1 := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih => simp [identityRows,ih.1,ih.2,tabulate]; omega

def run (xs : List D) (es : Rows D) : Meter (Rows D) :=
  let start := identityRows xs
  let out := unions xs start.value es
  ⟨out.value,start.work+out.work+1⟩

theorem run_value (xs : List D) (es : Rows D) : (run xs es).value=OrbitTable.run xs es := by
  simp [run,unions_val,(identity_spec xs).1,OrbitTable.run]

theorem run_length (xs : List D) (es : Rows D) : (run xs es).value.length=xs.length := by
  rw [run_value]
  suffices ∀ R : Rows D, R.length=xs.length → (es.foldl (merge xs) R).length=xs.length from
    this _ (by simp [tabulate])
  induction es with
  | nil => exact fun _ h => h
  | cons e es ih => exact fun R _ => ih _ (by simp [merge,tabulate])

theorem run_work (xs : List D) (es : Rows D) :
    (run xs es).work ≤ 64*(xs.length+es.length+4)^4 := by
  let q := xs.length+es.length+4
  have a : xs.length+2≤q := by dsimp [q]; omega
  have b : es.length≤q := by dsimp [q]; omega
  have y := unions_fee xs es (identityRows xs).value (by simp [(identity_spec xs).1,tabulate])
  have z : es.length*(20*(xs.length+2)^2) ≤ q*(20*q^2) :=
    Nat.mul_le_mul b (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left a _))
  have pos : 0<q := by dsimp [q]; omega
  have p := Nat.pow_le_pow_right pos (by decide : 3≤4)
  have v : q≤q^4 := by simpa using Nat.pow_le_pow_right pos (by decide : 1≤4)
  simp only [run,(identity_spec xs).2]
  change _ ≤ 64*q^4
  nlinarith [Nat.one_le_pow' q 4]

private def occurs (v : D) : Rows D → Meter Bool
  | [] => ⟨false,1⟩
  | (_,x)::rest =>
    if v=x then ⟨true,2⟩ else let tail := occurs v rest; ⟨tail.value,tail.work+2⟩

private theorem occurs_spec (v : D) (R : Rows D) : ((occurs v R).value=true ↔ v∈R.map Prod.snd) ∧
    (occurs v R).work≤2*(R.length+1) := by
  induction R with
  | nil => simp [occurs]
  | cons p tail ih =>
    rcases p with ⟨u,x⟩
    by_cases h : v=x
    · simp [occurs,h]
    · simp [occurs,h,ih.1]; omega

def count : Rows D → Meter Nat
  | [] => ⟨0,1⟩
  | (_,v)::rest =>
    let duplicate := occurs v rest
    let tail := count rest
    ⟨if duplicate.value then tail.value else tail.value+1,duplicate.work+tail.work+3⟩

theorem count_value (R : Rows D) : (count R).value=OrbitTable.count R := by
  induction R with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨u,v⟩
    simp only [count,OrbitTable.count_cons,ih,(occurs_spec v rest).1]

theorem count_work (R : Rows D) : (count R).work≤16*(R.length+2)^2 := by
  induction R with
  | nil => simp [count]
  | cons p rest ih =>
    obtain ⟨u,v⟩ := p
    have cost := (occurs_spec v rest).2
    simp only [count,List.length_cons]; nlinarith

end Recognition.RawVerifierOrbit
