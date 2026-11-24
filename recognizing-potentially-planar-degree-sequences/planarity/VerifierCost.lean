import RotationVerifier

/-! A charged list implementation of the orbit calculations. The unit is a
bounded number of word operations at a visited list cell. The four Euler
counts, the single-orbit-per-vertex test and dense input validation are charged
separately. No permutation or family of minor branch sets is enumerated. -/
namespace Recognition.VerifierCost
open SparseBoundary Recognition.OrbitTable Recognition.RotationVerifier

/-- At a union, the two named rows and every current vertex are looked up
by sequential scan. The last term includes output allocation. -/
def mergeWork (m k : Nat) := 2*(k+1)+(m+1)*(k+4)

variable {D : Type} [DecidableEq D]

def unionWork (xs : List D) : List (D×D) → Rows D → Nat
  | [],_ => 1
  | e::es,R => mergeWork xs.length R.length + unionWork xs es (merge xs R e)

theorem union_exact (xs : List D) (es : List (D×D)) (R : Rows D) (size : R.length=xs.length) :
    unionWork xs es R = es.length*mergeWork xs.length xs.length+1 := by
  induction es generalizing R with
  | nil => simp [unionWork]
  | cons e es ih =>
    have next : (merge xs R e).length=xs.length := by simp [merge,tabulate]
    rw [unionWork,ih _ next,size,List.length_cons,Nat.succ_mul]
    omega

/-- One generator gives m pairs, two give 2m. After the unions, the output
list has m labels. The quadratic scan removes repetitions. -/
def orbitBudget (m bands : Nat) := (bands+1)*(m+2) + bands*mergeWork m m + (m+1)^2 + 4

/-- Direct scan budgets for one dense certificate and its Euler test.
There is one union for the vertex rotation, one for edge reversal, one for
the face permutation, and one joint table with twice as many pairs. -/
def verificationBudget (n m : Nat) :=
  let dense := (n+1)^2*(n+2) + (m+1)*(n+2)^2
  let tableReads := (m+1)^2*(m+4)*6
  let single := orbitBudget m m
  let joint := orbitBudget m (2*m)
  40*(dense+tableReads+3*single+joint+1)

theorem visits_in_certificate_orbits (G : Graph n) (f rev : (Recognition.Wagner.toSimple G).Dart → (Recognition.Wagner.toSimple G).Dart) :
    let xs := darts G
    let a := xs.map fun x => (x,f x)
    let b := xs.map fun x => (x,rev x)
    let c := xs.map fun x => (x,f (rev x))
    let init := tabulate xs id
    unionWork xs a init + unionWork xs b init + unionWork xs c init + unionWork xs (a++b) init =
      5*xs.length*mergeWork xs.length xs.length+4 := by
  dsimp only
  have init : (tabulate (darts G) id).length = (darts G).length := by simp [tabulate]
  simp only [union_exact _ _ _ init,List.length_append,List.length_map]
  ring

/-- A fixed polynomial in the order bounds all charged list-scan budgets. -/
theorem polynomial (n m : Nat) (hm : m≤n*n) :
    verificationBudget n m ≤ 20000*(n+2)^6 := by
  dsimp only [verificationBudget,orbitBudget,mergeWork]
  calc
    _ ≤ 40*((n+1)^2*(n+2)+(n*n+1)*(n+2)^2+(n*n+1)^2*(n*n+4)*6 +
      3*((n*n+1)*(n*n+2)+(n*n)*(2*(n*n+1)+(n*n+1)*(n*n+4))+(n*n+1)^2+4) +
      ((2*(n*n)+1)*(n*n+2)+2*(n*n)*(2*(n*n+1)+(n*n+1)*(n*n+4))+(n*n+1)^2+4)+1) := by gcongr
    _ ≤ _ := by nlinarith [Nat.zero_le n]

end Recognition.VerifierCost
