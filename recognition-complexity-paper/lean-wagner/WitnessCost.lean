import WitnessTable
import LayerCost

/-! Meter the executable table that returns one concrete history per key.
A fee is supplied per triangle proposal and per equivalence test. Each
visited list cell and each copied successor also incurs a unit charge. -/
namespace Recognition.WitnessCost
open QuotientDP WitnessTable LayerCost

def propose (fee : Entry n → Triangle n → Nat) (bound : Nat) (e : Entry n) :=
  collect (fun a => (step bound e a,fee e a)) (candidates n)

def store (cmp : State n → State n → Bool × Nat) (table : List (State n)) (cs : List (Entry n)) :=
  collect (fun t => seek (fun e => cmp (prune e.raw) t) cs) table

def run (cmp : State n → State n → Bool × Nat) (fee : Entry n → Triangle n → Nat)
    (table : List (State n)) (bound : Nat) (target : Multiset Nat) : Nat → List (Entry n) × Nat
  | 0 => store cmp table [init target]
  | k+1 =>
    let (previous,a) := run cmp fee table bound target k
    let (cs,b) := expand (propose fee bound) previous
    let (out,c) := store cmp table cs
    (out,a+b+c+1)

private theorem propose_val (fee : Entry n → Triangle n → Nat) (bound e) :
    (propose fee bound e).1=next bound e := by simp [propose,collect_val,next]

private theorem store_val (cmp : State n → State n → Bool × Nat) (table cs) :
    (store cmp table cs).1=index (fun a b => (cmp a b).1) table cs := by
  simp [store,collect_val,seek_val,index]

theorem output (cmp : State n → State n → Bool × Nat) (fee : Entry n → Triangle n → Nat)
    (table bound target k) : (run cmp fee table bound target k).1 =
      WitnessTable.layer (fun a b => (cmp a b).1) table bound target k := by
  induction k with
  | zero => exact store_val .. 
  | succ k ih => simp [run,WitnessTable.layer,store_val,expand_val,propose_val,ih]

private theorem store_cost (cmp : State n → State n → Bool × Nat) (table cs) (u : Nat)
    (compareFee : ∀ x y,(cmp x y).2≤u) : (store cmp table cs).2≤table.length*(cs.length*(u+1)+2)+1 :=
  collect_cost _ _ _ (fun t _ => seek_cost _ _ _ (fun x _ => compareFee _ _))

/-- The numeral bound also counts comparisons rejected by the first-match
search. It applies unchanged when no terminal history exists. -/
theorem work (cmp : State n → State n → Bool × Nat) (fee : Entry n → Triangle n → Nat)
    (table bound target k u) (comparison : ∀ x y,(cmp x y).2≤u) (proposal : ∀ x a,fee x a≤u) :
    (run cmp fee table bound target k).2 ≤ (k+1)*((table.length+2)^2*(n^3*8+2)*(u+8)) := by
  let t := table.length
  let z := n^3*8
  have proposals (e : Entry n) : (propose fee bound e).2≤z*(u+1)+1 := by
    simpa only [propose,candidate_count,z] using
      collect_cost (fun a => (step bound e a,fee e a)) (candidates n) u (fun a _ => proposal e a)
  have num (e : Entry n) : (propose fee bound e).1.length≤z := by
    rw [propose_val]; simpa [z,Nat.mul_comm] using next_bound bound e
  induction k with
  | zero =>
    have cost := store_cost cmp table [init target] u comparison
    simp only [List.length_singleton,one_mul] at cost
    apply cost.trans
    simp only [Nat.zero_add,one_mul]
    have mult : table.length+1 ≤ (table.length+2)^2*(n^3*8+2) := by
      calc
        _ ≤ (table.length+2)*(table.length+2) := (by nlinarith)
        _ ≤ _ := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
    apply Nat.le_trans _ (Nat.mul_le_mul_right (u+8) mult)
    nlinarith
  | succ k ih =>
    let prev := run cmp fee table bound target k
    let cs := expand (propose fee bound) prev.1
    have len : prev.1.length≤t := by rw [show prev.1=(WitnessTable.layer _ _ _ _ k) from output ..]; exact layer_bound ..
    have ⟨expense,items⟩ := expand_cost (propose fee bound) prev.1 _ z proposals num
    have nc : cs.1.length≤t*z := items.trans (Nat.mul_le_mul_right _ len)
    have ex : cs.2≤t*(z*(u+1)+1+z+1)+1 := expense.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ len) 1)
    have cost := store_cost cmp table cs.1 u comparison
    have cap : (store cmp table cs.1).2 ≤ t*(t*z*(u+1)+2)+1 :=
      cost.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ nc) 2)) 1)
    change prev.2+cs.2+(store cmp table cs.1).2+1≤(k+1+1)*((t+2)^2*(z+2)*(u+8))
    change prev.2 ≤ (k+1)*((t+2)^2*(z+2)*(u+8)) at ih
    nlinarith

/-- Composition of a fixed code-pool bound, per-call bound and the
polynomially bounded face and proposal counts on a square-root scale h. -/
theorem exponential (cmp : State n → State n → Bool × Nat) (fee : Entry n → Triangle n → Nat)
    (table bound target k u A B D E h) (comparison : ∀ x y,(cmp x y).2≤u) (proposal : ∀ x a,fee x a≤u)
    (steps : k+1≤2^(A*h)) (pool : table.length+2≤2^(B*h))
    (tri : n^3*8+2≤2^(D*h)) (call : u+8≤2^(E*h)) :
    (run cmp fee table bound target k).2 ≤ 2^((A+2*B+D+E)*h) := by
  apply (work cmp fee table bound target k u comparison proposal).trans
  calc
    _ ≤ 2^(A*h)*((2^(B*h))^2*2^(D*h)*2^(E*h)) :=
      Nat.mul_le_mul steps (Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left pool _) tri) call)
    _ = _ := by rw [←pow_mul,←pow_add,←pow_add,←pow_add]; congr 1; ring

end Recognition.WitnessCost
