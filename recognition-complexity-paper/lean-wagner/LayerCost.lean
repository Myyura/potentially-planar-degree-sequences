import StateIncidence
import Mathlib.Data.Nat.Choose.Bounds

/-! A metered first-match search in a fixed table, with charges attached
to actual visited cells and the actual comparator and successor calls. -/
namespace Recognition.LayerCost
open PlanarDegrees.Frontier

variable {α : Type}

def seek (test : α → Bool × Nat) : List α → Option α × Nat
  | [] => (none,1)
  | x::xs =>
    let (hit,c) := test x
    if hit then (some x,c+1) else
      let (v,h) := seek test xs
      (v,c+1+h)

def collect (f : α → Option β × Nat) : List α → List β × Nat
  | [] => ([],1)
  | x::xs =>
      let (a,c) := f x
      let (rest,d) := collect f xs
      (a.elim rest (·::rest),c+d+1)

def pack (cmp eq : α → α → Bool × Nat) (table candidates : List α) :=
  let (hits,c) := collect (fun x => seek (cmp x) table) candidates
  let (out,d) := collect (fun t =>
    let (a,k) := seek (eq t) hits
    (a.map (fun _ => t),k)) table
  (out,c+d+1)

theorem seek_val (test : α → Bool × Nat) (xs : List α) :
    (seek test xs).1 = xs.find? (fun x => (test x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : (test x).1 <;> simp [seek,List.find?,h,ih]

theorem seek_cost (test : α → Bool × Nat) (xs : List α) (u : Nat)
    (budget : ∀ x∈xs, (test x).2≤u) : (seek test xs).2 ≤ xs.length*(u+1)+1 := by
  induction xs with
  | nil => simp [seek]
  | cons x xs ih =>
    have h := budget x (by simp)
    have tail := ih (fun y hy => budget y (by simp [hy]))
    cases b : (test x).1 <;> simp [seek,b,Nat.succ_mul] <;> omega

theorem collect_val (f : α → Option β × Nat) (xs : List α) :
    (collect f xs).1=xs.filterMap (fun x => (f x).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : (f x).1 <;> simp [collect,h,ih]

theorem collect_cost (f : α → Option β × Nat) (xs : List α) (v : Nat)
    (budget : ∀ x∈xs, (f x).2≤v) : (collect f xs).2≤xs.length*(v+1)+1 := by
  induction xs with
  | nil => simp [collect]
  | cons x xs ih =>
    have h := budget x (by simp)
    have tail := ih (fun y hy => budget y (by simp [hy]))
    simp [collect,Nat.succ_mul]; omega

theorem pack_val (same : α → α → Prop) [DecidableRel same] [DecidableEq α]
    (cmp eq : α → α → Bool × Nat) (hc : ∀ x y,(cmp x y).1=decide (same x y))
    (he : ∀ x y,(eq x y).1=decide (x=y)) (table cs : List α) :
    (pack cmp eq table cs).1=Table.pack same table cs := by
  let hits := cs.filterMap (Table.representative same table)
  have search (x) : (seek (cmp x) table).1=Table.representative same table x := by
    simp [seek_val,hc,Table.representative]
  have has (x : α) : ((seek (eq x) hits).1).isSome=decide (x∈hits) := by
    apply Bool.eq_iff_iff.mpr
    simp [seek_val,List.isSome_find?,List.any_eq_true,he]
  change (collect _ table).1=table.filter _
  rw [collect_val]
  have hit : (collect (fun x => seek (cmp x) table) cs).1=hits := by simp [collect_val,search,hits]
  simp only [hit]
  rw [←List.filterMap_eq_filter]
  apply List.filterMap_congr
  intro x hx
  change (seek (eq x) hits).1.map (fun _ => x) = if decide (x∈hits) then some x else none
  rw [←has]; cases (seek (eq x) hits).1 <;> rfl

theorem pack_cost (cmp eq : α → α → Bool × Nat) (table cs : List α) (u : Nat)
    (cmpFee : ∀ x y, (cmp x y).2≤u) (eqFee : ∀ x y,(eq x y).2≤u) :
    (pack cmp eq table cs).2 ≤ (cs.length+1)*(table.length+1)*(2*u+6) := by
  let got := collect (fun x => seek (cmp x) table) cs
  have h₁ : got.2 ≤ cs.length*(table.length*(u+1)+1+1)+1 :=
    collect_cost _ _ _ (fun x _ => seek_cost _ _ _ (fun y _ => cmpFee x y))
  have len : got.1.length≤cs.length := by
    dsimp only [got]; rw [collect_val]; exact List.length_filterMap_le ..
  let mark (t : α) := ((seek (eq t) got.1).1.map (fun _ => t),(seek (eq t) got.1).2)
  have h₂ : (collect mark table).2 ≤ table.length*(cs.length*(u+1)+1+1)+1 := by
    apply collect_cost
    intro x _
    exact (seek_cost _ _ _ (fun y _ => eqFee x y)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ len) _)
  change got.2+(collect mark table).2+1≤_
  nlinarith [Nat.zero_le cs.length,Nat.zero_le table.length,Nat.zero_le u]

/-- The cost paid to concatenate the finite lists includes a visit per
successor, independent of the charge for constructing that successor. -/
def expand (next : α → List α × Nat) : List α → List α × Nat
  | [] => ([],1)
  | s::ss =>
    let (a,b) := next s
    let (c,d) := expand next ss
    (a++c,b+a.length+d+1)

theorem expand_val (next : α → List α × Nat) (xs : List α) :
    (expand next xs).1=xs.flatMap (fun s => (next s).1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [expand,ih]

theorem expand_cost (next : α → List α × Nat) (xs : List α) (u z : Nat)
    (fee : ∀ x,(next x).2≤u) (count : ∀ x,(next x).1.length≤z) :
    (expand next xs).2≤xs.length*(u+z+1)+1 ∧ (expand next xs).1.length≤xs.length*z := by
  induction xs with
  | nil => simp [expand]
  | cons x xs ih =>
    obtain ⟨a,b⟩ := ih
    have c := fee x; have e := count x
    simp [expand,Nat.succ_mul]; constructor <;> omega

def layer (cmp eq : α → α → Bool × Nat) (table : List α) (next : α → List α × Nat) (seed : α) :
    Nat → List α × Nat
  | 0 => pack cmp eq table [seed]
  | k+1 =>
    let (prev,a) := layer cmp eq table next seed k
    let (cs,b) := expand next prev
    let (out,c) := pack cmp eq table cs
    (out,a+b+c+1)

theorem layer_val (same : α → α → Prop) [DecidableRel same] [DecidableEq α]
    (cmp eq : α → α → Bool × Nat) (hc : ∀ x y,(cmp x y).1=decide (same x y))
    (he : ∀ x y,(eq x y).1=decide (x=y)) (table : List α) (next : α → List α × Nat) (seed) (k) :
    (layer cmp eq table next seed k).1=Table.layer same table (fun x => (next x).1) seed k := by
  induction k with
  | zero => exact pack_val same cmp eq hc he _ _
  | succ k ih => simp only [layer,expand_val,ih,pack_val same cmp eq hc he,Table.layer]

private theorem pack_length (cmp eq : α → α → Bool × Nat) (table cs : List α) :
    (pack cmp eq table cs).1.length≤table.length := by
  unfold pack; rw [collect_val]; exact List.length_filterMap_le ..

private theorem layer_length (cmp eq : α → α → Bool × Nat) (table : List α) (next) (seed) (k) :
    (layer cmp eq table next seed k).1.length≤table.length := by
  cases k <;> apply pack_length

/-- Includes all rejected proposals and charges paid on negative inputs. -/
theorem layer_cost (cmp eq : α → α → Bool × Nat) (table : List α) (next : α → List α × Nat)
    (seed) (k u z : Nat) (cmpFee : ∀ x y,(cmp x y).2≤u) (eqFee : ∀ x y,(eq x y).2≤u)
    (fee : ∀ x,(next x).2≤u) (count : ∀ x,(next x).1.length≤z) :
    (layer cmp eq table next seed k).2 ≤ (k+1)*((table.length+2)^2*(z+2)*(2*u+8)) := by
  let t := table.length
  induction k with
  | zero =>
    have h := pack_cost cmp eq table [seed] u cmpFee eqFee
    simp only [List.length_singleton] at h
    apply h.trans
    rw [Nat.zero_add,Nat.one_mul,pow_two]
    have first : (1+1)*(table.length+1) ≤ (table.length+2)*(table.length+2) :=
      Nat.mul_le_mul (by omega) (by omega)
    exact Nat.mul_le_mul (first.trans (Nat.le_mul_of_pos_right _ (by omega))) (by omega)
  | succ k ih =>
    let prev := layer cmp eq table next seed k
    let cs := expand next prev.1
    have len : prev.1.length≤t := layer_length .. 
    have ⟨work,items⟩ := expand_cost next prev.1 u z fee count
    have count' : cs.1.length≤t*z := items.trans (Nat.mul_le_mul_right _ len)
    have work' : cs.2≤t*(u+z+1)+1 := work.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ len) 1)
    have pc := pack_cost cmp eq table cs.1 u cmpFee eqFee
    have pc' : (pack cmp eq table cs.1).2≤(t*z+1)*(t+1)*(2*u+6) :=
      pc.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.add_le_add_right count' 1)))
    change prev.2+cs.2+(pack cmp eq table cs.1).2+1 ≤ (k+1+1)*((t+2)^2*(z+2)*(2*u+8))
    change prev.2 ≤ (k+1)*((t+2)^2*(z+2)*(2*u+8)) at ih
    nlinarith

/-- Any fixed polylogarithmic exponent in the size of the coloured graph
is at most linear after changing the constant. -/
theorem log_power (q d : Nat) : ((q+1).log2+1)^d ≤ (d.factorial*2^d)*(q+1) := by
  let a := (q+1).log2
  calc
    _ ≤ (a+1).ascFactorial d := Nat.pow_succ_le_ascFactorial _ _
    _ = d.factorial*(a+d).choose d := Nat.ascFactorial_eq_factorial_mul_choose _ _
    _ ≤ d.factorial*(2^(a+d)) := Nat.mul_le_mul_left _ (Nat.choose_le_two_pow ..)
    _ ≤ _ := by rw [pow_add]; nlinarith [Nat.mul_le_mul_left (d.factorial*2^d) (Nat.log2_self_le (show q+1≠0 by omega))]

end Recognition.LayerCost
