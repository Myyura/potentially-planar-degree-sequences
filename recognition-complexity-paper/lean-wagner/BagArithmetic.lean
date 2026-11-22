import BagHom
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Arithmetic operations and intermediate integer sizes in the cached
homomorphism algorithm. Every previously summed variable is charged to
one factor, so multiplying independent tables never counts it twice. -/
namespace Recognition.BagArithmetic
open BagHom StateIso Finset

private abbrev Annotation (n m : Nat) := Factor n m × Nat

private def exponent (xs : List (Annotation n m)) := (xs.map Prod.snd).sum
private def valid (xs : List (Annotation n m)) := ∀a∈xs, ∀f,a.1.eval f≤m^a.2

private theorem prod_bound (xs : List (Annotation n m)) (good : valid xs) (f : Assignment n m) :
    weight (xs.map Prod.fst) f ≤ m^exponent xs := by
  induction xs with
  | nil => simp [weight,exponent]
  | cons a xs ih =>
    change a.1.eval f * weight (xs.map Prod.fst) f ≤ m^(a.2+exponent xs)
    rw [pow_add]
    exact Nat.mul_le_mul (good _ List.mem_cons_self _) (ih (fun _ h => good _ (List.mem_cons_of_mem _ h)))

private def Certificates (fs : List (Factor n m)) (k : Nat) := ∃xs : List (Annotation n m),
  xs.map Prod.fst=fs ∧ exponent xs=k ∧ valid xs

private theorem init (A : Colored n) (B : Colored m) (Y) : Certificates (constraints A B Y) 0 := by
  let fs := constraints A B Y
  refine ⟨fs.map (·,0),by simp [Function.comp_def,fs],by simp [exponent,Function.comp_def],?_⟩
  intro a mem f
  obtain ⟨F,inF,rfl⟩:=List.mem_map.mp mem
  simp only [fs,constraints,List.mem_append,List.mem_map] at inF
  rcases inF with ⟨i,_,rfl⟩|⟨e,_,rfl⟩ <;> simp [vertexFactor,edgeFactor] <;> split <;> decide

private theorem next (v : Fin n) (fill : Fin m) {fs : List (Factor n m)} {k} (cert : Certificates fs k) :
    Certificates (eliminate v fs fill) (k+1) := by
  obtain ⟨xs,rfl,rfl,good⟩ := cert
  let test (a : Annotation n m) := decide (v∈a.1.scope)
  let old := xs.filter test
  let kept := xs.filter (fun a => !(test a))
  have p : withVar v (xs.map Prod.fst)=old.map Prod.fst := by simp [withVar,old,test,List.filter_map,Function.comp_def]
  have q : withoutVar v (xs.map Prod.fst)=kept.map Prod.fst := by simp [withoutVar,kept,test,List.filter_map,Function.comp_def]
  have total : exponent old+exponent kept=exponent xs := by
    have h := ((List.filter_append_perm test xs).map Prod.snd).sum_eq
    simpa [exponent,old,kept] using h
  let F := cached (marginal v (xs.map Prod.fst)) fill
  refine ⟨(F,exponent old+1)::kept,by simp [F,eliminate,q],by simp [exponent] at total ⊢;omega,?_⟩
  intro a h f
  rcases List.mem_cons.mp h with rfl|ha
  · change F.eval f ≤ m^(exponent old+1)
    rw [cached_eval]
    change (∑i : Fin m, weight (withVar v (xs.map Prod.fst)) (Function.update f v i))≤_
    rw [p,pow_succ]
    calc
      _ ≤ ∑ _ : Fin m,m^exponent old := Finset.sum_le_sum (fun i _ => prod_bound _ (fun _ mem =>
        good _ (List.mem_filter.mp mem).1) _)
      _ = _ := by simp [Nat.mul_comm]
  · exact good a (List.mem_filter.mp ha).1 f

private theorem run_cert (fill : Fin m) (order : List (Fin n)) {fs : List (Factor n m)} {k}
    (cert : Certificates fs k) : Certificates (run fill order fs) (k+order.length) := by
  induction order generalizing fs k with
  | nil => simpa [run] using cert
  | cons v vs ih => simpa [run,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (next v fill cert)

private theorem factor_value {fs : List (Factor n m)} {k} (cert : Certificates fs k) (pos : 0<m)
    (F : Factor n m) (mem : F∈fs) (f : Assignment n m) : F.eval f≤m^k := by
  obtain ⟨xs,rfl,rfl,good⟩:=cert
  obtain ⟨⟨F,w⟩,h,rfl⟩:=List.mem_map.mp mem
  have sub : w≤exponent xs := by
    change w≤(xs.map Prod.snd).sum
    exact List.single_le_sum (fun v _ => Nat.zero_le v) _
      (List.mem_map.mpr ⟨(F,w),h,rfl⟩)
  exact (good _ h _).trans (Nat.pow_le_pow_right pos sub)

/-- A table value after k eliminations never exceeds m^k, even for zero or
incompatible partial assignments in the other tables. -/
theorem intermediate_bound (A : Colored n) (B : Colored m) (Y) (fill : Fin m) (order : List (Fin n))
    (F : Factor n m) (mem : F∈run fill order (constraints A B Y)) (f : Assignment n m) :
    F.eval f ≤ m^order.length := by
  have h := run_cert fill order (init A B Y)
  simp only [zero_add] at h
  exact factor_value h (by have := fill.isLt; omega) F mem f

theorem intermediate_bits (A : Colored n) (B : Colored m) (Y) (fill : Fin m) (order : List (Fin n))
    (F : Factor n m) (mem : F∈run fill order (constraints A B Y)) (f : Assignment n m) :
    (F.eval f).log2 ≤ order.length * PlanarDegrees.Frontier.cost m := by
  have v := intermediate_bound A B Y fill order F mem f
  have base : m≤2^PlanarDegrees.Frontier.cost m := (Nat.le_add_right _ 2).trans (PlanarDegrees.Frontier.cost_brackets m).2
  have pow := v.trans (Nat.pow_le_pow_left base order.length)
  rw [←pow_mul,mul_comm (PlanarDegrees.Frontier.cost m)] at pow
  by_cases zero : F.eval f=0
  · simp [zero]
  · apply Nat.lt_succ_iff.mp
    apply (Nat.log2_lt zero).mpr
    exact pow.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

/-- Each new marginal table has m summands per leaf. Each summand multiplies
one factor per member of the bucket; the final result is one further product. -/
def arithmetic (fill : Fin m) : List (Fin n) → List (Factor n m) → Nat
  | [],fs => fs.length
  | v::vs,fs => m^(bag v fs).card*m*((withVar v fs).length+1) + arithmetic fill vs (eliminate v fs fill)

private theorem more (v : Fin n) (fs : List (Factor n m)) (fill : Fin m) :
    (eliminate v fs fill).length≤fs.length+1 := by
  simpa [eliminate,withoutVar] using Nat.add_le_add_right (List.length_filter_le (fun F : Factor n m => decide (v∉F.scope)) fs) 1

theorem arithmetic_bound (fill : Fin m) (order : List (Fin n)) (fs : List (Factor n m)) :
    arithmetic fill order fs ≤ (tableRows fill order fs+1) * (m+1)*(fs.length+order.length+1) := by
  induction order generalizing fs with
  | nil => simp [arithmetic,tableRows]; nlinarith
  | cons v vs ih =>
    let rest := eliminate v fs fill
    have has := List.length_filter_le (fun F : Factor n m => decide (v∈F.scope)) fs
    change (withVar v fs).length≤fs.length at has
    have bound := more v fs fill
    change rest.length≤fs.length+1 at bound
    have recur := (ih rest).trans (Nat.mul_le_mul_left _ (show rest.length+vs.length+1 ≤ fs.length+(vs.length+1)+1 by omega))
    rw [arithmetic,tableRows,leaf_count,names_length]
    change m^(bag v fs).card*m*((withVar v fs).length+1) + arithmetic fill vs rest ≤
      (m^(bag v fs).card+tableRows fill vs rest+1)*(m+1)*(fs.length+(vs.length+1)+1)
    have head := Nat.mul_le_mul (Nat.mul_le_mul_left (m^(bag v fs).card) (Nat.le_succ m))
      (show (withVar v fs).length+1≤fs.length+(vs.length+1)+1 by omega)
    apply (Nat.add_le_add head recur).trans
    simp only [Nat.succ_eq_add_one];apply le_of_eq;ring

private theorem constraint_count (A : Colored n) (B : Colored m) (Y : Finset (Fin m)) :
    (constraints A B Y).length≤n+n*n := by
  have all (ls : List (Fin n)) : (ls.flatMap fun i => (List.finRange n).map (i,·)).length=ls.length*n := by
    induction ls with
    | nil => simp
    | cons a as ih => simp [ih,Nat.succ_mul,Nat.add_comm]
  have sub := List.length_filter_le (fun ij : Fin n×Fin n => A.edge ij.1 ij.2)
    ((List.finRange n).flatMap fun i => (List.finRange n).map (i,·))
  rw [all,List.length_finRange] at sub
  simpa [constraints,pairs] using Nat.add_le_add_left sub n

/-- All marginal sums and products in all exclusion terms are bounded
together, with their complete polynomial multiplicity. -/
theorem total_arithmetic (A : Colored n) (B : Colored m) (fill : Fin m) (K C : Nat)
    (source : n≤K) (target : m≤K) (D : Layout A (C*(K.sqrt+1))) :
    (∑ Y ∈ (univ : Finset (Fin m)).powerset,
      arithmetic fill (List.finRange n) (constraints A B Y)) ≤ 2^((6+9*C)*(K+1)) := by
  let R (Y) := tableRows fill (List.finRange n) (constraints A B Y)
  let terms := (univ : Finset (Fin m)).powerset
  have base : ∀Y, arithmetic fill (List.finRange n) (constraints A B Y) ≤
      (R Y+1)*((K+1)^3) := by
    intro Y
    have size := constraint_count A B Y
    have q : (m+1)*((constraints A B Y).length+(List.finRange n).length+1) ≤ (K+1)^3 := by
      simp only [List.length_finRange]
      have bound : (constraints A B Y).length+n+1≤(K+1)^2 := by
        have ini := Nat.mul_le_mul source source
        nlinarith
      exact (Nat.mul_le_mul (Nat.add_le_add_right target 1) bound).trans_eq (by ring)
    exact (arithmetic_bound ..).trans (by rw [mul_assoc]; apply Nat.mul_le_mul_left _ q)
  have rows := BagHom.square_root_table_bound A B K C source target D fill
  let b := (2+9*C)*(K+1)
  have nTerms : terms.card ≤ 2^b := by
    simp only [terms,Finset.card_powerset,Finset.card_univ,Fintype.card_fin]
    exact Nat.pow_le_pow_right (by decide) (by dsimp [b]; nlinarith)
  have small : K+1≤2^(K+1) := by exact (Nat.lt_two_pow_self (n := K+1)).le
  calc
    _ ≤ ∑ Y∈terms, (R Y+1)*((K+1)^3) := sum_le_sum (fun Y _ => base Y)
    _ = ((∑Y∈terms,R Y)+terms.card)*(K+1)^3 := by simp [←sum_mul,sum_add_distrib]
    _ ≤ (2^b+2^b)*(2^(K+1))^3 := Nat.mul_le_mul (Nat.add_le_add rows nTerms) (Nat.pow_le_pow_left small _)
    _ = 2^(b+1+(K+1)*3) := by
      rw [show 2^b+2^b=2^(b+1) by simp [pow_succ,Nat.mul_two],
        ←pow_mul (2:Nat) (K+1) 3,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by dsimp [b];nlinarith)

/-- Every partial alternating sum, including all signs, has polynomially
many bits in the graph orders. -/
theorem partial_alternating (A : Colored n) (B : Colored m) (order : List (Fin n))
    (perm : order.Perm (List.finRange n)) (terms : Finset (Finset (Fin m))) :
    |∑Y∈terms,(-1:Int)^Y.card*(count A B order Y:Int)| ≤ (2^m*m^n:Nat) := by
  have each (Y : Finset (Fin m)) : count A B order Y ≤ m^n := by
    rw [count_exact _ _ perm]
    unfold homCount
    exact ((Finset.card_le_card (Finset.filter_subset ..)).trans (homs A B).card_le_univ).trans_eq (by simp)
  have size : terms.card≤2^m := terms.card_le_univ.trans_eq (by simp)
  calc
    _ ≤ ∑Y∈terms,|(-1:Int)^Y.card*(count A B order Y:Int)| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _Y∈terms, ((m^n:Nat):Int) := Finset.sum_le_sum (fun Y _ => by
      simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,Int.natCast_nonneg,abs_of_nonneg]
      exact_mod_cast each Y)
    _ ≤ _ := by simp;exact_mod_cast (Nat.mul_le_mul_right (m^n) size)

end Recognition.BagArithmetic
