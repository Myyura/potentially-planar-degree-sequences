import FixedTypes
import SATCost
import WireSearch
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Canonical sparse language for explicitly listed inputs with few degree values. -/
namespace Recognition.FixedTypeLanguage
open SparseBoundary

def few (j : Nat) (ds : List Nat) : Prop :=
  (FixedTypes.support ds ds.length).length ≤ j

def listed (j : Nat) := Wire.degreeLanguage (fun ds => Planaric ds ∧ few j ds)

def canonical (j : Nat) (bs : List Bool) : Prop :=
  ∃ ds : List Nat, Wire.degrees ds = bs ∧ ds ≠ [] ∧
    ds.Pairwise (· ≥ ·) ∧ Planaric ds ∧ few j ds

private theorem few_perm {a b : List Nat} (p : a.Perm b) : few j a ↔ few j b := by
  have f : (fun d => a.contains d) = (fun d => b.contains d) := by
    funext d
    exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using (p.mem_iff (a:=d)))
  unfold few FixedTypes.support
  rw [p.length_eq,f]

/-- Each comparison of fields bounded by the parser cap is charged at most cap+1 bits. -/
def insert (cap a : Nat) : List Nat → List Nat × Nat
  | [] => ([a],1)
  | b::bs => if a ≥ b then (a::b::bs,cap+3) else
      let tail := insert cap a bs
      (b::tail.1,tail.2+cap+3)

private theorem insert_eq (cap a : Nat) (xs : List Nat) :
    (insert cap a xs).1 = xs.orderedInsert (· ≥ ·) a := by
  induction xs with
  | nil => rfl
  | cons b bs ih => by_cases h : a≥b <;> simp [insert,h,ih]

private theorem insert_fee (cap a : Nat) (xs : List Nat) :
    (insert cap a xs).2 ≤ (xs.length+1)*(cap+3) := by
  induction xs with
  | nil => simp [insert]
  | cons b bs ih =>
    simp only [insert,List.length_cons]; split <;> simp only <;> nlinarith

def sort (cap : Nat) : List Nat → List Nat × Nat
  | [] => ([],1)
  | a::xs =>
    let tail := sort cap xs
    let out := insert cap a tail.1
    (out.1,tail.2+out.2+1)

private theorem sort_eq (cap : Nat) (xs : List Nat) :
    (sort cap xs).1 = xs.insertionSort (· ≥ ·) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [sort,insert_eq,ih]

private theorem sort_fee (cap : Nat) (xs : List Nat) :
    (sort cap xs).2 ≤ (xs.length+1)^2*(cap+4) := by
  induction xs with
  | nil => simp [sort]
  | cons a xs ih =>
    simp only [sort,List.length_cons]
    have q := insert_fee cap a (sort cap xs).1
    have e : (sort cap xs).1.length=xs.length := by simp [sort_eq]
    rw [e] at q
    nlinarith

def normalize (bs : List Bool) : List Bool × Nat :=
  let p := WireSearch.decode bs
  match p.1 with
  | none => ([],p.2+1)
  | some ds =>
    let s := sort ds.length ds
    let out := SATCost.emit s.1
    (out.1,p.2+s.2+out.2+ds.length+1)

private theorem empty_miss : ¬ canonical j [] := by
  rintro ⟨xs,h,ne,_⟩
  have eq := Wire.degrees_round_trip xs
  rw [h] at eq
  exact ne (Option.some.inj eq.symm)

private theorem canonical_code (ds : List Nat) :
    canonical j (Wire.degrees ds) ↔ ds ≠ [] ∧ ds.Pairwise (· ≥ ·) ∧ Planaric ds ∧ few j ds := by
  constructor
  · rintro ⟨xs,h,hx⟩
    have e := congrArg Wire.readDegrees h
    simp only [Wire.degrees_round_trip,Option.some.injEq] at e
    exact e ▸ hx
  · exact fun h => ⟨ds,rfl,h⟩

theorem normalize_iff (bs : List Bool) (j : Nat) :
    canonical j (normalize bs).1 ↔ listed j bs := by
  have v := (WireSearch.decode_work bs).1
  cases eq : (WireSearch.decode bs).1 with
  | none =>
    simp only [normalize,eq,empty_miss,false_iff]
    rintro ⟨xs,raw,_,h,_⟩
    have hit := (WireSearch.parse_exact ..).2 ⟨raw,WireSearch.degrees_fit h⟩
    rw [← v,eq] at hit
    contradiction
  | some ds =>
    have raw := ((WireSearch.parse_exact ..).1 (v.symm.trans eq)).1
    have p := List.perm_insertionSort (· ≥ ·) ds
    have non : ds.insertionSort (· ≥ ·) ≠ [] ↔ ds ≠ [] := by
      apply not_congr
      constructor
      · intro h
        exact List.length_eq_zero_iff.mp (p.length_eq.symm.trans (by simp [h]))
      · intro h
        exact List.length_eq_zero_iff.mp (p.length_eq.trans (by simp [h]))
    simp only [normalize,eq,SATCost.emitted,sort_eq,canonical_code,non,
      List.pairwise_insertionSort,true_and,planaric_perm p,few_perm p,listed,Wire.degreeLanguage,raw,
      Option.some.injEq,exists_eq_left']

private theorem sum_bound (xs : List Nat) (n : Nat) (h : ∀ x∈xs, x≤n) :
    xs.sum ≤ xs.length*n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have a := h x (by simp)
    have b := ih (fun y mem => h y (by simp [mem]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul]; omega

theorem normalize_cost (bs : List Bool) :
    (normalize bs).2 ≤ 100*(bs.length+1)^4 := by
  obtain ⟨v,c⟩ := WireSearch.decode_work bs
  have quart (n : Nat) : n+1 ≤ (n+1)^4 := by
    simpa only [pow_one] using (Nat.pow_le_pow_right (show 0<n+1 by omega) (show 1≤4 by decide))
  cases eq : (WireSearch.decode bs).1 with
  | none => simp only [normalize,eq]; nlinarith [quart bs.length]
  | some ds =>
    obtain ⟨r,bound⟩ := (WireSearch.parse_exact ..).1 (v.symm.trans eq)
    have len := SATCost.words_count r
    let xs := (sort ds.length ds).1
    have p : xs.Perm ds := by simpa [xs,sort_eq] using List.perm_insertionSort (· ≥ ·) ds
    have f := sort_fee ds.length ds
    have g := SATCost.emission_fee xs
    have e := Wire.degrees_length xs
    have s := sum_bound ds ds.length bound
    rw [p.length_eq,p.sum_eq] at e
    have b : (Wire.degrees xs).length+1 ≤ 2*ds.length^2+ds.length+1 := by nlinarith
    have k := Nat.pow_le_pow_left b 2
    have h := Nat.pow_le_pow_left (Nat.add_le_add_right len 1) 4
    simp only [normalize,eq]
    change (WireSearch.decode bs).2+(sort ds.length ds).2+
      (SATCost.emit xs).2+ds.length+1 ≤ _
    have room : (sort ds.length ds).2 + (SATCost.emit xs).2 + ds.length+1 ≤ 90*(ds.length+1)^4 := by
      nlinarith [Nat.zero_le (ds.length^3),Nat.zero_le (ds.length^4),Nat.zero_le (ds.length^2)]
    nlinarith [quart bs.length]

/-- Finite superset of all canonical yes strings of length at most L. -/
private noncomputable def atOrder (n j : Nat) : Finset (List Bool) := by
  classical
  have := FixedTypes.finite_profiles n j
  let _ := Fintype.ofFinite (FixedTypes.Profile n j)
  exact Finset.univ.image (fun p : FixedTypes.Profile n j => Wire.degrees p.degrees)

private theorem atOrder_card (n j : Nat) : (atOrder n j).card ≤ (n+1)^(2*j) := by
  classical
  have := FixedTypes.finite_profiles n j
  let _ := Fintype.ofFinite (FixedTypes.Profile n j)
  apply Finset.card_image_le.trans
  simpa only [Finset.card_univ,← Nat.card_eq_fintype_card] using (FixedTypes.count_bound n j)

noncomputable def cover (L j : Nat) := (Finset.range (L+1)).biUnion (fun n => atOrder n j)

theorem covered {j L : Nat} {bs : List Bool} (h : canonical j bs) (len : bs.length≤L) :
    bs ∈ cover L j := by
  classical
  obtain ⟨ds,rfl,_,sorted,yes,types⟩ := h
  have n := (SATCost.words_count (Wire.degrees_round_trip ds)).trans len
  have := FixedTypes.finite_profiles ds.length j
  let _ := Fintype.ofFinite (FixedTypes.Profile ds.length j)
  let p : FixedTypes.Profile ds.length j := ⟨ds,rfl,WireSearch.degrees_fit yes,sorted,types⟩
  exact Finset.mem_biUnion.mpr ⟨ds.length,Finset.mem_range.mpr (by omega),
    Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩⟩

theorem cover_card (L j : Nat) : (cover L j).card ≤ (L+1)^(2*j+1) := by
  classical
  calc
    _ ≤ ∑ n ∈ Finset.range (L+1), (atOrder n j).card := Finset.card_biUnion_le
    _ ≤ ∑ _n ∈ Finset.range (L+1), (L+1)^(2*j) := by
      apply Finset.sum_le_sum
      intro n hn
      exact (atOrder_card n j).trans (Nat.pow_le_pow_left (by have := Finset.mem_range.mp hn; omega) _)
    _ = _ := by simp [pow_succ,Nat.mul_comm]

end Recognition.FixedTypeLanguage
