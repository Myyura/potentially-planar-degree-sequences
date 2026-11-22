import SparseBoundary.ZeroPadding

/-! Star forests distinguish exponentially many degree multisets at a fixed order.
The target predicate is the project's forbidden-minor definition of potential planarity. -/
namespace Recognition.Enumeration
open SparseBoundary

private theorem emptyPlanar : Planaric [] :=
  ⟨⟨0⟩, fun i => i.elim0, Graph.planar_of_few_high _ (by decide)⟩

/-- The first vertex is the centre, followed by k leaves. -/
def star (k : Nat) := k :: List.replicate k 1

theorem star_planaric (k : Nat) : Planaric (star k) := by
  induction k with
  | zero => exact (ZeroPadding.planaric [] 1).2 emptyPlanar
  | succ k ih =>
    let d := star k
    let r : Fin d.length := ⟨0, by simp [d, star]⟩
    have h := planaric_attach_leaf ih r
    have row : List.ofFn (fun i : Fin d.length => d[i] + (if i = r then 1 else 0)) =
        (k+1)::List.replicate k 1 := by
      apply List.ext_getElem
      · simp [d, star]
      · intro i hi _
        cases i with
        | zero => simp [d, star, r]
        | succ i =>
          simp only [List.getElem_ofFn]
          have ne (u : Fin d.length) (hu : u.val = i+1) : u ≠ r := by
            intro he
            rw [he] at hu
            change 0 = i+1 at hu
            omega
          rw [ite_eq_right (ne _ rfl), Nat.add_zero]
          change (k::List.replicate k 1)[i+1] = ((k+1)::List.replicate k 1)[i+1]
          rfl
    rw [row] at h
    exact (planaric_perm (List.Perm.swap _ _ _)).mp h

/-- Every bit uses the same number of vertices for either value. At the head
of a word of length k, the star (when present) has k+1 leaves. -/
def forest : List Bool → List Nat
  | [] => []
  | b :: bs =>
    (if b then star (bs.length + 2) else List.replicate (bs.length + 3) 0) ++ forest bs

def order : Nat → Nat
  | 0 => 0
  | k+1 => k + 3 + order k

theorem forest_length (bs : List Bool) : (forest bs).length = order bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [forest, star, ih, order, Nat.add_assoc] <;> omega

theorem forest_planaric (bs : List Bool) : Planaric (forest bs) := by
  induction bs with
  | nil => exact emptyPlanar
  | cons b bs ih =>
    cases b
    · exact planaric_append (by simpa using (ZeroPadding.planaric [] (bs.length+3)).2 emptyPlanar) ih
    · exact planaric_append (star_planaric _) ih

private theorem le_length {bs : List Bool} {v : Nat} (h : v ∈ forest bs) : v ≤ bs.length+1 := by
  induction bs with
  | nil => simp [forest] at h
  | cons b bs ih =>
    cases b <;> simp [forest, star] at h <;> simp only [List.length_cons] <;> grind

/-- Reading the multiset determines the original word, even after arbitrary
permutation of its entries. -/
theorem forest_bits {bs cs : List Bool} (hlen : bs.length = cs.length)
    (p : (forest bs).Perm (forest cs)) : bs = cs := by
  induction bs generalizing cs with
  | nil => simpa using hlen.symm
  | cons b bs ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have e : bs.length = cs.length := by simpa using hlen
      have peak (t : Bool) (xs : List Bool) :
          xs.length+2 ∈ forest (t::xs) ↔ t = true := by
        have h : xs.length+2 ∉ forest xs := fun h => by have := le_length h; omega
        cases t <;> simp [forest, star, h]
      have bc : b = c := by
        have z : (bs.length+2 ∈ forest (b::bs)) ↔ (bs.length+2 ∈ forest (c::cs)) := p.mem_iff
        rw [peak b bs, e, peak c cs] at z
        cases b <;> cases c <;> simp_all
      subst c
      simp only [forest, e] at p
      exact congrArg (List.cons b) (ih e ((List.perm_append_left_iff _).mp p))

theorem order_formula (k : Nat) : 2 * order k = k * (k + 5) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [order, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at *; omega

def padded (n : Nat) (bs : List Bool) := forest bs ++ List.replicate (n - order bs.length) 0

/-- For each n with k(k+5) ≤ 2n, the 2^k binary words of length k
give pairwise different realizable n-vertex degree multisets. -/
theorem output_family (k n : Nat) (fits : k*(k+5) ≤ 2*n) :
    (∀ bs : List Bool, bs.length = k → (padded n bs).length = n ∧ Planaric (padded n bs)) ∧
    (∀ bs cs : List Bool, bs.length = k → cs.length = k →
        (padded n bs).Perm (padded n cs) → bs = cs) := by
  constructor
  · intro bs hb
    constructor
    · simp only [padded, List.length_append, forest_length, List.length_replicate, hb]
      have := order_formula k
      omega
    · exact (ZeroPadding.planaric _ _).2 (forest_planaric bs)
  · intro bs cs hb hc p
    simp only [padded, hb, hc] at p
    exact forest_bits (hb.trans hc.symm) ((List.perm_append_right_iff _).mp p)

end Recognition.Enumeration
