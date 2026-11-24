import SparseBoundary.FanShell

namespace SparseBoundary.Fan.Universal

open Graph

/-- The seven seed graphs realize the five partitions of four excess
degree units, followed by the two partitions of two. The vertex tags
are ordered by degree, and circular positions are given separately. -/
private def seed : Fin 7 → Graph 7
  | 0 => ⟨1082959⟩
  | 1 => ⟨1097823⟩
  | 2 => ⟨1082613⟩
  | 3 => ⟨1097847⟩
  | 4 => ⟨1083189⟩
  | 5 => ⟨1098255⟩
  | _ => ⟨1097845⟩

private def positions : Fin 7 → List (Fin 7)
  | 0 => [0,1,2,3,4,5,6]
  | 1 => [0,2,1,3,4,5,6]
  | 2 => [0,1,2,3,4,5,6]
  | 3 => [0,1,3,2,4,5,6]
  | 4 => [0,1,2,4,3,5,6]
  | 5 => [0,1,2,3,4,5,6]
  | _ => [0,1,2,3,4,5,6]

private def outerFirst : Fin 7 → Fin 7
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | _ => 0

private def outerLast : Fin 7 → Fin 7
  | 0 => 6
  | 1 => 6
  | 2 => 6
  | 3 => 6
  | 4 => 6
  | 5 => 6
  | _ => 6

private def degrees : Fin 7 → List Nat
  | 0 => [7,3,3,3,3,3,3]
  | 1 => [6,4,3,3,3,3,3]
  | 2 => [5,5,3,3,3,3,3]
  | 3 => [5,4,4,3,3,3,3]
  | 4 => [4,4,4,4,3,3,3]
  | 5 => [5,3,3,3,3,3,3]
  | _ => [4,4,3,3,3,3,3]


private def rank (k i : Fin 7) : Fin 7 := (positions k)[i.val]!
private def excess (k : Fin 7) : Nat := if k.val<5 then 4 else 2

private theorem certified (k : Fin 7) : Nonempty (Perimeter (seed k)) := by
  refine ⟨⟨rank k,?_,outerFirst k,outerLast k,?_,?_,?_,?_⟩⟩
  all_goals revert k
  all_goals first | (unfold noncross; decide +kernel) | decide +kernel

private theorem seed_degrees : ∀ k i : Fin 7, (seed k).degree i+1=(degrees k)[i.val]! := by
  decide +kernel

private theorem seed_total : ∀ k : Fin 7, ((List.finRange 7).map (fun i => (seed k).degree i+1)).sum=
    3*7+excess k := by decide +kernel

private theorem seed_for (k : Fin 7) (a b c d e f g : Nat)
    (fit : ∀i : Fin 7, (degrees k)[i.val]!≤([a,b,c,d,e,f,g] : List Nat)[i.val]!) :
    ShellFor [a,b,c,d,e,f,g] (excess k) := by
  refine ⟨seed k,certified k,?_,seed_total k⟩
  intro i
  rw [seed_degrees]
  change (degrees k)[i.val]!≤[a,b,c,d,e,f,g][i.val]'(i.isLt)
  simpa only [getElem!_pos [a,b,c,d,e,f,g] i.val i.isLt] using fit i

private theorem tail_eq_three (xs : List Nat) (hm : ∀i∈xs,3≤i) (mx : ∀i∈xs,i≤3) :
    xs.sum=3*xs.length := by
  have h : xs=List.replicate xs.length 3 := List.eq_replicate_iff.mpr ⟨rfl,fun i hi =>
    Nat.le_antisymm (mx i hi) (hm i hi)⟩
  exact (congrArg List.sum h).trans (by simp [List.sum_replicate_nat,Nat.mul_comm])

private theorem all7 (P : Fin 7 → Prop) (h0 : P 0) (h1 : P 1) (h2 : P 2)
    (h3 : P 3) (h4 : P 4) (h5 : P 5) (h6 : P 6) : ∀ i, P i := by
  intro i
  have h : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by simp only [Fin.ext_iff]; omega
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> assumption

/-- Select a seven-vertex seed under the componentwise capacities
imposed by the sorted degree sequence. -/
private theorem choose_seed (a b c d e f g : Nat) (xs : List Nat) (C : Nat)
    (order : (a::b::c::d::e::f::g::xs).Pairwise (·≥·))
    (low : ∀y∈a::b::c::d::e::f::g::xs,3≤y)
    (typeC : C=4 ∨ C=2)
    (room : 3*(7+xs.length)+C≤(a::b::c::d::e::f::g::xs).sum) :
    ShellFor [a,b,c,d,e,f,g] C := by
  have ab := List.rel_of_pairwise_cons order (by simp : b∈b::c::d::e::f::g::xs)
  have bc := List.rel_of_pairwise_cons order.of_cons (by simp : c∈c::d::e::f::g::xs)
  have cd := List.rel_of_pairwise_cons order.of_cons.of_cons (by simp : d∈d::e::f::g::xs)
  have de := List.rel_of_pairwise_cons order.of_cons.of_cons.of_cons (by simp : e∈e::f::g::xs)
  have ef := List.rel_of_pairwise_cons order.of_cons.of_cons.of_cons.of_cons (by simp : f∈f::g::xs)
  have fg := List.rel_of_pairwise_cons order.of_cons.of_cons.of_cons.of_cons.of_cons (by simp : g∈g::xs)
  have three := low g (by simp)
  have tail : d≤3 → xs.sum=3*xs.length := by
    intro hd
    apply tail_eq_three _ (fun v hv => low v (by simp [hv]))
    intro v hv
    have := List.rel_of_pairwise_cons order.of_cons.of_cons.of_cons.of_cons.of_cons.of_cons hv
    omega
  simp only [List.sum_cons] at room
  have ample : (C=4 ∧ 7≤a) ∨ (C=4 ∧ 6≤a ∧ 4≤b) ∨ (C=4 ∧ 5≤b) ∨
      (C=4 ∧ 5≤a ∧ 4≤c) ∨ (C=4 ∧ 4≤d) ∨ (C=2 ∧ 5≤a) ∨ (C=2 ∧ 4≤b) := by
    by_cases h : d≤3
    · have := tail h; omega
    · omega
  rcases ample with ⟨rfl,h⟩|⟨rfl,h,h'⟩|⟨rfl,h⟩|⟨rfl,h,h'⟩|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩
  · apply seed_for 0 a b c d e f g
    apply all7 <;> first
      | (change 7≤a; omega)
      | (change 3≤b; omega)
      | (change 3≤c; omega)
      | (change 3≤d; omega)
      | (change 3≤e; omega)
      | (change 3≤f; omega)
      | (change 3≤g; omega)
  · apply seed_for 1 a b c d e f g
    apply all7 <;> first
      | (change 6≤a; omega)
      | (change 4≤b; omega)
      | (change 3≤c; omega)
      | (change 3≤d; omega)
      | (change 3≤e; omega)
      | (change 3≤f; omega)
      | (change 3≤g; omega)
  · apply seed_for 2 a b c d e f g
    apply all7 <;> first
      | (change 5≤a; omega)
      | (change 5≤b; omega)
      | (change 3≤c; omega)
      | (change 3≤d; omega)
      | (change 3≤e; omega)
      | (change 3≤f; omega)
      | (change 3≤g; omega)
  · apply seed_for 3 a b c d e f g
    apply all7 <;> first
      | (change 5≤a; omega)
      | (change 4≤b; omega)
      | (change 4≤c; omega)
      | (change 3≤d; omega)
      | (change 3≤e; omega)
      | (change 3≤f; omega)
      | (change 3≤g; omega)
  · apply seed_for 4 a b c d e f g
    apply all7 <;> first
      | (change 4≤a; omega)
      | (change 4≤b; omega)
      | (change 4≤c; omega)
      | (change 4≤d; omega)
      | (change 3≤e; omega)
      | (change 3≤f; omega)
      | (change 3≤g; omega)
  · apply seed_for 5 a b c d e f g
    apply all7 <;> first
      | (change 5≤a; omega)
      | (change 3≤b; omega)
      | (change 3≤c; omega)
      | (change 3≤d; omega)
      | (change 3≤e; omega)
      | (change 3≤f; omega)
      | (change 3≤g; omega)
  · apply seed_for 6 a b c d e f g
    apply all7 <;> first
      | (change 4≤a; omega)
      | (change 4≤b; omega)
      | (change 3≤c; omega)
      | (change 3≤d; omega)
      | (change 3≤e; omega)
      | (change 3≤f; omega)
      | (change 3≤g; omega)

/-- Any sorted rim profile on at least seven vertices, with minimum
three and the required total surplus, extends to a realization with
a universal hub. -/
theorem from_surplus (h : List Nat) (C t : Nat) (hc : C=4 ∨ C=2) (size : 7≤h.length)
    (so : h.Pairwise (·≥·)) (hm : ∀v∈h,3≤v) (vol : h.sum=3*h.length+C+t) :
    Planaric (List.replicate t 2 ++ (h.length+t)::h) := by
  have shape : ∃a b c d e f g xs, h=a::b::c::d::e::f::g::xs := by
    cases h with
    | nil => simp at size
    | cons a h =>
      cases h with
      | nil => simp at size
      | cons b h =>
        cases h with
        | nil => simp at size
        | cons c h =>
          cases h with
          | nil => simp at size
          | cons d h =>
            cases h with
            | nil => simp at size
            | cons e h =>
              cases h with
              | nil => simp at size
              | cons f h =>
                cases h with
                | nil => simp at size
                | cons g xs => exact ⟨a,b,c,d,e,f,g,xs,rfl⟩
  obtain ⟨a,b,c,d,e,f,g,xs,rfl⟩ := shape
  let head := [a,b,c,d,e,f,g]
  have shell := choose_seed a b c d e f g xs C so hm hc
    (by simp only [List.length_cons] at vol; omega)
  have many := shell_append shell xs (fun v m => hm v (by simp [m]))
  have pm : (xs++head).Perm (a::b::c::d::e::f::g::xs) := List.perm_append_comm
  have mlen := pm.length_eq
  have msum := pm.sum_nat
  have full := universal_of_shell (t:=t) many (by change (xs++head).sum=3*(xs++head).length+C+t; omega)
  change Planaric (List.replicate t 2 ++ ((xs++head).length+t)::(xs++head)) at full
  rw [mlen] at full
  exact (planaric_perm ((pm.cons _).append_left _)).mp full

/-- Both boundary layers at a universal maximum, for arbitrary numbers
of core threes. The parameter j is zero on the upper layer. -/
theorem boundary {a t j : Nat} (h : List Nat) (size : 7≤h.length)
    (so : h.Pairwise (·≥·)) (hm : ∀v∈h,3≤v) (hj : j≤1)
    (hub : a=h.length+t) (vol : a+h.sum+2*j=4*(h.length+1)+2*t) :
    Planaric (List.replicate t 2 ++ a::h) := by
  subst a
  exact from_surplus h (4-2*j) t (by omega) size so hm (by omega)

end SparseBoundary.Fan.Universal
