import AtlasEG
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import SparseBoundary.FanGraphicNecessity
import SparseBoundary.GraphEncoding

open Finset
namespace SparseBoundary.ErdosGallai

private theorem full_sum (d : List Nat) (f : Nat → Nat) :
    ∑ i : Fin d.length, f d[i.val] = (d.map f).sum := by
  rw [← Fin.sum_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

private theorem prefix_sum (d : List Nat) (f : Nat → Nat) {k : Nat} (le : k≤d.length) :
    ∑ i : Fin k, f (d[i.val]'(by omega)) = ((d.take k).map f).sum := by
  rw [← Fin.sum_ofFn]
  congr 1
  apply List.ext_getElem <;> simp [Nat.min_eq_left le]

private theorem increasing_index {k n : Nat} (g : Fin k ↪o Fin n) (i : Fin k) :
    i.val ≤ (g i).val := by
  have aux (z : Nat) (hz : z<k) : z ≤ (g ⟨z,hz⟩).val := by
    induction z with
    | zero => omega
    | succ j ih =>
      have small : j<k := by omega
      have hj := ih small
      have bigger := g.strictMono (show (⟨j,small⟩ : Fin k)<⟨j+1,hz⟩ from by simp [Fin.lt_def])
      change (g ⟨j,small⟩).val < (g ⟨j+1,hz⟩).val at bigger
      omega
  exact aux _ i.isLt

private theorem prefix_dominates (d : List Nat) (ho : d.Pairwise (· ≥ ·))
    (S : Finset (Fin d.length)) (F : Nat → Nat) (mon : Monotone F) :
    ∑ i∈S, F d[i.val] ≤ ((d.take S.card).map F).sum := by
  have cap : S.card ≤ d.length := by simpa using Finset.card_le_univ S
  rw [← prefix_sum d F cap]
  let g := S.orderEmbOfFin rfl
  have sm : ∑ i∈S, F d[i.val] = ∑ i : Fin S.card, F d[(g i).val] := by
    conv => lhs; rw [← S.map_orderEmbOfFin_univ rfl, Finset.sum_map]
    rfl
  rw [sm]
  apply Finset.sum_le_sum
  intro i _
  apply mon
  have le := increasing_index g i
  rcases Nat.eq_or_lt_of_le le with eq|lt
  · simp [eq]
  · exact List.pairwise_iff_getElem.mp ho i.val (g i).val (by omega) (g i).isLt lt

private theorem sum_weights (d : List Nat) (k : Nat) :
    (d.map (fun x => x+min k x)).sum = d.sum + (d.map (min k)).sum := by
  induction d with
  | nil => simp
  | cons x d ih => simp [ih]; omega

/-- A full graph-realizability sufficiency theorem for the project's
    sorted-list Erdős--Gallai criterion. -/
theorem graphic_of_eg {d : List Nat} (sorted : d.Pairwise (· ≥ ·)) (h : EG d) : Graphic d := by
  classical
  let V := Fin d.length
  let deg := fun i : V => d[i.val]
  apply Exists.elim (p := fun G : SimpleGraph V => ∃ _ : DecidableRel G.Adj, ∀ i, G.degree i=deg i)
    (b := Graphic d) ?_ ?_
  · apply (MathlibExt.Combinatorics.SimpleGraph.ErdosGallaiWanted.erdos_gallai deg).mpr
    constructor
    · have even := h.1
      have sm := full_sum d id
      refine ⟨d.sum/2,?_⟩
      change (∑ i : Fin d.length, d[i.val]) = _
      change (∑ i : Fin d.length, d[i.val]) = (d.map id).sum at sm
      rw [List.map_id] at sm
      rw [sm]; omega
    · intro S
      let k := S.card
      have cap : k≤d.length := by simpa [k,V] using Finset.card_le_univ S
      have hg := h.2 k cap
      have hw := prefix_dominates d sorted S (fun x => x+min k x)
        (by intro x y hh; exact Nat.add_le_add hh (min_le_min_left _ hh))
      rw [Finset.sum_add_distrib,sum_weights] at hw
      have hh := Finset.sum_sdiff (Finset.subset_univ S) (f := fun i : V => min k (deg i))
      have ht := full_sum d (min k)
      have split_ : ((d.take k).map (min k)).sum + ((d.drop k).map (min k)).sum =
          (d.map (min k)).sum := by
        rw [← List.sum_append,← List.map_append, List.take_append_drop]
      change ∑ i∈S, d[i.val] ≤ k*(k-1) + ∑ i∈univ \ S, min d[i.val] k
      simp only [Nat.min_comm (b:=k)]
      change (∑ i∈univ \ S, min k d[i.val]) + (∑ i∈S, min k d[i.val]) =
        (∑ i : Fin d.length, min k d[i.val]) at hh
      rw [ht] at hh
      change (∑ i∈S, d[i.val]) + (∑ i∈S, min k d[i.val]) ≤
        (d.take k).sum + ((d.take k).map (min k)).sum at hw
      omega
  · intro H hx
    obtain ⟨inst,real⟩ := hx
    let _ := inst
    let G : Graph d.length := Graph.ofRelation (fun x y => decide (H.Adj x y))
    have adjG (x y : V) : G.adj x y = decide (H.Adj x y) := by
      apply Graph.adj_ofRelation
      · intro i j; apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using H.adj_comm i j
      · intro i; simp
    refine ⟨G, fun i => ?_⟩
    have cnt : ∀ (xs : List V) (P : V → Bool),
        (xs.filter P).length = (xs.map (fun v => if P v then 1 else 0)).sum := by
      intro xs P; induction xs with
      | nil => simp
      | cons x xs ih => cases he : P x <;> simp [he,ih,Nat.add_comm]
    have eqadj : G.adj i = fun j => decide (H.Adj i j) := funext (adjG i)
    rw [Graph.degree,eqadj,cnt,← Fin.sum_univ_def]
    have eq := H.card_neighborFinset_eq_degree i
    change (∑ x : V, if decide (H.Adj i x) = true then 1 else 0) = deg i
    rw [← real i, ← eq]
    simp [SimpleGraph.neighborFinset_def]

/-- The two-cut criterion for at least six core vertices. -/
theorem graphic_boundary_criterion {a b p t j : Nat} (u : List Nat)
    (sort : (a::b::u).Pairwise (· ≥ ·))
    (hp : p=u.length+2) (h6 : 6≤p) (min : ∀ v∈a::b::u,3≤v)
    (sum : (a::b::u).sum+2*j = 4*p+2*t) :
    Graphic (withTwos (a::b::u) t) ↔
      a+1≤p+t ∧ 2*p+2≤u.sum+2*j := by
  have sorted : (withTwos (a::b::u) t).Pairwise (· ≥ ·) := by
    apply List.pairwise_append.mpr
    refine ⟨sort,by simp,?_⟩
    intro x hx y hy
    have := List.eq_of_mem_replicate hy
    have := min x hx
    omega
  exact (Iff.intro eg_of_graphic (graphic_of_eg sorted)).trans (boundary_criterion u hp h6 min sum)

/-- Throughout the sparse region, including the equality layers, the
    second prefix inequality follows from the maximum-degree cap. -/
theorem sparse_graphic {a b t : Nat} (u : List Nat) (size : 6≤u.length+2)
    (sort : (a::b::u).Pairwise (· ≥ ·)) (hm : ∀ v∈a::b::u,3≤v)
    (volume : (a::b::u).sum≤4*(u.length+2)+2*t) (even : (a::b::u).sum%2=0)
    (max : a≤u.length+t+1) : Graphic (withTwos (a::b::u) t) := by
  apply graphic_of_eg
  · apply List.pairwise_append.mpr
    refine ⟨sort,by simp,?_⟩
    intro x hx y hy
    have := List.eq_of_mem_replicate hy; have := hm x hx; omega
  · apply (criterion u size hm volume even).mpr
    have ba : b≤a := List.rel_of_pairwise_cons sort (by simp)
    exact ⟨max,by omega⟩

private theorem five_core_cuts (a b c d e t j : Nat)
    (ab : b ≤ a) (minB : 3 ≤ b) (minC : 3 ≤ c) (minD : 3 ≤ d) (minE : 3 ≤ e)
    (positive : 1 ≤ j) (volume : a+b+c+d+e+2*j=20+2*t)
    (cap : a ≤ t+4) : EG (withTwos [a,b,c,d,e] t) := by
  constructor
  · simp [withTwos]
    omega
  intro k hk
  by_cases small : k < 5
  · have : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl <;> simp [withTwos] <;> omega
  · have five : [a,b,c,d,e].length ≤ k := by simp; omega
    have mul := Nat.mul_le_mul_left k (show 4 ≤ k-1 by omega)
    simp only [withTwos, List.length_append, List.length_replicate] at hk
    simp at hk
    simp only [withTwos, List.take_append, List.drop_append,
      List.take_of_length_le five, List.drop_of_length_le five, List.nil_append,
      List.take_replicate, List.drop_replicate, List.sum_append, List.map_replicate,
      List.sum_replicate_nat]
    simp [Nat.min_eq_right (show 2≤k by omega), Nat.min_eq_left (show k-5≤t by omega)]
    omega

/-- The degree bound and two-term cut characterize the sparse profile also
when the core has five vertices and at least one unit of slack. -/
theorem graphic_sparse_criterion {a b p t j : Nat} (u : List Nat)
    (sort : (a::b::u).Pairwise (· ≥ ·)) (hp : p=u.length+2)
    (size : 5≤p) (slack : 6≤p+j) (minimum : ∀ v∈a::b::u,3≤v)
    (volume : (a::b::u).sum+2*j=4*p+2*t) :
    Graphic (withTwos (a::b::u) t) ↔
      a+1≤p+t ∧ 2*p+2≤u.sum+2*j := by
  by_cases six : 6≤p
  · exact graphic_boundary_criterion u sort hp six minimum volume
  have five : p=5 := by omega
  subst p
  match u with
  | [c,d,e] =>
    have ba : b≤a := List.rel_of_pairwise_cons sort (by simp)
    have lb := minimum b (by simp)
    have lc := minimum c (by simp)
    have ld := minimum d (by simp)
    have le := minimum e (by simp)
    simp at volume ⊢
    constructor
    · intro hg
      have cut := (eg_of_graphic hg).2 1 (by simp [withTwos])
      simp [withTwos] at cut
      omega
    · rintro ⟨cap,_⟩
      apply graphic_of_eg
      · apply List.pairwise_append.mpr
        refine ⟨sort,by simp,?_⟩
        intro x hx y hy
        have := List.eq_of_mem_replicate hy
        have := minimum x hx
        omega
      · exact five_core_cuts a b c d e t j ba lb lc ld le (by omega) (by omega) (by omega)
  | [] | [_] | [_,_] | _::_::_::_::_ => simp at five

/-- On the same profiles the first degree bound alone is sufficient. -/
theorem graphic_sparse_iff_degree_cap {a b p t j : Nat} (u : List Nat)
    (sort : (a::b::u).Pairwise (· ≥ ·)) (hp : p=u.length+2)
    (size : 5≤p) (slack : 6≤p+j) (minimum : ∀ v∈a::b::u,3≤v)
    (volume : (a::b::u).sum+2*j=4*p+2*t) :
    Graphic (withTwos (a::b::u) t) ↔ a+1≤p+t := by
  rw [graphic_sparse_criterion u sort hp size slack minimum volume]
  have ba : b≤a := List.rel_of_pairwise_cons sort (by simp)
  simp only [List.sum_cons] at volume
  exact ⟨And.left, fun cap => ⟨cap, by omega⟩⟩

end SparseBoundary.ErdosGallai
