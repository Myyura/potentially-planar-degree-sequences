import SparseInterior
import SparseBoundary.FanUniversal
import SparseBoundary.LargeAssembly
import SparseBoundary.FanLargePositive
import SparseBoundary.ZeroBoundary
import SparseBoundary.ZeroPadding

namespace SparseBoundary
open ErdosGallai

/-- The positive-budget upper construction and the two zero-budget equalities
suffice for the entire large-core range. -/
theorem large_of_upper_zero
    (upper : ∀h t, 8≤List.length h → 1≤t → Fan.Three.Input h t →
      Planaric (List.replicate t 2++h))
    (zero : ∀h j, Core h → 8≤List.length h → j≤1 → Graphic h →
      h.sum+2*j=4*h.length → Planaric h) : LargeExact := by
  intro h t j core size hj hg vol
  by_cases tn : t=0
  · subst t; simp [profile] at hg vol ⊢; exact zero h j core size hj hg vol
  have cap (x) (hx : x∈h) : x+1≤h.length+t := by
    have b := graphic_degree_lt hg x (List.mem_append_left _ hx)
    simp [profile] at b; omega
  have volume : h.sum+2*j=4*h.length+2*t := by simp [profile] at vol; omega
  have uj (L : List Nat) (s : Nat) (core' : Core L) (sz : 8≤L.length) (svol : L.sum=4*L.length+2*s)
      (cap' : ∀x∈L,x+1≤L.length+s) (gr : Graphic (profile L s 0)) : Planaric (profile L s 0) := by
    by_cases empt : s=0
    · subst s; simp [profile] at svol gr ⊢; exact zero L 0 core' sz (by decide) gr (by simpa using svol)
    · simpa [profile] using (planaric_perm List.perm_append_comm).mp
        (upper L s sz (by omega) ⟨core',svol,cap'⟩)
  by_cases j0 : j=0
  · exact uj h t core size (by omega) cap hg
  have j1 : j=1 := by omega
  match h with
  | [] | [_] => simp at size
  | a::b::u =>
    have max := cap a (by simp)
    by_cases hub : a=(b::u).length+t
    · have sol := Fan.Universal.boundary (j:=1) (b::u) (by simp at size ⊢; omega)
          core.1.of_cons (fun v hv=>core.2 v (List.mem_cons_of_mem _ hv)) (by decide) hub
          (by simp only [List.length_cons,List.sum_cons] at volume ⊢; omega)
      simpa [profile] using (planaric_perm List.perm_append_comm).mp sol
    let s := t-1
    have max' : a≤u.length+s+1 := by simp at hub max; dsimp [s]; omega
    have sv : (a::b::u).sum=4*(a::b::u).length+2*s := by simp only [s,List.length_cons,List.sum_cons] at volume ⊢; omega
    have gr := sparse_graphic (t:=s) u (by simp at size; omega) core.1 core.2
      (by simp at sv ⊢; omega) (by omega) max'
    have pl := uj (a::b::u) s core size sv (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl|hx
      · simp; omega
      · have := List.rel_of_pairwise_cons core.1 hx; simp; omega)
      (by simpa [profile,withTwos] using gr)
    simp only [profile,List.replicate_zero,List.append_nil] at pl ⊢
    exact pad_twos pl ⟨a,by simp,by have := core.2 a (by simp); omega⟩ (by dsimp [s]; omega)

private theorem zero_few_complete : ZeroFew := by
  intro h j core size hj vol cap few
  apply ZeroCore.few j hj h size core vol cap few
  intro no
  have low (x) (hx : x∈h) : 4≤x := by
    have := core.2 x hx
    have ne : x≠3 := by rintro rfl; have := List.count_pos_iff.mpr hx; omega
    omega
  have lower (r : List Nat) (min : ∀v∈r,4≤v) : 4*r.length≤r.sum := by
    induction r with
    | nil => simp
    | cons x r ih =>
      have := min x (by simp)
      have := ih (fun y hy => min y (by simp [hy]))
      simp; omega
  have floor := lower h low
  have v : h.sum=4*h.length := by omega
  exact FourCore.small_budget_min_four size (by decide : 0≤1)
    ⟨core.1,low,by simpa using v,by simpa using cap⟩

/-- All ordinary graphic profiles at either exact leaf-free boundary
with at least eight high vertices have planar realizations. -/
theorem large_exact_verified : LargeExact := by
  have upper : UpperPositive := fun _ _ size pos input => Fan.Three.upper_positive size pos input
  refine large_of_upper_zero upper ?_
  intro h j core size hj hg vol
  apply zero_from_positive upper zero_few_complete h j core size hj vol
  intro x hx
  exact graphic_degree_lt hg x hx

/-- Theorem 1, with no residual numerical or graph-theoretic hypotheses. -/
theorem first_boundary : FirstBoundaryStatement := lower_from_large large_exact_verified

/-- Theorem 2, with no residual numerical or graph-theoretic hypotheses. -/
theorem second_boundary : SecondBoundaryStatement := upper_from_large large_exact_verified

/-- The upper classification in terms of the unordered input alone. -/
theorem second_boundary_invariant (d : List Nat) (ne : d≠[])
    (positive : ∀x∈d,1≤x) (hg : Graphic d) (vol : d.sum+2*d.count 1=4*d.length) :
    ¬Planaric d ↔ Exceptional d := by
  obtain ⟨h,t,core,pm⟩ := normalize_positive d positive
  exact (second_boundary d h t (d.count 1) ne core pm hg vol).trans (exceptional_profile core pm).symm

/-- The same lower theorem for arbitrary isolated vertices; the threshold
uses the number of positive entries and the exception is read after deletion. -/
theorem first_with_isolates (d : List Nat) (hg : Graphic d) :
    let p := d.filter (· != 0)
    p.sum+2+2*p.count 1≤4*p.length → (Planaric d ↔ ¬p.Perm lowerException) := by
  intro p bound
  have ne : p≠[] := by intro e; simp [e] at bound
  have pos (x) (hx : x∈p) : 1≤x := by
    have nz := (List.mem_filter.mp hx).2
    simp at nz
    omega
  have eq := ZeroPadding.filter_positive d
  exact eq.2.trans (first_boundary p ne pos (eq.1.mp hg) bound)

/-- The upper theorem after deletion of arbitrary isolated vertices. -/
theorem second_with_isolates (d : List Nat) (hg : Graphic d) :
    let p := d.filter (· != 0)
    p.sum+2*p.count 1=4*p.length → (¬Planaric d ↔ Exceptional p) := by
  intro p bound
  by_cases empty : p=[]
  · have eq := ZeroPadding.filter_positive d
    change (Graphic d ↔ Graphic p) ∧ (Planaric d ↔ Planaric p) at eq
    rw [empty] at eq ⊢
    have planar := eq.2.mpr (planaric_of_small_core (eq.1.mp hg) (by decide) (by decide))
    have no : ¬Exceptional [] := by
      have c : Core [] := by simp [Core]
      have pm : ([] : List Nat).Perm (profile [] 0 0) := by simp [profile]
      rw [exceptional_profile c pm]
      simp [UpperForbidden,profile]
    exact ⟨fun n => (n planar).elim,fun e => (no e).elim⟩
  have pos (x) (hx : x∈p) : 1≤x := by
    have nz := (List.mem_filter.mp hx).2
    simp at nz
    omega
  have eq := ZeroPadding.filter_positive d
  exact eq.2.not.trans (second_boundary_invariant p empty pos (eq.1.mp hg) bound)

end SparseBoundary
