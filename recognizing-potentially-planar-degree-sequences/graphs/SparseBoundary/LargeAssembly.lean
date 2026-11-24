import SparseBoundary.ZeroMany
import SparseBoundary.FanThreeReduction
import SparseBoundary.FiveSparse

namespace SparseBoundary
open Fan.Three

/-- Uniform construction for the upper equality when a two is present. -/
def UpperPositive : Prop := ∀h t, 8≤List.length h → 1≤t → Input h t →
    Planaric (List.replicate t 2++h)

/-- The remaining zero-budget profiles with at most two cubic vertices. -/
def ZeroFew : Prop := ∀ h j, Core h → 8≤List.length h → j≤1 →
    h.sum+2*j=4*h.length → (∀ x∈h, x+1≤h.length) → h.count 3≤2 → Planaric h

/-- Both zero-budget equalities. Only the positive upper boundary is needed:
a lower one-subdivision residual is either universal or obtained by
subdividing a zero-budget realization on the upper boundary. -/
theorem zero_from_positive (upper : UpperPositive) (few : ZeroFew)
    (h : List Nat) (j : Nat) (core : Core h) (size : 8≤h.length) (hj : j≤1)
    (vol : h.sum+2*j=4*h.length) (cap : ∀x∈h,x+1≤h.length) : Planaric h := by
  have top (r : List Nat) (rc : Core r) (big : 8≤r.length) (v : r.sum=4*r.length)
      (c : ∀ x∈r,x+1≤r.length) : Planaric r := by
    by_cases small : r.count 3≤2
    · exact few r 0 rc big (by decide) (by simpa using v) c small
    apply ZeroCore.many 0 (by decide) r big rc (by simpa using v) c (by omega)
    intro rs sz _ cs sv cx
    exact upper rs 1 sz (by decide) ⟨cs,by simpa using sv,by
      intro x hx; have := cx x hx; omega⟩
  by_cases upperLayer : j=0
  · exact top h core size (by omega) cap
  have lower : j=1 := by omega
  by_cases small : h.count 3≤2
  · exact few h j core size hj vol cap small
  apply ZeroCore.many j hj h size core vol cap (by omega)
  intro rs sz _ cs sv cx
  match rs with
  | [] => simp at sz
  | a::u =>
    have m := cx a (by simp)
    by_cases univ : a=(a::u).length
    · exact Fan.Universal.boundary (j:=1) (t:=1) u (by simp at sz; omega)
         cs.1.of_cons (fun x hx=>cs.2 x (List.mem_cons_of_mem _ hx)) (by decide)
         (by simpa using univ) (by simp only [List.sum_cons,List.length_cons] at sv ⊢; omega)
    have p := top (a::u) cs sz (by omega) (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl|hx
      · omega
      · have := List.rel_of_pairwise_cons cs.1 hx; omega)
    exact planaric_add_two p ⟨a,by simp,by have := cs.2 a (by simp); omega⟩

end SparseBoundary
