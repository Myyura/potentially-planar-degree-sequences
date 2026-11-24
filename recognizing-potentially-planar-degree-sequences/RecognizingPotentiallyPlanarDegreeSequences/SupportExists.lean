import RecognizingPotentiallyPlanarDegreeSequences.SupportTrim
import SparseBoundary.BranchDegree

namespace RecognizingPotentiallyPlanarDegreeSequences.Support
open SparseBoundary SparseBoundary.Graph

theorem vsum_even {f : Fin n → Nat} (even : ∀ i, f i%2=0) : vsum f%2=0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [vsum_succ]; have z := even 0; have t := ih (fun i => even i.succ); omega

namespace Multi

private theorem bool_present (x : Nat) : (decide (0<x)).toNat=present x := by
  cases x <;> simp [present]

theorem cons_support_zero (L : Nat) (row : Fin n → Nat) (M : Multi n) :
  (cons L row M).support.degree 0=vsum (fun i => present (row i)) := by
  rw [support,degree_adjoin_zero,←count_true]; simp only [bool_present]

theorem cons_support_succ (L : Nat) (row : Fin n → Nat) (M : Multi n) (i : Fin n) :
  (cons L row M).support.degree i.succ=M.support.degree i+present (row i) := by
  rw [support,degree_adjoin_succ,bool_present]

private theorem present_hit (i x : Fin n) : present (hit i x)=hit i x := by
  by_cases eq : i=x <;> simp [hit,eq,present]

/-- Pair vertices of odd demand. Every other incidence is supplied by a
loop; the simple support has degree 0 or 1 at each vertex. -/
theorem matching_loops (f : Fin n → Nat) (even : vsum f%2=0) :
  ∃ M : Multi n, (∀ i, M.degree i=f i) ∧ (∀ i, M.support.degree i=f i%2) := by
  induction n with
  | zero => exact ⟨.nil,fun i => i.elim0,fun i => i.elim0⟩
  | succ n ih =>
    let tail (i : Fin n) := f i.succ
    have total : f 0+vsum tail=vsum f := (vsum_succ f).symm
    by_cases e : f 0%2=0
    · obtain ⟨R,dr,sr⟩ := ih tail (by omega)
      refine ⟨.cons (f 0/2) (fun _ => 0) R,?_,?_⟩
      · refine Fin.cases ?_ (fun j => ?_)
        · simp [degree]; omega
        · simp [degree,dr,tail]
      · refine Fin.cases ?_ (fun j => ?_)
        · simp [cons_support_zero,e]
        · simp [cons_support_succ,sr,tail]
    · have odd : ∃ x, tail x%2=1 := by
        apply Classical.byContradiction; intro no
        have allEven (x) : tail x%2=0 := by have nx : ¬tail x%2=1 := fun e => no ⟨x,e⟩; omega
        have := vsum_even allEven; omega
      obtain ⟨x,hx⟩ := odd
      let g i := tail i-hit i x
      have row (i) : g i+hit i x=tail i := by
        by_cases eq : i=x <;> simp_all [g,hit] <;> omega
      have sum : vsum g+1=vsum tail := by
        have eq : (fun i => g i+hit i x)=tail := funext row
        have := congrArg vsum eq; simpa [vsum_add] using this
      obtain ⟨R,dr,sr⟩ := ih g (by omega)
      refine ⟨.cons (f 0/2) (fun i => hit i x) R,?_,?_⟩
      · refine Fin.cases ?_ (fun i => ?_)
        · simp [degree]; omega
        · simpa [degree,dr] using row i
      · refine Fin.cases ?_ (fun i => ?_)
        · simp [cons_support_zero,present_hit]; omega
        · simp only [cons_support_succ,sr,present_hit]
          change g i%2+hit i x=tail i%2
          by_cases eq : i=x
          · subst i; simp [g,hit] at *; omega
          · simp [g,hit,eq]

/-- The set of normalized candidates is nonempty under precisely the
parity and total-capacity hypotheses used for the optimization formula. -/
theorem candidate_exists (h : List Nat) (ell : Nat) (enough : ell≤h.sum)
    (even : (h.sum+ell)%2=0) : Nonempty (Candidate h ell) := by
  let f (i : Fin h.length) := h[i]
  have fs : vsum f=h.sum := by
    have hf : List.ofFn f=h := by apply List.ext_getElem <;> simp [f]
    simp [vsum,hf]
  obtain ⟨g,cap,gs⟩ := take_row f (h.sum-ell) (by omega)
  obtain ⟨M,dm,sm⟩ := matching_loops g (by omega)
  have plan : M.support.Planar := by
    apply planar_of_few_high
    have no : (List.finRange h.length).filter (fun i => decide (3≤M.support.degree i))=[] := by
      apply List.filter_eq_nil_iff.mpr; intro i _; simp [sm]; omega
    rw [no]; simp
  refine ⟨⟨M,plan,fun i => (dm i) ▸ cap i,?_⟩⟩
  have hs := M.handshake
  rw [funext dm,gs] at hs; omega

end Multi
end RecognizingPotentiallyPlanarDegreeSequences.Support
