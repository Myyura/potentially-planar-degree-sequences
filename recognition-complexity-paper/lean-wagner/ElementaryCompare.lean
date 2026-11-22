import LayoutSearch
import BagArithmetic

/-! Compare a table pattern by first finding a narrow order and then
counting surjections by variable elimination and inclusion–exclusion. -/
namespace Recognition.ElementaryCompare
open QuotientDP MinorWidth StateIso

abbrev orderSize (t : State n) :=
  (StateIncidence.names t).length+(SparseCompare.blocks (StateIncidence.graph t)).length
abbrev pattern (t : State n) : Colored (orderSize t) := SparseCompare.graph (StateIncidence.graph t)

def allowed (budget w : Nat) (t : State n) : Bool :=
  decide (orderSize t≤budget) && (LayoutSearch.ordered (pattern t) w).isSome

theorem allowed_of_hierarchy (budget w : Nat) (t : State n) (size : orderSize t≤budget)
    (D : Hierarchy (pattern t) w) : allowed budget w t=true := by
  simp [allowed,size,LayoutSearch.ordered_complete D]

def reindex (A : Colored k) (xs : List (Fin k)) : Colored k :=
  ⟨fun i => A.color (LayoutSearch.index xs i),
    fun i j => A.edge (LayoutSearch.index xs i) (LayoutSearch.index xs j)⟩

theorem narrow_of_order {A : Colored k} (hit : LayoutSearch.ordered A w=some xs) :
    ∃ p : Equiv.Perm (Fin k), reindex A xs=relabel A p ∧ LayoutSearch.Narrow A w p := by
  obtain ⟨p,h,layout⟩ := LayoutSearch.ordered_sound hit
  exact ⟨p,by simp [reindex,relabel,h],layout⟩

theorem order_layout {A : Colored k} (hit : LayoutSearch.ordered A w=some xs) :
    Nonempty (BagHom.Layout (reindex A xs) w) := by
  obtain ⟨p,eq,h⟩ := narrow_of_order hit
  exact eq ▸ ⟨LayoutSearch.layout A p h⟩

private theorem relabel_iff (A : Colored k) (p : Equiv.Perm (Fin k)) (B : Colored l) :
    StateIso.Iso (relabel A p) B ↔ StateIso.Iso A B := by
  constructor
  · rintro ⟨f,c,e⟩
    exact ⟨p.symm.trans f,fun i => by simpa [relabel] using c (p.symm i),
      fun i j => by simpa [relabel] using e (p.symm i) (p.symm j)⟩
  · rintro ⟨f,c,e⟩
    exact ⟨p.trans f,fun i => c _,fun i j => e _ _⟩

def compareOrder (x t : State n) (xs : List (Fin (orderSize t))) : Bool :=
  decide (orderSize t=orderSize x) && decide (t.remaining=x.remaining ∧ t.used=x.used ∧ t.faces=x.faces) &&
    BagHom.compare (reindex (pattern t) xs) (pattern x) (List.finRange _)

theorem compareOrder_correct (x t : State n) {xs : List (Fin (orderSize t))} (hit : LayoutSearch.ordered (pattern t) w=some xs) :
    compareOrder x t xs=true ↔ Same x t := by
  obtain ⟨p,eq,_⟩ := narrow_of_order hit
  have swap : Same t x ↔ Same x t := ⟨equivalence.symm,equivalence.symm⟩
  rw [←swap,StateIncidence.same_iff]
  simp only [compareOrder,Bool.and_eq_true,decide_eq_true_eq,BagHom.compare_correct _ _ (List.Perm.refl _),
    eq,relabel_iff,pattern,SparseCompare.graph_iff,and_assoc]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨f,_,_⟩ := (SparseCompare.graph_iff _ _).mpr h.2.2.2
    exact ⟨by simpa using Fintype.card_congr f,h⟩

/-- On every retained key the first branch is used. The reference
fallback extends the comparator to arbitrary states outside the table. -/
def compareWith (w : Nat) (x t : State n) :=
  match LayoutSearch.ordered (pattern t) w with
  | some xs => compareOrder x t xs
  | none => StateIncidence.compare x t

theorem compareWith_correct (w : Nat) (x t : State n) : compareWith w x t=true ↔ Same x t := by
  unfold compareWith
  split
  next xs hit => exact compareOrder_correct x t hit
  next => exact StateIncidence.compare_iff x t

theorem allowed_branch (x t : State n) (valid : allowed K w t=true) :
    ∃ xs,LayoutSearch.ordered (pattern t) w=some xs ∧ compareWith w x t=compareOrder x t xs := by
  simp only [allowed,Bool.and_eq_true,decide_eq_true_eq] at valid
  obtain ⟨xs,hit⟩ := Option.isSome_iff_exists.mp valid.2
  exact ⟨xs,hit,by simp [compareWith,hit]⟩

end Recognition.ElementaryCompare
