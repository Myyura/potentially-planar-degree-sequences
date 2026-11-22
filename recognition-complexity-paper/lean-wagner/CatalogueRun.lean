import ShortBoundary
import PrefixModel

/-! Connect short encoded state representatives to the *actual* projected
full-history recurrence. Full histories are newest-first, so geometric
prefixes are reversed before the existing state projection is applied. -/
namespace Recognition.CatalogueRun
open PlanarDegrees.Frontier PlanarDegrees.Topology
open Recognition.QuotientDP Recognition.ShortBoundary Recognition.BoundaryState Recognition.Outline

theorem model_of_run {bound target fs U} {t : State n} (run : FullRun bound target fs U t) :
    ∃ s, replay ((fs.map FullDegrees.row).flatMap Face.sides)=some s ∧
      Model (fs.map FullDegrees.row) s (prune t) := by
  obtain ⟨s,h,M⟩ := PrefixModel.correspondence run
  exact ⟨s,by simpa [List.flatMap_map,FullDegrees.rows] using h,⟨M.pending,M.sealed,M.blocks,M.current⟩⟩

/-- The exact `Table.covered` test made by the DP holds at every suffix of
an ordered accepting history. This includes the start and terminal state. -/
theorem catalogued_histories (x : Nat) (ds : List Nat) (C : ClosedTrace ds.length f)
    (terminal : (f+1)+4=2*(ds.length+1)) (weighted :
      Separators (List.range (ds.length+1)) (cofacial (List.ofFn C.faces))
        (fun a => cost (simpleDegree C.ledger.sealed a))) :
    ∃ seq : List Face, seq.Perm (List.ofFn C.faces) ∧
      ∀ fs : List (QuotientDP.Triangle (x::ds).length), fs.map FullDegrees.row=seq.reverse →
      ∀ tail U t, tail.IsSuffix fs → FullRun (f+1) ((x::ds : List Nat) : Multiset Nat) tail U t →
        Table.covered Same (catalogue (x::ds)) (prune t) := by
  obtain ⟨seq,perm,order⟩ := catalogued_permuted C terminal (x::ds) rfl weighted
  refine ⟨seq,perm,?_⟩
  intro fs seqEq tail U t suffix run
  obtain ⟨past,e⟩ := suffix
  have reorder : seq=(tail.map FullDegrees.row).reverse++(past.map FullDegrees.row).reverse := by
    have h := congrArg List.reverse seqEq.symm
    simpa [← e,List.map_append,List.reverse_append] using h
  obtain ⟨s,ok,include_⟩ := order _ _ reorder _ (List.reverse_perm _).symm
  obtain ⟨s',ok',model⟩ := model_of_run run
  rw [ok] at ok'
  obtain rfl := Option.some.inj ok'
  have rem : t.remaining ≤ ((x::ds : List Nat) : Multiset Nat) := by
    rw [← FullDegrees.histogram run]; exact Multiset.le_add_right ..
  have used : t.used ≤ (x::ds).length := by
    rw [(FullDegrees.facts run).used]
    simpa using U.card_le_univ
  have faces : t.faces≤2*(x::ds).length := by
    have total := perm.length_eq
    have len := congrArg List.length reorder
    have hist := (FullDegrees.facts run).faces
    simp only [List.length_ofFn,List.length_map,List.length_reverse,List.length_append,List.length_cons] at *
    omega
  obtain ⟨d,mem,iso⟩ := include_ (prune t) model rem used faces
  exact ⟨d,mem,equivalence.symm iso⟩

#print axioms catalogued_histories
end Recognition.CatalogueRun
