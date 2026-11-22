import Mathlib.Algebra.BigOperators.Fin
import PackedMinor
import Reduction

/-! Degree counts transported between the packed graph and Mathlib's graph. -/
namespace Recognition.Wagner
open SparseBoundary

theorem neighbor_count (G : Graph n) (i : Fin n) :
    Nat.card {u // (toSimple G).Adj i u} = G.degree i := by
  classical
  let l := (List.finRange n).filter (G.adj i)
  have nd : l.Nodup := List.filter_sublist.nodup (List.nodup_finRange n)
  have same : l.toFinset = Finset.univ.filter (fun u => (toSimple G).Adj i u) := by
    ext v
    simp [l,toSimple_adj]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,← same,List.toFinset_card_of_nodup nd]
  rfl

theorem order_counts {d : List Nat} (G : Graph d.length) (valid : Reduction.TableValid d)
    (realizes : G.Realizes d) :
    (∀ v, 3 ≤ Nat.card {u // (toSimple G).Adj v u}) ∧
    Nat.card (toSimple G).edgeSet + 6 = 3*Nat.card (Fin d.length) := by
  classical
  constructor
  · intro v
    rw [neighbor_count,realizes v]
    exact (valid.2.2 _ (List.getElem_mem v.isLt)).1
  · have sum := (toSimple G).sum_degrees_eq_twice_card_edges
    have each (i : Fin d.length) : (toSimple G).degree i = d[i] := by
      rw [← SimpleGraph.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card]
      exact (neighbor_count G i).trans (realizes i)
    simp_rw [each] at sum
    have listSum : (∑ i : Fin d.length, d[i]) = d.sum := by
      rw [← List.sum_ofFn]
      congr 1
      apply List.ext_getElem <;> simp
    rw [listSum] at sum
    have ev := valid.2.1
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_fin]
    omega
end Recognition.Wagner
