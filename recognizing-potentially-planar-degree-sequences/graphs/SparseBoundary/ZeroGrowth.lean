import SparseBoundary.Truncation
import SparseBoundary.GraphSmooth
import SparseBoundary.GraphWeighted
import SparseBoundary.GraphPerm

namespace SparseBoundary.ZeroGrowth
open Graph

/-- An edge contraction with an explicit certificate for each surviving edge. -/
theorem contract {G : Graph (n+1)} {D : Graph n} (hp : G.Planar) (a : Fin n)
    (joined : G.adj 0 a.succ=true)
    (edges : ∀ i j, D.adj i j=true → G.adj i.succ j.succ=true ∨
      (i=a ∧ G.adj 0 j.succ=true) ∨ (j=a ∧ G.adj i.succ 0=true)) : D.Planar := by
  apply contract_planar hp a joined
  intro i j e
  rcases edges i j e with e | ⟨ia,e⟩ | ⟨ja,e⟩
  · exact ⟨_,.inl rfl,_,.inl rfl,e⟩
  · exact ⟨_,.inr ⟨ia,rfl⟩,_,.inl rfl,e⟩
  · exact ⟨_,.inl rfl,_,.inr ⟨ja,rfl⟩,e⟩

theorem profile {G : Graph n} (hp : G.Planar) {d : List Nat}
    (perm : (List.ofFn G.degree).Perm d) : Planaric d :=
  (planaric_perm perm).mp (planaric_profile hp)

end SparseBoundary.ZeroGrowth
