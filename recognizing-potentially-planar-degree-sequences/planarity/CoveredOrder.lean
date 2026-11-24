import CatalogueRun
import OrderInput

/-! A sphere certificate produces one complete path in the finite catalogue.
The geometric separator assumption concerns this certificate's underlying
uncoloured graph and is invariant under the normalization of edge colors. -/
namespace Recognition.CoveredOrder
open Recognition.QuotientDP Recognition.OrderInput Recognition.Witness Recognition.Outline
open PlanarDegrees.Frontier PlanarDegrees.Topology

private theorem transfer {v f} (C D : ClosedTrace v f)
    (corners : ∀ i, cornerNames (D.faces i)=cornerNames (C.faces i))
    (sides : ∀ i, sideNames (D.faces i)=sideNames (C.faces i))
    (weighted : Separators (List.range (v+1)) (cofacial (List.ofFn C.faces))
      (fun x => cost (simpleDegree C.ledger.sealed x))) :
    Separators (List.range (v+1)) (cofacial (List.ofFn D.faces))
      (fun x => cost (simpleDegree D.ledger.sealed x)) := by
  have dual : cofacial (List.ofFn D.faces) = cofacial (List.ofFn C.faces) := by
    funext x y; apply propext
    have same (T : ClosedTrace v f) : cofacial (List.ofFn T.faces) x y ↔
        ∃i,x∈cornerNames (T.faces i) ∧ y∈cornerNames (T.faces i) := by
      simp only [cofacial,List.mem_ofFn]
      constructor
      · rintro ⟨F,⟨i,rfl⟩,hx,hy⟩; exact ⟨i,hx,hy⟩
      · rintro ⟨i,hx,hy⟩; exact ⟨_,⟨i,rfl⟩,hx,hy⟩
    simp only [same,corners]
  have plain (T : ClosedTrace v f) : (sideTrace T.faces).map Event.edge =
      (List.finRange (f+1)).flatMap (fun i => sideNames (T.faces i)) := by
    simp only [sideTrace,List.map_flatMap]; rfl
  have edgeNames : (sideTrace D.faces).map Event.edge=(sideTrace C.faces).map Event.edge := by
    simp only [plain,sides]
  have equal : D.ledger.sealed.Perm C.ledger.sealed := by
    apply (List.perm_ext_iff_of_nodup (inventory_counts D.accepted).2.1 (inventory_counts C.accepted).2.1).mpr
    intro e; simp only [(replay_accurate D.accepted).sealed,(replay_accurate C.accepted).sealed,occurrences,edgeNames]
  have costEq (x) : simpleDegree D.ledger.sealed x=simpleDegree C.ledger.sealed x := equal.countP_eq _
  simpa only [dual,costEq] using weighted

/-- Every certifying triangulation with the weighted separator property
supplies an accepting path whose every state is represented by the finite
catalogue at the stated cutoff. -/
theorem path (d : Nat) (ds : List Nat) (C : ClosedTrace ds.length f)
    (count : f+1+4=2*(ds.length+1)) (degrees : (witnessDegrees C).Perm (d::ds))
    (weighted : Separators (List.range (ds.length+1)) (cofacial (List.ofFn C.faces))
      (fun x => cost (simpleDegree C.ledger.sealed x))) :
    ∃ s : State (ds.length+1), Table.Path Same (ShortBoundary.catalogue (d::ds))
      (successors (f+1)) (start ((d::ds : List Nat) : Multiset Nat)) (f+1) s ∧ finished (f+1) s := by
  classical
  obtain ⟨D,vc,ec,dc,col,color⟩ := repainted_trace C (Equiv.refl _)
  obtain ⟨seq,perm,covered⟩ := CatalogueRun.catalogued_histories d ds D count (transfer C D vc ec weighted)
  obtain ⟨fs,U,s,rows,run,done⟩ := literal_run D count col color seq.reverse ((List.reverse_perm _).trans perm)
  have target : (witnessDegrees D : Multiset Nat)=((d::ds : List Nat) : Multiset Nat) := Multiset.coe_eq_coe.mpr (dc ▸ degrees)
  rw [target] at run
  have actual := cover_path _ run (covered fs rows)
  have len : fs.length=f+1 := by
    have a := congrArg List.length rows
    have b := perm.length_eq
    simp only [List.length_reverse,List.length_map,List.length_ofFn] at a b
    omega
  exact ⟨prune s,len ▸ actual,done⟩

#print axioms path
end Recognition.CoveredOrder
