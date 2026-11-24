import Combined.FixedBudget
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Distinct incident faces for old labels and a labelled matching in the third fill. -/
namespace Combined.FixedForward
open Recognition Recognition.Rigidity Recognition.Layers Recognition.Stacking SparseBoundary

private def faceStar {V : Type} (M : Map V) {x a b : V} (f : M.face x a b) :
    Star M (fun _ => True) := ⟨corners x a b, ⟨x,a,b,f,rfl⟩, trivial⟩

private theorem three_faces {V : Type} (M : Map V) (x : V) :
    ∃ s t u : Star M (fun _ => True), s ≠ t ∧ s ≠ u ∧ t ≠ u ∧ s.val x ∧ t.val x ∧ u.val x := by
  obtain ⟨a,b,f⟩ := M.incident x
  obtain ⟨c,hcb,g,_⟩ := M.twoSides f
  obtain ⟨w,hwa,h,_⟩ := M.twoSides (M.flip (M.rot (M.rot f)))
  have hxa := M.distinct f
  have hab := M.distinct (M.rot f)
  have hbx := M.distinct (M.rot (M.rot f))
  have separate {i j : Star M (fun _ => True)} (v : V) (yes : i.val v) (no : ¬ j.val v) : i ≠ j :=
    fun e => no (e ▸ yes)
  refine ⟨faceStar M f, faceStar M g, faceStar M h, separate b ?_ ?_, separate a ?_ ?_,
    Ne.symm (separate b ?_ ?_), Or.inl rfl, Or.inl rfl, Or.inl rfl⟩ <;>
    simp [faceStar, corners, *] <;> grind

/-- Hall's theorem, applied to vertex--face incidence.  Each vertex sees at
least three distinct triangular faces and each face has precisely three corners. -/
theorem incident_matching {V : Type} (M : Map V) (E : Enumeration V) :
    ∃ f : V → Star M (fun _ => True), Function.Injective f ∧ ∀ v, (f v).val v := by
  classical
  let S := Star M (fun _ => True)
  let F := starEnumeration M (fun _ => True) E
  let : Fintype V := Fintype.ofList E.vertices E.complete
  let : Fintype S := Fintype.ofList F.vertices F.complete
  let t (x : V) := Finset.univ.filter (fun z : S => z.val x)
  have hall (s : Finset V) : s.card ≤ (s.biUnion t).card := by
    let J := s.biUnion t
    let rel (x : V) (z : S) := z.val x
    have lo (x : V) (hx : x ∈ s) : 3 ≤ (J.bipartiteAbove rel x).card := by
      obtain ⟨a,b,c,hab,hac,hbc,ha,hb,hc⟩ := three_faces M x
      have get (z : S) (h : z.val x) : z ∈ J.bipartiteAbove rel x := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩,h⟩
      have sub : ({a,b,c} : Finset S) ⊆ J.bipartiteAbove rel x := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact get _ ha
        · exact get _ hb
        · exact get _ hc
      simpa [hab,hac,hbc] using Finset.card_le_card sub
    have hi (z : S) (_ : z ∈ J) : (s.bipartiteBelow rel z).card ≤ 3 := by
      obtain ⟨a,b,c,f,he⟩ := z.property.1
      have sub : s.bipartiteBelow rel z ⊆ {a,b,c} := by
        intro x hx
        have mem : z.val x := (Finset.mem_filter.mp hx).2
        simpa [he,corners] using mem
      have hab := M.distinct f
      have hbc := M.distinct (M.rot f)
      have hac := Ne.symm (M.distinct (M.rot (M.rot f)))
      simpa [hab,hac,hbc] using Finset.card_le_card sub
    have count := Finset.card_mul_le_card_mul rel lo hi
    change s.card*3 ≤ (s.biUnion t).card*3 at count
    omega
  obtain ⟨f,inj,inc⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  exact ⟨f,inj,fun x => (Finset.mem_filter.mp (inc x)).2⟩

private theorem row_eq (T : Reduction.Table) :
    (Reduction.layer T Reduction.full).degrees = FixedBudget.full T.degrees := by
  rw [FixedBudget.full_lift]
  simp [Reduction.layer, Reduction.selectedLabels, Reduction.full, StellationResult.lift]

private theorem labels (T : Reduction.Table) : (Reduction.selectedLabels T Reduction.full).Nodup ∧
    ∀ v ∈ Reduction.selectedLabels T Reduction.full, v < T.degrees.length := by
  simp [Reduction.selectedLabels, Reduction.full]

private theorem first_round {d : List Nat} {r : Nat} (R : Model d) (valid : Reduction.TableValid d)
    (fit : r ≤ d.length) : ∃ N : Model (FixedBudget.full d), ∀ i : Fin r, N.edge i.val (d.length+i.val) := by
  classical
  let T : Reduction.Table := ⟨d,0⟩
  let O := Forward.allFaces (T := T) R
  obtain ⟨f,inj,inc⟩ := incident_matching R.map R.vertices
  have find (i : Fin r) : ∃ x, R.label x = i.val :=
    (R.hits i.val).mp (Nat.lt_of_lt_of_le i.isLt fit)
  let src (i : Fin r) := (find i).choose
  have lab (i : Fin r) : R.label (src i) = i.val := (find i).choose_spec
  let m (i : Fin r) : Star R.map O.fill := f (src i)
  have nd := Forward.ofFn_unique m (fun i j eq => Fin.ext ((lab i).symm.trans
    ((congrArg R.label (inj eq)).trans (lab j))))
  let N := Forward.extend (T := T) R (O := O) (List.ofFn m) nd valid (labels T).1 (labels T).2
  have edge (i : Fin r) : N.edge i.val (d.length+i.val) := by
    refine ⟨.inl (src i), .inr (m i), lab i,
      Forward.extend_names (T := T) R (O := O) m nd valid (labels T).1 (labels T).2 i, ?_⟩
    obtain ⟨z,hz⟩ := (star_neighbors R.map O.fill (m i) (src i)).mpr (inc (src i))
    exact ⟨z,(stack R.map O.fill).flip hz⟩
  change ∃ N : Model (FixedBudget.full T.degrees), ∀ i : Fin r, N.edge i.val (d.length+i.val)
  rw [← row_eq T]
  exact ⟨N,edge⟩

private theorem carry_round {d : List Nat} (R : Model d) (valid : Reduction.TableValid d) :
    ∃ N : Model (FixedBudget.full d), ∀ i j, R.edge i j → N.edge i j := by
  let T : Reduction.Table := ⟨d,0⟩
  let O := Forward.allFaces (T := T) R
  change ∃ N : Model (FixedBudget.full T.degrees), ∀ i j, R.edge i j → N.edge i j
  rw [← row_eq T]
  exact ⟨Forward.extend (T := T) R (O := O) [] (by simp) valid (labels T).1 (labels T).2,
    fun _ _ h => Forward.extend_edges (T := T) R (O := O) [] (by simp) valid (labels T).1 (labels T).2 h⟩

/-- A planar source has a planar realization after three complete rounds in
which original vertex `i` is adjacent to first-generation vertex `n+i`. -/
theorem planar_matching {d : List Nat} {r : Nat} (valid : Reduction.TableValid d)
    (fit : r ≤ d.length) (p : Planaric d) :
    let row := FixedBudget.full (FixedBudget.full (FixedBudget.full d))
    ∃ G : Graph row.length, G.Realizes row ∧ G.Planar ∧
      ∀ x y : Fin row.length, x.val < r → y.val = d.length+x.val → G.adj x y = true := by
  obtain ⟨G,hg,hp⟩ := p
  obtain ⟨R,_⟩ := Wagner.tight_embedding d G valid hg hp
  obtain ⟨S,match₁⟩ := first_round R valid fit
  obtain ⟨U,keep₂⟩ := carry_round S (FixedBudget.full_valid valid)
  obtain ⟨W,keep₃⟩ := carry_round U (FixedBudget.full_valid (FixedBudget.full_valid valid))
  refine ⟨Transfer.graph W,Transfer.graph_realizes W,
    EliminationResult.model_planar W (FixedBudget.full_valid (FixedBudget.full_valid (FixedBudget.full_valid valid))),?_⟩
  intro x y hx hy
  apply (Transfer.same_edges W x y).mp
  rw [hy]
  exact keep₃ _ _ (keep₂ _ _ (match₁ ⟨x.val,hx⟩))

end Combined.FixedForward
