import SparseBoundary.GraphDeletion

namespace SparseBoundary

private structure Relabel (d e : List Nat) where
  f : Fin e.length → Fin d.length
  inj : ∀ i j, f i = f j → i = j
  onto : ((List.finRange e.length).map f).Perm (List.finRange d.length)
  matchDegree : ∀ i, d[(f i).val] = e[i.val]

private theorem relabel_perm {d e : List Nat} (h : d.Perm e) : Nonempty (Relabel d e) := by
  induction h with
  | nil => exact ⟨⟨id,fun _ _ h => h,.rfl, fun _ => rfl⟩⟩
  | cons x _ ih =>
    obtain ⟨r⟩ := ih
    let f : Fin (_+1) → Fin (_+1) := Fin.cases 0 (fun i => (r.f i).succ)
    refine ⟨⟨f,?_,?_,?_⟩⟩
    · intro i j
      refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;>
        simp [f]
      all_goals first | exact fun he => r.inj _ _ he | (intro he; have hv := congrArg Fin.val he; simp [Fin.val_succ] at hv)
    · simp only [List.length_cons,List.finRange_succ,List.map_cons,List.map_map,f,Fin.cases_zero]
      apply List.Perm.cons
      simpa [Function.comp_def] using r.onto.map Fin.succ
    · exact Fin.cases rfl (fun i => r.matchDegree i)
  | swap x y l =>
    let f : Fin (l.length+2) → Fin (l.length+2) :=
      Fin.cases (Fin.succ 0) (Fin.cases 0 (fun j => j.succ.succ))
    have inv (i) : f (f i) = i := by
      refine Fin.cases rfl (fun j => ?_) i
      exact Fin.cases rfl (fun _ => rfl) j
    refine ⟨⟨f, fun i j h => (inv i).symm.trans ((congrArg f h).trans (inv j)),?_,?_⟩⟩
    · simp only [List.length_cons, List.finRange_succ, List.map_cons,List.map_map,
        f,Fin.cases_zero,Fin.cases_succ,Function.comp_def]
      exact List.Perm.swap .. 
    · exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j)
  | trans _ _ i1 i2 =>
    obtain ⟨r⟩ := i1
    obtain ⟨s⟩ := i2
    refine ⟨⟨r.f ∘ s.f,fun i j e => s.inj i j (r.inj _ _ e),?_,
      fun i => (r.matchDegree _).trans (s.matchDegree i)⟩⟩
    rw [← List.map_map]
    exact (s.onto.map r.f).trans r.onto

private theorem restrict_realizes {d e : List Nat} (r : Relabel d e)
    {G : Graph d.length} (hd : G.Realizes d) : (G.restrict r.f).Realizes e := by
  intro i
  have h := (r.onto.filter (G.adj (r.f i))).length_eq
  rw [List.filter_map, List.length_map] at h
  have hf : (G.restrict r.f).adj i = G.adj (r.f i) ∘ r.f :=
    funext (Graph.restrict_adj G r.f i)
  exact (show (G.restrict r.f).degree i = G.degree (r.f i) from by
    simpa only [Graph.degree, hf] using h).trans ((hd _).trans (r.matchDegree i))

theorem graphic_perm {d e : List Nat} (p : d.Perm e) : Graphic d ↔ Graphic e := by
  have forward {d e : List Nat} (p : d.Perm e) : Graphic d → Graphic e := by
    obtain ⟨r⟩ := relabel_perm p
    rintro ⟨G,hd⟩
    exact ⟨_,restrict_realizes r hd⟩
  exact ⟨forward p,forward p.symm⟩

theorem planaric_perm {d e : List Nat} (p : d.Perm e) : Planaric d ↔ Planaric e := by
  have forward {d e : List Nat} (p : d.Perm e) : Planaric d → Planaric e := by
    obtain ⟨r⟩ := relabel_perm p
    rintro ⟨G,hd,hp⟩
    exact ⟨_,restrict_realizes r hd, Graph.planar_restrict hp _ r.inj⟩
  exact ⟨forward p,forward p.symm⟩

end SparseBoundary
