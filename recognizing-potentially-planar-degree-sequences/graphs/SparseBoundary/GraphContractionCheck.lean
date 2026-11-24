import SparseBoundary.GraphCliqueSum
import SparseBoundary.GraphWeighted

namespace SparseBoundary.Graph

private theorem good_edge {G : Graph n} {R : Fin k → Fin k → Bool} {s}
    (hn : k<n) (neighbors : ∀ x,∃ y,G.adj x y=true) (model : G.minorTest R s=true) :
    ∃ u v,G.adj u v=true ∧ ∀ i j,i≠j → u∈s i → v∉s j := by
  classical
  obtain ⟨connected,disj,_⟩ := bag_data model
  by_cases total : ∀ x,∃ i,x∈s i
  · let label x := Classical.choose (total x)
    have inbag (x : Fin n) : x∈s (label x) := Classical.choose_spec (total x)
    have duplicate : ∃ x y,x≠y ∧ label x=label y := by
      apply Classical.byContradiction
      intro h
      have inj (x y) (hh : label x=label y) : x=y :=
        Classical.byContradiction (fun ne => h ⟨x,y,ne,hh⟩)
      let labels := (List.finRange n).map label
      have nd : labels.Nodup := List.Pairwise.map label (fun a b ne he => ne (inj a b he)) (List.nodup_finRange _)
      have ll := nd.length_le_of_subset (l₂:=List.finRange k) (fun x _ => List.mem_finRange x)
      simp [labels] at ll
      omega
    obtain ⟨x,y,ne,ex⟩ := duplicate
    let i := label x
    have hx : x∈s i := inbag x
    have hy : y∈s i := by change y∈s (label x); rw [ex]; exact inbag y
    have inside : ∃ u∈s i, ∃ v∈s i,G.adj u v=true := by
      apply Classical.byContradiction; intro bad
      have flat := uniform_bag (connected i) (fun z => z=x) (by
        intro u hu v hv ee; exact (bad ⟨u,hu,v,hv,ee⟩).elim)
      exact ne ((flat x hx y hy).mp rfl).symm
    obtain ⟨u,hu,v,hv,e⟩ := inside
    refine ⟨u,v,e,?_⟩
    intro a b ab ua vb
    have eqi : a=i := Classical.byContradiction fun h => disj a i h u ua hu
    subst a
    exact disj i b ab v hv vb
  · obtain ⟨x,hx⟩ := Classical.not_forall.mp total
    obtain ⟨y,edge⟩ := neighbors x
    exact ⟨x,y,edge,fun i _ _ hi _ => hx ⟨i,hi⟩⟩

/-- It suffices to certify all one-edge contractions: every forbidden
    model in a graph with more than six vertices and no isolated vertices
    has an edge whose contraction preserves the model. -/
theorem planar_from_edge_certificates {G : Graph n} (big : 6<n)
    (neighbors : ∀ x,∃ y,G.adj x y=true)
    (step : ∀ u v,G.adj u v=true → ∃ (H : Graph m) (f : Fin n → Fin m), H.Planar ∧
      (∀ x y,G.adj x y=true → f x=f y ∨ H.adj (f x) (f y)=true) ∧
      (∀ x y,f x=f y → x=y ∨ (x=u ∧ y=v) ∨ (x=v ∧ y=u))) :
    G.Planar := by
  have run {k : Nat} {R : Fin k → Fin k → Bool} (lt : k<n) (ir : ∀ i,R i i=false)
      (s) (hs : G.minorTest R s=true) : ∃ H : Graph m,H.Planar ∧ ∃ t,H.minorTest R t=true := by
    obtain ⟨u,v,ed,separate⟩ := good_edge lt neighbors hs
    obtain ⟨H,f,ph,hom,fiber⟩ := step u v ed
    refine ⟨H,ph,transfer_minor ir s hs f hom ?_⟩
    intro i j ij x hx y hy eq
    rcases fiber x y eq with rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact (bag_data hs).2.1 i j ij _ hx hy
    · exact separate i j ij hx hy
    · exact separate j i (Ne.symm ij) hy hx
  constructor
  · rintro ⟨s,hs⟩; obtain ⟨H,h,p⟩ := run (by omega) (by decide) s hs; exact h.1 p
  · rintro ⟨s,hs⟩; obtain ⟨H,h,p⟩ := run (by omega) (by decide) s hs; exact h.2 p

/-- Compact label certificate. Numeral codes assign a four-bit label to
    each source vertex. The verifier checks edges and the one allowed
    collision, independently of how the certificate was found. -/
private def pos (u v : Nat) := pairCount (max u v)+min u v
private def codeMap (m key i : Nat) := ((key >>> (4*i)) % 16) % m

def stepCheck (G : Graph n) (children : Array (Graph (m+1))) (rows : Array (Nat × Nat)) : Bool :=
  (List.finRange n).all fun u =>
    (List.finRange n).any (G.adj u) && (List.finRange n).all fun v =>
    !G.adj u v || (match rows[pos u.val v.val]? with
      | none => false
      | some (idx,code) => match children[idx]? with
        | none => false
        | some H =>
          let f (x : Fin n) : Fin (m+1) := ⟨codeMap (m+1) code x.val,Nat.mod_lt _ (by omega)⟩
          (List.finRange n).all fun x => (List.finRange n).all fun y =>
            (!G.adj x y || f x==f y || H.adj (f x) (f y)) &&
            (f x != f y || x==y || (x==u && y==v) || (x==v && y==u)))

theorem planar_of_step_check {G : Graph n} {children : Array (Graph (m+1))} {rows}
    (big : 6<n) (known : ∀ H∈children,H.Planar) (test : stepCheck G children rows=true) : G.Planar := by
  have checked u := Bool.and_eq_true_iff.mp (List.all_eq_true.mp test u (List.mem_finRange u))
  apply planar_from_edge_certificates (m:=m+1) big
  · intro u; obtain ⟨v,_,e⟩ := List.any_eq_true.mp (checked u).1; exact ⟨v,e⟩
  · intro u v ed
    have entry := List.all_eq_true.mp (checked u).2 v (List.mem_finRange v)
    simp only [ed,Bool.not_true,Bool.false_or] at entry
    cases r : rows[pos u.val v.val]? with
    | none => simp [r] at entry
    | some pair =>
      obtain ⟨idx,code⟩ := pair
      cases ch : children[idx]? with
      | none => simp [r,ch] at entry
      | some H =>
        simp only [r,ch] at entry
        let f (x : Fin n) : Fin (m+1) := ⟨codeMap (m+1) code x.val,Nat.mod_lt _ (by omega)⟩
        have cell (x y) := Bool.and_eq_true_iff.mp
          (List.all_eq_true.mp (List.all_eq_true.mp entry x (List.mem_finRange x)) y (List.mem_finRange y))
        refine ⟨H,f,known H (Array.mem_of_getElem? ch),?_,?_⟩
        · intro x y e
          have c := (cell x y).1
          change (!G.adj x y || f x==f y || H.adj (f x) (f y))=true at c
          simpa [e] using c
        · intro x y same
          have c := (cell x y).2
          change (f x != f y || x==y || (x==u && y==v) || (x==v && y==u))=true at c
          simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at c
          grind

def layerCheck (graphs : Array (Graph n)) (children : Array (Graph (m+1)))
    (certs : Array (Array (Nat × Nat))) : Bool :=
  (List.range graphs.size).all fun i => stepCheck (graphs[i]?.getD ⟨0⟩) children (certs[i]?.getD #[])

theorem planar_layer {graphs : Array (Graph n)} {children : Array (Graph (m+1))}
    {certs : Array (Array (Nat × Nat))} (big : 6<n) (known : ∀ H∈children,H.Planar)
    (check : layerCheck graphs children certs=true) : ∀ G∈graphs,G.Planar := by
  intro G h
  obtain ⟨i,hi,he⟩ := Array.getElem_of_mem h
  have ok := List.all_eq_true.mp check i (List.mem_range.mpr hi)
  rw [← he]
  apply planar_of_step_check big known
  simpa only [Array.getElem?_eq_getElem hi,Option.getD_some] using ok

/-- A graph whose edges embed in a known planar graph is planar. -/
theorem planar_subgraph_map {G : Graph n} {H : Graph m} (hp : H.Planar) (f : Fin n → Fin m)
    (inj : ∀ x y,f x=f y → x=y) (edges : ∀ x y,G.adj x y=true → H.adj (f x) (f y)=true) :
    G.Planar := by
  have pull {k : Nat} {R : Fin k → Fin k → Bool} (ir : ∀ i,R i i=false)
      (s) (hs : G.minorTest R s=true) : ∃ t,H.minorTest R t=true := by
    apply transfer_minor ir s hs f (fun x y e => Or.inr (edges x y e))
    intro i j hn x hx y hy same
    exact (bag_data hs).2.1 i j hn _ hx (inj x y same ▸ hy)
  exact ⟨fun ⟨s,h⟩ => hp.1 (pull (by decide) s h),fun ⟨s,h⟩ => hp.2 (pull (by decide) s h)⟩

end SparseBoundary.Graph
