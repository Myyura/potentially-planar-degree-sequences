import SparseBoundary.TruncationData

namespace SparseBoundary.Truncation
open Graph

private theorem local_image {G : Graph n} {H : Graph m} (f : Fin n → Fin m)
    (s : List (Fin n))
    (hom : ∀ x∈s, ∀ y∈s, G.adj x y = true → f x = f y ∨ H.adj (f x) (f y) = true) (hc : G.connected s = true) :
    ∃ t, H.connected t = true ∧ ∀ z, z ∈ t ↔ z ∈ s.map f := by
  match s with
  | [] => simp [connected] at hc
  | [x] => exact ⟨[f x],rfl,fun _ => Iff.rfl⟩
  | x::y::ys =>
    obtain ⟨ha,ht⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨w,hw,he⟩ := List.any_eq_true.mp ha
    obtain ⟨t,hcon,hm⟩ := local_image f (y::ys) (fun u hu v hv =>
      hom u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv)) ht
    have hw' := (hm (f w)).mpr (List.mem_map.mpr ⟨w,hw,rfl⟩)
    by_cases hx : f x ∈ t
    · refine ⟨t,hcon,?_⟩
      intro z
      simp only [List.map_cons, List.mem_cons]
      constructor
      · intro hz; exact Or.inr (by simpa using (hm z).mp hz)
      · rintro (rfl|hz)
        · exact hx
        · exact (hm z).mpr (by simpa using hz)
    · rcases hom x (by simp) w (List.mem_cons_of_mem _ hw) he with h|h
      · exact (hx (h ▸ hw')).elim
      · refine ⟨f x :: t,?_,?_⟩
        · cases t with
          | nil => simp at hw'
          | cons u us =>
            exact Bool.and_eq_true_iff.mpr ⟨List.any_eq_true.mpr ⟨f w,hw',h⟩,hcon⟩
        · intro z
          rw [List.map_cons,List.mem_cons,List.mem_cons,hm]

def project {H : Graph (n+1)} {G : Graph (3+n)} (S : Shape H G) (c : Fin (k+1)) (i : Fin k) :
    Fin (3+n) → Fin (n+1) :=
  Fin.addCases (fun s => if i.val=c.val then 0 else (S.port s).succ) Fin.succ

theorem zero_owner {H : Graph (n+1)} {G : Graph (3+n)} (S : Shape H G) (c : Fin (k+1))
    (i : Fin k) (x : Fin (3+n)) : project S c i x=0 → i.val=c.val := by
  refine Fin.addCases (fun s => ?_) (fun u => ?_) x
  · simp only [project,Fin.addCases_left]; split <;> simp_all [Fin.succ_ne_zero]
  · simp [project,Fin.succ_ne_zero]

structure ImageModel {H : Graph (n+1)} {G : Graph (3+n)}
    (S : Shape H G) (b : Fin k → List (Fin (3+n))) (U : Fin k → Fin k → Bool) (c : Fin (k+1)) where
  bags : Fin k → List (Fin (n+1))
  valid : Model H U bags
  image : ∀ i z, z∈bags i ↔ ∃ x∈b i, project S c i x=z

theorem make_image {H : Graph (n+1)} {G : Graph (3+n)} (S : Shape H G)
    {b : Fin k → List (Fin (3+n))} {R : Fin k → Fin k → Bool} (M : Model G R b)
    (U : Fin k → Fin k → Bool) (le : ∀ i j, U i j=true → R i j=true)
    (irr : ∀ i, U i i=false) (c : Fin (k+1))
    (center : Centered U (roles b) (anchors S b) c) : Nonempty (ImageModel S b U c) := by
  classical
  have atSite (i : Fin k) (s : Fin 3) (hi : s.castAdd n∈b i) (nc : i.val≠c.val) :
      Fin.natAdd 3 (S.port s) ∈ b i ∧ ∀ t : Fin 3, t.castAdd n∈b i → t=s := by
    obtain ⟨anc,uni⟩ := center.1 s i ((roles_hit M s i).mpr hi) nc
    exact ⟨(of_decide_eq_true anc) i hi,fun t ht => uni t ((roles_hit M t i).mpr ht)⟩
  have original (i : Fin k) (u : Fin n) (x : Fin (3+n)) :
      x∈b i → project S c i x=u.succ → Fin.natAdd 3 u∈b i := by
    refine Fin.addCases (fun s hs he => ?_) (fun v hv he => ?_) x
    · by_cases eq : i.val=c.val
      · simp [project,eq,Ne.symm (Fin.succ_ne_zero _)] at he
      · have e : S.port s=u := by simpa [project,eq] using he
        exact e ▸ (atSite i s hs eq).1
    · have e : v=u := by simpa [project] using he
      exact e ▸ hv
  have separate (i j : Fin k) (ne : i≠j) (x) (hx : x∈b i) (y) (hy : y∈b j)
      (eq : project S c i x=project S c j y) : False := by
    let z := project S c i x
    have test : ∀ w : Fin (n+1), project S c i x=w → project S c j y=w → False := fun w =>
      Fin.cases (fun hi hj => ne (Fin.ext ((zero_owner S c i x hi).trans (zero_owner S c j y hj).symm)))
        (fun u hi hj => M.sep i j ne _ (original i u x hx hi) (original j u y hy hj)) w
    exact test z rfl eq.symm
  have weak (i j : Fin k) (req : i=j ∨ U i j=true) (x y : Fin (3+n)) :
      x∈b i → y∈b j → G.adj x y=true →
      project S c i x=project S c j y ∨ H.adj (project S c i x) (project S c j y)=true := by
    refine Fin.addCases (fun s => ?_) (fun u => ?_) x <;>
      refine Fin.addCases (fun t => ?_) (fun v => ?_) y
    · intro hs ht _
      simp only [project,Fin.addCases_left]
      by_cases ci : i.val=c.val <;> by_cases cj : j.val=c.val <;> simp [ci,cj,S.spoke,H.adj_comm (S.port s).succ 0]
      rcases req with rfl|e
      · have eq := (atSite i s hs ci).2 t ht
        exact Or.inl (congrArg S.port eq.symm)
      · have h := center.2 s t i j ((roles_hit M s i).mpr hs) ((roles_hit M t j).mpr ht) e
        exact (h.elim ci cj).elim
    · intro _ _ he
      have q := S.exit s v he
      subst v
      by_cases ci : i.val=c.val <;> simp [project,ci,S.spoke]
    · intro _ _ he
      have q := S.exit t u ((G.adj_comm _ _).trans he)
      subst u
      by_cases cj : j.val=c.val <;> simp [project,cj,S.spoke,H.adj_comm (S.port t).succ 0]
    · intro _ _ he; right; simpa only [project,Fin.addCases_right] using S.outer u v he
  have lift (i) := local_image (project S c i) (b i)
    (fun x hx y hy => weak i i (.inl rfl) x y hx hy) (M.con i)
  let target i := Classical.choose (lift i)
  have props i := Classical.choose_spec (lift i)
  have pre (i : Fin k) (z : Fin (n+1)) : z∈target i ↔ ∃ x∈b i,project S c i x=z := by
    simpa only [target,List.mem_map] using (props i).2 z
  refine ⟨⟨target,⟨fun i => (props i).1,?_,?_⟩,pre⟩⟩
  · intro i j ne z hi hj
    obtain ⟨x,hx,eqx⟩ := (pre i z).mp hi
    obtain ⟨y,hy,eqy⟩ := (pre j z).mp hj
    exact separate i j ne x hx y hy (eqx.trans eqy.symm)
  · intro i j e
    obtain ⟨x,hx,y,hy,he⟩ := M.link i j (le i j e)
    have ne : i≠j := by rintro rfl; simp [irr] at e
    refine ⟨_,(pre i _).mpr ⟨x,hx,rfl⟩,_,(pre j _).mpr ⟨y,hy,rfl⟩,?_⟩
    exact (weak i j (.inr e) x y hx hy he).resolve_left (separate i j ne x hx y hy)

end SparseBoundary.Truncation
