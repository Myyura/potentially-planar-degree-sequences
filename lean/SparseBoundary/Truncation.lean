import SparseBoundary.TruncationProject

namespace SparseBoundary.Truncation
open Graph

private theorem replace_five {H : Graph (n+1)} {G : Graph (3+n)} (S : Shape H G)
    {b : Fin 5 → List (Fin (3+n))} (M : Model G clique5 b)
    (sp : SplitFive (roles b) (anchors S b)) :
    ∃ bags, H.minorTest biclique33 bags=true := by
  classical
  let r := roles b
  let z (s : Fin 3) : Fin 5 := ⟨(r s).val,(sp.1 s).1⟩
  obtain ⟨u,v,uv,out⟩ := sp.2.2
  have on (s : Fin 3) : hit r s (z s) := rfl
  have zin (s t : Fin 3) (h : z s=z t) : s=t :=
    sp.2.1 s t (Fin.ext (congrArg (fun x : Fin 5 => x.val) h))
  have noU (s : Fin 3) : z s ≠ u := fun e => (out s).1 (e ▸ on s)
  have noV (s : Fin 3) : z s ≠ v := fun e => (out s).2 (e ▸ on s)
  let labs : List (Fin 5) := [z 0,z 1,z 2,u,v]
  have zd (i j : Fin 3) (h : i≠j) : z i ≠ z j := fun h' => h (zin _ _ h')
  have nd : labs.Nodup := by
    simp [labs,zd 0 1 (by decide),zd 0 2 (by decide),zd 1 2 (by decide),noU,noV,uv]
  let L (i : Fin 5) := labs[i.val]'(by exact i.isLt)
  have inj (i j : Fin 5) (h : L i=L j) : i=j :=
    Fin.ext (nd.eq_of_getElem_eq i.isLt j.isLt h)
  let mark (i : Fin 5) := decide (∃ t, (r t).val=i.val)
  have tag (s : Fin 3) (i : Fin 5) (h : hit r s i) : mark i=true := decide_eq_true ⟨s,h⟩
  have mu : mark u=false := by apply decide_eq_false; rintro ⟨s,hs⟩; exact (out s).1 hs
  have mv : mark v=false := by apply decide_eq_false; rintro ⟨s,hs⟩; exact (out s).2 hs
  have five : ∀ i : Fin 5, i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by decide
  have marked (i : Fin 5) : mark (L i)=decide (i.val<3) := by
    rcases five i with rfl|rfl|rfl|rfl|rfl
    · exact tag 0 _ (on 0)
    · exact tag 1 _ (on 1)
    · exact tag 2 _ (on 2)
    · exact mu
    · exact mv
  let U (i j : Fin 5) := clique5 i j && (mark i != mark j)
  let c := Fin.last 5
  have center : Centered U (roles b) (anchors S b) c := by
    constructor
    · intro s i hs _
      refine ⟨(sp.1 s).2,fun t ht => ?_⟩
      exact sp.2.1 t s (Fin.ext (ht.trans hs.symm))
    · intro s t i j hs ht req
      simp [U,tag s i hs,tag t j ht] at req
  obtain ⟨P⟩ := make_image S M U (fun _ _ h => (Bool.and_eq_true_iff.mp h).1)
    (fun i => by simp [U,clique5]) c center
  have root_abs (i : Fin 5) : (0 : Fin (n+1)) ∉ P.bags i := by
    intro hh
    obtain ⟨x,_,eq⟩ := (P.image i 0).mp hh
    have ce := zero_owner S c i x eq
    change i.val=5 at ce
    omega
  have port_mem (s : Fin 3) : (S.port s).succ∈P.bags (z s) := by
    apply (P.image _ _).mpr
    refine ⟨s.castAdd n,(roles_hit M s (z s)).mp (on s),?_⟩
    have ne : (z s).val ≠ c.val := by change (z s).val ≠ 5; omega
    simp [project,ne]
  have to_root (i : Fin 5) (hi : i.val<3) : ∃ y∈P.bags (L i),H.adj 0 y=true := by
    rcases five i with rfl|rfl|rfl|rfl|rfl
    · exact ⟨_,port_mem 0,S.spoke 0⟩
    · exact ⟨_,port_mem 1,S.spoke 1⟩
    · exact ⟨_,port_mem 2,S.spoke 2⟩
    · contradiction
    · contradiction
  let B : Fin 6 → List (Fin (n+1)) := Fin.lastCases [0] (fun i => P.bags (L i))
  have bc (i j : Fin 5) (h : biclique33 i.castSucc j.castSucc=true) : U (L i) (L j)=true := by
    have ij : i≠j := by rintro rfl; simp [biclique33] at h
    have neq : L i ≠ L j := fun he => ij (inj _ _ he)
    simpa [U,clique5,neq,marked,biclique33] using h
  have low : ∀ i : Fin 5, biclique33 (Fin.last 5) i.castSucc=true → i.val<3 := by decide
  have low' : ∀ i : Fin 5, biclique33 i.castSucc (Fin.last 5)=true → i.val<3 := by decide
  refine ⟨B,model_iff.mpr ⟨?_,?_,?_⟩⟩
  · exact Fin.lastCases rfl (fun i => by simpa only [B,Fin.lastCases_castSucc] using P.valid.con (L i))
  · intro i j
    refine Fin.lastCases ?_ (fun x => ?_) i <;> refine Fin.lastCases ?_ (fun y => ?_) j <;>
      simp only [B,Fin.lastCases_castSucc,Fin.lastCases_last]
    · exact fun ne => (ne rfl).elim
    · intro _ w hw; change w∈[0] at hw; simp at hw; subst w; exact root_abs (L y)
    · intro _ w hw h0; change w∈[0] at h0; simp at h0; subst w; exact root_abs (L x) hw
    · intro ne; exact P.valid.sep _ _ (fun h => ne (congrArg Fin.castSucc (inj _ _ h)))
  · intro i j
    refine Fin.lastCases ?_ (fun x => ?_) i <;> refine Fin.lastCases ?_ (fun y => ?_) j <;>
      simp only [B,Fin.lastCases_castSucc,Fin.lastCases_last]
    · exact fun h => (by decide : biclique33 (Fin.last 5) (Fin.last 5)≠true) h |>.elim
    · intro h
      obtain ⟨w,hw,edge⟩ := to_root y (low y h)
      exact ⟨0,List.mem_singleton_self 0,w,hw,edge⟩
    · intro h
      obtain ⟨w,hw,edge⟩ := to_root x (low' x h)
      exact ⟨w,hw,0,List.mem_singleton_self 0,(H.adj_comm _ _).trans edge⟩
    · exact fun h => P.valid.link _ _ (bc _ _ h)

/-- Truncating a vertex of degree three to a triangle preserves planarity.
    If three different K₅ bags occupy the triangle, the old graph contains
    a K₃,₃ model with the central vertex as its sixth bag. -/
theorem planar {H : Graph (n+1)} {G : Graph (3+n)} (S : Shape H G) (hp : H.Planar) : G.Planar := by
  constructor
  · rintro ⟨b,test⟩
    have M := model_iff.mp test
    have ad := admissible_of_model S M
    rcases tags_five _ _ ad with ⟨c,center⟩|sp
    · obtain ⟨img⟩ := make_image S M clique5 (fun _ _ h => h) (by decide) c center
      exact hp.1 ⟨img.bags,model_iff.mpr img.valid⟩
    · exact hp.2 (replace_five S M sp)
  · rintro ⟨b,test⟩
    have M := model_iff.mp test
    obtain ⟨c,center⟩ := tags_six _ _ (admissible_of_model S M)
    obtain ⟨img⟩ := make_image S M biclique33 (fun _ _ h => h) (by decide) c center
    exact hp.2 ⟨img.bags,model_iff.mpr img.valid⟩

end SparseBoundary.Truncation
