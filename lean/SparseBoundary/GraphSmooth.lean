import SparseBoundary.GraphSeries

namespace SparseBoundary.Graph

private theorem add_connected {G : Graph n} {l : List (Fin n)} (h : G.connected l=true)
    (v w : Fin n) (hw : w∈l) (e : G.adj v w=true) : G.connected (v::l)=true := by
  cases l with
  | nil => simp at hw
  | cons x xs => exact Bool.and_eq_true_iff.mpr ⟨List.any_eq_true.mpr ⟨w,hw,e⟩,h⟩

/-- For edge contraction at a newly labelled vertex, the inverse images of
    all surviving vertices are singletons except for the two endpoints of
    the contracted edge. -/
private def fiber (a i : Fin n) (v : Fin (n+1)) : Prop := v=i.succ ∨ (i=a ∧ v=0)

private theorem connected_lift {G : Graph (n+1)} {H : Graph n} {a : Fin n}
    (joined : G.adj 0 a.succ=true)
    (edges : ∀ i j, H.adj i j=true → ∃ u, fiber a i u ∧ ∃ v, fiber a j v ∧ G.adj u v=true)
    (s : List (Fin n)) (hs : H.connected s=true) :
    ∃ t, G.connected t=true ∧ ∀ v, v∈t ↔ ∃ i∈s, fiber a i v := by
  match s with
  | [] => simp [connected] at hs
  | [i] =>
    by_cases eq : i=a
    · subst i
      refine ⟨[0,a.succ],add_connected (by rfl : G.connected [a.succ]=true) _ _ (by simp) joined,?_⟩
      intro v; simp [fiber,or_comm]
    · exact ⟨[i.succ],rfl,fun v => by simp [fiber,eq]⟩
  | i::j::ss =>
    obtain ⟨links,ht⟩ := Bool.and_eq_true_iff.mp hs
    obtain ⟨r,hr,ed⟩ := List.any_eq_true.mp links
    obtain ⟨t,tc,tm⟩ := connected_lift joined edges (j::ss) ht
    obtain ⟨u,fu,v,fv,e⟩ := edges i r ed
    have here := (tm v).mpr ⟨r,hr,fv⟩
    have once := add_connected tc u v here e
    have formula (w : Fin (n+1)) : (∃ l∈i::j::ss, fiber a l w) ↔ fiber a i w ∨ w∈t := by
      constructor
      · rintro ⟨l,hl,hf⟩
        rcases List.mem_cons.mp hl with rfl|hl
        · exact Or.inl hf
        · exact Or.inr ((tm w).mpr ⟨l,hl,hf⟩)
      · rintro (hh|hh)
        · exact ⟨i,by simp,hh⟩
        · obtain ⟨z,hz,fs⟩ := (tm w).mp hh
          exact ⟨z,List.mem_cons_of_mem _ hz,fs⟩
    by_cases eq : i=a
    · subst i
      rcases fu with rfl|⟨_,rfl⟩
      · refine ⟨0::a.succ::t,add_connected once 0 a.succ (by simp) joined,?_⟩
        intro w; rw [formula]; simp [fiber,or_assoc,or_comm,or_left_comm]
      · refine ⟨a.succ::0::t,add_connected once a.succ 0 (by simp) ((G.adj_comm _ _).trans joined),?_⟩
        intro w; rw [formula]; simp [fiber,or_assoc]
    · have ui : u=i.succ := fu.resolve_right (fun e => eq e.1)
      subst u
      refine ⟨i.succ::t,once,?_⟩
      intro w; rw [formula]; simp [fiber,eq]

/-- Contraction preserves planarity, in the useful one-edge form. -/
theorem contract_planar {G : Graph (n+1)} {H : Graph n} (hp : G.Planar) (a : Fin n)
    (joined : G.adj 0 a.succ=true)
    (edges : ∀ i j, H.adj i j=true →
      ∃ u, (u=i.succ ∨ (i=a ∧ u=0)) ∧ ∃ v, (v=j.succ ∨ (j=a ∧ v=0)) ∧ G.adj u v=true) :
    H.Planar := by
  classical
  have pull {k : Nat} {R : Fin k → Fin k → Bool} (s) (hs : H.minorTest R s=true) :
      ∃ t,G.minorTest R t=true := by
    obtain ⟨con,dis,link⟩ := bag_data hs
    have each (i : Fin k) := connected_lift joined edges (s i) (con i)
    let t (i : Fin k) := Classical.choose (each i)
    have spec (i : Fin k) := Classical.choose_spec (each i)
    refine ⟨t,List.all_eq_true.mpr (fun i _ => Bool.and_eq_true_iff.mpr ⟨(spec i).1,?_⟩)⟩
    apply List.all_eq_true.mpr
    intro j _
    apply Bool.and_eq_true_iff.mpr
    constructor
    · by_cases eq : i=j
      · simp [eq]
      · have d : disjoint (t i) (t j)=true := by
          simp only [disjoint,List.all_eq_true,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not]
          intro x hx hj
          obtain ⟨u,hu,fu⟩ := ((spec i).2 _).mp hx
          obtain ⟨v,hv,fv⟩ := ((spec j).2 _).mp hj
          have same : u=v := by rcases fu with e|⟨e,e'⟩ <;> rcases fv with h|⟨h,h'⟩ <;>
                                  simp_all [Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero _)]
          exact dis i j eq _ hu (same ▸ hv)
        simp [d]
    · by_cases req : R i j=true
      · obtain ⟨u,hu,v,hv,e⟩ := link i j req
        obtain ⟨x,fx,y,fy,xy⟩ := edges u v e
        have l : links G (t i) (t j)=true := List.any_eq_true.mpr
          ⟨x,((spec i).2 x).mpr ⟨u,hu,fx⟩,List.any_eq_true.mpr ⟨y,((spec j).2 y).mpr ⟨v,hv,fy⟩,xy⟩⟩
        simp [l]
      · simp [Bool.eq_false_iff.mpr req]
  exact ⟨fun ⟨s,h⟩ => hp.1 (pull s h),fun ⟨s,h⟩ => hp.2 (pull s h)⟩

end SparseBoundary.Graph
