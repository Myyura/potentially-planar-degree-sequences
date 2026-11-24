import SparseBoundary.GraphSeries

namespace SparseBoundary.Graph

set_option maxRecDepth 8192
set_option maxSynthPendingDepth 32

theorem uniform_bag {G : Graph n} {s : List (Fin n)} (hc : G.connected s=true)
    (P : Fin n → Prop) (same : ∀ u∈s, ∀ v∈s, G.adj u v=true → (P u ↔ P v)) :
    ∀ u∈s, ∀ v∈s, P u ↔ P v := by
  match s with
  | [] => simp
  | [a] => simp
  | a::b::l =>
    obtain ⟨links,conn⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨z,hz,edge⟩ := List.any_eq_true.mp links
    have rest := uniform_bag conn P (fun u hu v hv => same u (List.mem_cons_of_mem _ hu)
      v (List.mem_cons_of_mem _ hv))
    have first : P a ↔ P z := same a (by simp) z (List.mem_cons_of_mem _ hz) edge
    intro u hu v hv
    have any (w : Fin n) (hw : w∈a::b::l) : P w ↔ P z := by
      rcases List.mem_cons.mp hw with h|hw
      · exact h ▸ first
      · exact rest w hw z hz
    exact (any u hu).trans (any v hv).symm

/-- After deletion of any two labels, the remaining template has diameter
    at most two, and contains at least three labels. -/
private def Robust (R : Fin k → Fin k → Bool) : Prop :=
  (∀ i : Fin k, ∃ j, j≠i) ∧
  (∀ p q, ∃ i j r : Fin k, i≠p ∧ i≠q ∧ j≠p ∧ j≠q ∧ r≠p ∧ r≠q ∧ i≠j ∧ i≠r ∧ j≠r) ∧
  (∀ i j p q, i≠p → i≠q → j≠p → j≠q → i=j ∨ R i j=true ∨
    ∃ r, r≠p ∧ r≠q ∧ R i r=true ∧ R r j=true)

private def Anchor (a b : Fin n) (x : Fin (n+2)) := x=a.succ.succ ∨ x=b.succ.succ

private theorem each_anchor {G : Graph (n+2)} {a b : Fin n}
    (sep : ∀ x y, x.val<2 → G.adj x y=true → y.val<2 ∨ Anchor a b y)
    {R : Fin k → Fin k → Bool} (rob : Robust R) {s} (hm : G.minorTest R s=true)
    (i : Fin k) (inside : ∃ x∈s i, x.val<2) : ∃ y∈s i, Anchor a b y := by
  classical
  apply Classical.byContradiction
  intro missing
  obtain ⟨connected,disj,links⟩ := bag_data hm
  obtain ⟨alt,ha⟩ := rob.1 i
  have owner (v : Fin n) (out : v.succ.succ∉s i) :
      ∃ p : Fin k, i≠p ∧ ∀ j, j≠p → v.succ.succ∉s j := by
    by_cases h : ∃ j, v.succ.succ∈s j
    · obtain ⟨j,hj⟩ := h
      exact ⟨j,fun e => out (e ▸ hj),fun l hl hv =>
        disj l j hl _ hv hj⟩
    · exact ⟨alt,Ne.symm ha,fun j _ hh => h ⟨j,hh⟩⟩
  obtain ⟨p,ip,pa⟩ := owner a (fun ha => missing ⟨_,ha,Or.inl rfl⟩)
  obtain ⟨q,iq,pb⟩ := owner b (fun hb => missing ⟨_,hb,Or.inr rfl⟩)
  let live (r : Fin k) := ∃ x∈s r, x.val<2
  have avoid (j) (jp : j≠p) (jq : j≠q) (y) (hy : y∈s j) : ¬Anchor a b y := by
    rintro (rfl|rfl)
    · exact pa j jp hy
    · exact pb j jq hy
  have step (u v) (up : u≠p) (uq : u≠q) (vp : v≠p) (vq : v≠q)
      (adjacent : R u v=true) (hu : live u) : live v := by
    obtain ⟨x,hx,hz⟩ := hu
    have uni := uniform_bag (connected u) (fun y => y.val<2) (by
      intro j hj l hl ee
      exact ⟨fun h => (sep j l h ee).resolve_right (avoid u up uq l hl),
        fun h => (sep l j h ((G.adj_comm _ _).trans ee)).resolve_right (avoid u up uq j hj)⟩)
    obtain ⟨j,hj,l,hl,edge⟩ := links u v adjacent
    exact ⟨l,hl,(sep j l ((uni x hx j hj).mp hz) edge).resolve_right (avoid v vp vq l hl)⟩
  have all (j) (jp : j≠p) (jq : j≠q) : live j := by
    rcases rob.2.2 i j p q ip iq jp jq with rfl|edge|⟨l,lp,lq,il,lj⟩
    · exact inside
    · exact step i j ip iq jp jq edge inside
    · exact step l j lp lq jp jq lj (step i l ip iq lp lq il inside)
  obtain ⟨u,v,w,up,uq,vp,vq,wp,wq,uv,uw,vw⟩ := rob.2.1 p q
  obtain ⟨x,hx,smallx⟩ := all u up uq
  obtain ⟨y,hy,smally⟩ := all v vp vq
  obtain ⟨z,hz,smallz⟩ := all w wp wq
  have nexy : x≠y := fun he => disj u v uv _ hx (he ▸ hy)
  have nexz : x≠z := fun he => disj u w uw _ hx (he ▸ hz)
  have neyz : y≠z := fun he => disj v w vw _ hy (he ▸ hz)
  have xy : x.val≠y.val := fun h => nexy (Fin.ext h)
  have xz : x.val≠z.val := fun h => nexz (Fin.ext h)
  have yz : y.val≠z.val := fun h => neyz (Fin.ext h)
  omega

private theorem projection {G : Graph (n+2)} {a b : Fin n}
    (sep : ∀ x y, x.val<2 → G.adj x y=true → y.val<2 ∨ Anchor a b y)
    {R : Fin k → Fin k → Bool} (rob : Robust R) {s} (hm : G.minorTest R s=true)
    (x : Fin (n+2)) (hx : x.val<2) :
    ∃ z : Fin n, (z=a ∨ z=b) ∧ ∀ i, x∈s i → z.succ.succ∈s i := by
  classical
  by_cases found : ∃ i, x∈s i
  · obtain ⟨i,hi⟩ := found
    have atAny (v : Fin n) (hv : v.succ.succ∈s i) : ∀ j, x∈s j → v.succ.succ∈s j := by
      intro j hj
      by_cases e : i=j
      · exact e ▸ hv
      · exact False.elim ((bag_data hm).2.1 i j e x hi hj)
    obtain ⟨y,hy,rfl|rfl⟩ := each_anchor sep rob hm i ⟨x,hi,hx⟩
    · exact ⟨a,Or.inl rfl,atAny a hy⟩
    · exact ⟨b,Or.inr rfl,atAny b hy⟩
  · exact ⟨a,Or.inl rfl,fun i hi => False.elim (found ⟨i,hi⟩)⟩

/-- Gluing a subgraph of K₄ along a pre-existing edge preserves planarity.
    The two new vertices may attach to one another and to the two ends of
    that edge. Any original edges may also be deleted. -/
theorem clique_sum_edge {H : Graph n} {G : Graph (n+2)} (hp : H.Planar) (a b : Fin n)
    (edge : H.adj a b=true)
    (old : ∀ u v : Fin n, G.adj u.succ.succ v.succ.succ=true → H.adj u v=true)
    (only : ∀ x : Fin (n+2), x.val<2 → ∀ v : Fin n, G.adj x v.succ.succ=true → v=a ∨ v=b) :
    G.Planar := by
  have sep (x y) (hx : x.val<2) (e : G.adj x y=true) : y.val<2 ∨ Anchor a b y := by
    refine Fin.cases ?_ (fun z => ?_) y e
    · exact fun _ => Or.inl (by simp)
    · refine Fin.cases ?_ (fun w ew => ?_) z
      · exact fun _ => Or.inl (by simp)
      · rcases only x hx w ew with rfl|rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
  have between {u v : Fin n} (hu : u=a ∨ u=b) (hv : v=a ∨ v=b) : u=v ∨ H.adj u v=true := by
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> simp_all [H.adj_comm]
  have pull {k : Nat} {R : Fin k → Fin k → Bool} (irr : ∀ i, R i i=false) (rob : Robust R)
      (s) (h : G.minorTest R s=true) : ∃ bags,H.minorTest R bags=true := by
    let z : Fin (n+2) := 0
    let o : Fin (n+2) := (0 : Fin (n+1)).succ
    obtain ⟨u,hu,uz⟩ := projection sep rob h z (by simp [z])
    obtain ⟨v,hv,vo⟩ := projection sep rob h o (by simp [o])
    let f : Fin (n+2) → Fin n := Fin.cases u (Fin.cases v id)
    have preserve (x y : Fin (n+2)) : G.adj x y=true → f x=f y ∨ H.adj (f x) (f y)=true := by
      have middle (x : Fin (n+2)) (w : Fin n) (hx : x.val<2) (fc : f x=a ∨ f x=b)
          (e : G.adj x w.succ.succ=true) : f x=w ∨ H.adj (f x) w=true := between fc (only x hx w e)
      have symm {x y : Fin n} (p : x=y ∨ H.adj x y=true) : y=x ∨ H.adj y x=true :=
        p.imp Eq.symm ((H.adj_comm _ _).trans ·)
      have uzero : f z=a ∨ f z=b := hu
      have vopp : f o=a ∨ f o=b := hv
      refine Fin.cases ?_ (fun w => ?_) x <;> refine Fin.cases ?_ (fun l => ?_) y
      · exact fun _ => Or.inl rfl
      · refine Fin.cases (fun _ => between hu hv) (fun r e => ?_) l
        exact middle z r (by simp [z]) uzero e
      · refine Fin.cases (fun _ => between hv hu) (fun r e => ?_) w
        exact symm (middle z r (by simp [z]) uzero ((G.adj_comm _ _).trans e))
      · refine Fin.cases ?_ (fun r => ?_) w <;> refine Fin.cases ?_ (fun t => ?_) l
        · exact fun _ => Or.inl rfl
        · exact middle o t (by simp [o]) vopp
        · exact fun e => symm (middle o r (by simp [o]) vopp ((G.adj_comm _ _).trans e))
        · exact fun e => Or.inr (old r t e)
    apply transfer_minor irr s h f preserve
    intro i j hij x hx y hy same
    have keep (x : Fin (n+2)) (i) : x∈s i → (f x).succ.succ∈s i :=
      Fin.cases (uz i) (fun j => Fin.cases (vo i) (fun _ hh => hh) j) x
    exact (bag_data h).2.1 i j hij _ (keep x i hx) (same ▸ keep y j hy)
  constructor
  · rintro ⟨s,h⟩; apply hp.1 (pull (by decide) ?_ s h)
    unfold Robust
    constructor
    · decide
    · constructor <;> decide
  · rintro ⟨s,h⟩; apply hp.2 (pull (by decide) ?_ s h)
    unfold Robust
    constructor
    · decide
    · constructor <;> decide


end SparseBoundary.Graph
