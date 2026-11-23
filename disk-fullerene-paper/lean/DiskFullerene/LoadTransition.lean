import DiskFullerene.DualIso
import DiskFullerene.TerminalRuns

namespace DiskFullerene.Dual
open EndLabels EndEuler Separation

def endpoint {M} (G : IsDiskFullerene M h) (e : Edge M) (t : Fin M.ord) :=
  t=(primal G e).1 ∨ t=(primal G e).2

theorem endpoint_iff {M} (G : IsDiskFullerene M h) (hh : 3≤h) (e : Edge M) (t : Fin M.ord) :
    endpoint G e t ↔ (dual G e).1∈triangle t ∧ (dual G e).2∈triangle t := by
  have a := sideEnds (left_incident G (endpoints_mem e))
  have b := sideEnds (left_incident G (dart_reverse G (endpoints_mem e)))
  constructor
  · rintro (rfl|rfl)
    · exact ⟨(mem_triangle _ _).mpr a.1,(mem_triangle _ _).mpr b.2⟩
    · exact ⟨(mem_triangle _ _).mpr a.2,(mem_triangle _ _).mpr b.1⟩
  · rintro ⟨l,r⟩
    obtain ⟨k,ac,hit⟩ := common_edge_at G hh (left_ne_right G hh e) l r
    have eq := uniqueAcross G hh ac (show Across (dual G) e (dual G e).1 (dual G e).2 from Or.inl rfl)
    exact eq ▸ hit

private theorem triangle_distinct {M} {G : IsDiskFullerene M h} (hh : 3≤h) {w x y}
    (S : TriangleSide G w x y) : w≠x ∧ w≠y ∧ x≠y := by
  have ne {a b} {e : Edge M} (H : Across (dual G) e a b) : a≠b := by
    have n := left_ne_right G hh e
    rcases H with eq|eq <;> rw [eq] at n <;> simp_all [ne_comm]
  exact ⟨ne S.first,(ne S.last).symm,ne S.middle⟩

private theorem cross_iff_marks {M} {G : IsDiskFullerene M h} (hh : 3≤h) {w x y}
    (S : TriangleSide G w x y) (b : Bool) (e : Edge M) :
    (vertexSide S b (primal G e).1 ≠ vertexSide S b (primal G e).2) ↔
      ((dual G e).1∈[w,x,y] ∧ (dual G e).2∈[w,x,y]) := by
  classical
  have test : (vertexSide S b (primal G e).1 ≠ vertexSide S b (primal G e).2) ↔ ThreeEdges S.wx S.xy S.yw e := by
    rw [S.part.crosses]
    by_cases l : S.part.left (primal G e).1 <;> by_cases r : S.part.left (primal G e).2 <;> cases b <;> simp [vertexSide,l,r]
  rw [test]
  constructor
  · rintro (rfl|rfl|rfl)
    · rcases S.first with a|a <;> simp [a]
    · rcases S.middle with a|a <;> simp [a]
    · rcases S.last with a|a <;> simp [a]
  · intro sides
    have neq := left_ne_right G hh e
    have all : Across (dual G) e w x ∨ Across (dual G) e x y ∨ Across (dual G) e y w := by
      unfold Across
      generalize (dual G e)=k at sides neq ⊢
      rcases k with ⟨i,j⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at sides
      simp only at neq
      rcases sides with ⟨(rfl|rfl|rfl),(rfl|rfl|rfl)⟩ <;> simp_all
    rcases all with a|a|a
    · exact Or.inl (uniqueAcross G hh a S.first)
    · exact Or.inr (Or.inl (uniqueAcross G hh a S.middle))
    · exact Or.inr (Or.inr (uniqueAcross G hh a S.last))

private theorem mask_agree {M} (G : IsDiskFullerene M h) (seed : Edge M) {p q : Fin M.ord → Bool}
    (cross : ∀ e, (p (primal G e).1≠p (primal G e).2) ↔ (q (primal G e).1≠q (primal G e).2))
    {t} (agree : p t=q t) : p=q := by
  funext u
  have path := primalResilient G seed seed t u
  induction path with
  | refl => exact agree
  | @step a b _ hop ih =>
    obtain ⟨e,_,eab⟩ := hop
    have h := cross e
    rcases eab with eq|eq <;> rw [eq] at h <;> cases w : p a <;> cases x : p b <;> cases y : q a <;> cases z : q b <;> simp_all

/-- Consecutive seams wxy and wxz share w,x. In the two triangles of
the quadrilateral the primal vertices t and o are the only vertices that
change side. The choice of the two side orientations is fixed at t. -/
theorem advance_sides {M} {G : IsDiskFullerene M h} (hh : 3≤h) {w x y z : Face M}
    (S : TriangleSide G w x y) (T : TriangleSide G w x z) (b d : Bool) (yz : y≠z)
    {t o : Fin M.ord} (tr : ∀ f, f∈triangle t ↔ f=x ∨ f=y ∨ f=z)
    (ap : ∀ f, f∈triangle o ↔ f=w ∨ f=y ∨ f=z)
    (fromSide : vertexSide S b t=false) (toSide : vertexSide T d t=true) :
    ∀ v, vertexSide T d v = if v=t ∨ v=o then !vertexSide S b v else vertexSide S b v := by
  classical
  let p := vertexSide S b
  let q := vertexSide T d
  let patch := fun v : Fin M.ord => decide (v=t ∨ v=o)
  have s := triangle_distinct hh S
  have j := triangle_distinct hh T
  have to : t≠o := by
    rintro rfl
    have := (tr x).mpr (by simp)
    have := (ap x).mp this
    grind
  have cross (e : Edge M) :
      (q (primal G e).1≠q (primal G e).2) ↔
      ((p (primal G e).1 ^^ patch (primal G e).1) ≠ (p (primal G e).2 ^^ patch (primal G e).2)) := by
    let a := (primal G e).1; let a' := (primal G e).2
    have edgeNe : a≠a' := fun H => (dart_info G (endpoints_mem e)).2.2 (congrArg Fin.val H)
    have flip_pair {α : Type} [DecidableEq α] (a b t o : α) (ab : a≠b) (diff : t≠o) :
        (decide (a=t ∨ a=o) ≠ decide (b=t ∨ b=o)) ↔ ¬((t=a ∨ t=b) ↔ (o=a ∨ o=b)) := by
      simp only [ne_eq,decide_eq_decide]; grind
    have patchEq : (patch a≠patch a') ↔ (¬(endpoint G e t ↔ endpoint G e o)) := by
      exact flip_pair a a' t o edgeNe to
    rw [endpoint_iff G hh,endpoint_iff G hh] at patchEq
    simp only [tr,ap] at patchEq
    have pp := cross_iff_marks hh S b e
    have qq := cross_iff_marks hh T d e
    change (p a≠p a') ↔ _ at pp
    change (q a≠q a') ↔ _ at qq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at pp qq
    have n := left_ne_right G hh e
    have logical : (q a≠q a') ↔ ¬((p a≠p a') ↔ (patch a≠patch a')) := by
      rcases H : dual G e with ⟨i,k⟩
      rw [H] at pp qq patchEq n
      simp only at pp qq patchEq n
      grind (splits := 35)
    change (q a≠q a') ↔ ((p a ^^ patch a)≠(p a' ^^ patch a'))
    rw [logical]
    cases p a <;> cases p a' <;> cases patch a <;> cases patch a' <;> decide
  have masks := mask_agree G S.wx (p:=q) (q:=fun v => p v ^^ patch v) cross
    (t:=t) (by change vertexSide T d t=(vertexSide S b t ^^ patch t); simp [fromSide,toSide,patch])
  intro v
  have eq := congrFun masks v
  change q v = (p v ^^ patch v) at eq
  change q v=if v=t ∨ v=o then !p v else p v
  by_cases yes : v=t ∨ v=o
  · have h : patch v=true := decide_eq_true yes
    simp only [yes,↓reduceIte]
    simpa only [h,Bool.xor_true] using eq
  · have h : patch v=false := decide_eq_false yes
    simp only [yes,↓reduceIte]
    simpa only [h,Bool.xor_false] using eq

end DiskFullerene.Dual
