import RowPortMinor

/-! Relabel only the occupied part of the strip drawing. The ambient
coordinate grid need not inject into a finite spine. -/
namespace Recognition.RowSlotMap
open Recognition.RowPlane Recognition.RowPortMinor LeanPool.K5MinorFreeChoosability

def pos (layers : List Layer) (w : Nat) (p : Nat × Nat) :
    Fin ((layers.length+1)*w+2) := Fin.ofNat _ (slot w p.1 p.2)

def InBox (layers : List Layer) (w : Nat) (p : Nat × Nat) :=
  p.1 ≤ layers.length ∧ p.2 < w

theorem pos_val {ls w p} (good : InBox ls w p) :
    (pos ls w p).val = slot w p.1 p.2 := by
  have bound := (port_bounds w p.1 good.2).2.trans_le
    (Nat.mul_le_mul_right w (Nat.add_le_add_right good.1 1))
  simp [pos,Nat.mod_eq_of_lt (show slot w p.1 p.2 < (ls.length+1)*w+2 by omega)]

theorem pos_inj {ls w p q} (P : InBox ls w p) (Q : InBox ls w q)
    (h : pos ls w p=pos ls w q) : p=q := by
  have eq := congrArg Fin.val h
  rw [pos_val P,pos_val Q] at eq
  have both := slot_injective P.2 Q.2 eq
  exact Prod.ext both.1 both.2

def Forward (ls : List Layer) (p q : Nat × Nat) : Prop :=
  ∃ a, ls[p.1]? = some a ∧ q.1=p.1+1 ∧ a.arc p.2 q.2

theorem forward_edge {ls w p q} (P : InBox ls w p) (Q : InBox ls w q)
    (h : Forward ls p q) : (portGraph ls w).Adj (pos ls w p) (pos ls w q) := by
  obtain ⟨a,entry,next,arc⟩ := h
  have ht : p.1<ls.length := by
    by_contra! z
    rw [List.getElem?_eq_none z] at entry
    contradiction
  rw [List.getElem?_eq_getElem ht,Option.some.injEq] at entry
  apply port_adj (p := p.1%2) (by omega)
  exact ⟨⟨p.1,ht⟩,p.2,q.2,rfl,P.2,Q.2,entry ▸ arc,pos_val P,by rw [pos_val Q,next]⟩

/-- Injectivity and edge preservation are required on the occupied rectangle;
unused points of the ambient infinite grid need no labels in the host. -/
noncomputable def transport {X V W : Type*} {A : SimpleGraph X} {B : SimpleGraph V}
    {G : SimpleGraph W} (M : MinorModel A G) (f : X → V) (inside : X → Prop)
    (bound : ∀ v x, x∈M.branch v → inside x)
    (inj : ∀ x y, inside x → inside y → f x=f y → x=y)
    (edges : ∀ x y, inside x → inside y → A.Adj x y → B.Adj (f x) (f y)) :
    MinorModel B G := by
  classical
  refine ⟨(fun v => (M.branch v).image f),?_,?_,?_,?_⟩
  · intro v
    exact (M.branch_nonempty v).image f
  · intro v
    apply (connSet_iff_induce_connected ..).mp
    have con := (connSet_iff_induce_connected ..).mpr (M.branch_connected v)
    refine ⟨?_,?_⟩
    · exact (M.branch_nonempty v).image f
    · intro a ha b hb
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
      apply RIn.map f _ (con.2 x hx y hy)
      intro p q edge hp hq
      exact RIn.single (edges p q (bound v p hp) (bound v q hq) edge)
        (Finset.mem_image_of_mem _ hp) (Finset.mem_image_of_mem _ hq)
  · intro u v ne
    apply Finset.disjoint_left.mpr
    intro x xu xv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp xu
    obtain ⟨q,hq,eq⟩ := Finset.mem_image.mp xv
    have same := inj q p (bound v q hq) (bound u p hp) eq
    exact Finset.disjoint_left.mp (M.branch_disjoint u v ne) hp (same ▸ hq)
  · intro u v e
    obtain ⟨a,ha,b,hb,edge⟩ := M.branch_adjacent u v e
    exact ⟨_,Finset.mem_image_of_mem _ ha,_,Finset.mem_image_of_mem _ hb,
      edges a b (bound u a ha) (bound v b hb) edge⟩

noncomputable def pack {V : Type*} {G : SimpleGraph V} {ls w}
    {grid : SimpleGraph (Nat × Nat)} (M : MinorModel grid G)
    (bound : ∀ v x, x∈M.branch v → InBox ls w x)
    (arc : ∀ p q, grid.Adj p q → Forward ls p q ∨ Forward ls q p) :
    MinorModel (portGraph ls w) G :=
  transport M (pos ls w) (InBox ls w) bound (fun _ _ => pos_inj) fun p q h k edge => by
    rcases arc p q edge with f|r
    · exact forward_edge h k f
    · exact (forward_edge k h r).symm

end Recognition.RowSlotMap
