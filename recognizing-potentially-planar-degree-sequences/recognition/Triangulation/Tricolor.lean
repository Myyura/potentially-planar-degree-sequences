import Triangulation.Stacking

namespace Recognition.Tricolor
open Rigidity Stacking
variable {V : Type} (M : Map V) (fill : Choice V)
abbrev tag (j : Fin 3) : Fin 7 := j.castLE (by decide)

structure Parent (color : Vertex M fill → Fin 7) (t : Fin 3 → Vertex M fill) (p : Fin 3 → V) : Prop where
  face : M.face (p 0) (p 1) (p 2)
  colors : ∀ i, color (.inl (p i)) = tag i
  form : (¬fill (corners (p 0) (p 1) (p 2)) ∧ ∀ i, t i = .inl (p i)) ∨
    ∃ s : Star M fill, s.val = corners (p 0) (p 1) (p 2) ∧
      ∃ j : Fin 3, color (.inr s) = tag j ∧
        ∀ i, t i = if i=j then .inr s else .inl (p i)

private theorem tag_inj {i j : Fin 3} (h : tag i = tag j) : i=j := Fin.ext (congrArg (Fin.val (n := 7)) h)

private theorem three (i : Fin 3) : i=0 ∨ i=1 ∨ i=2 := by
  have hi := i.isLt
  rcases (show i.val=0 ∨ i.val=1 ∨ i.val=2 from by omega) with h|h|h
  · exact .inl (Fin.ext h)
  · exact .inr (.inl (Fin.ext h))
  · exact .inr (.inr (Fin.ext h))

private theorem from_star (s : Star M fill) {a b c : V} (ab : a≠b) (bc : b≠c) (ac : a≠c)
    (ha : s.val a) (hb : s.val b) (hc : s.val c) :
    M.face a b c ∧ s.val = corners a b c := by
  obtain ⟨u,v,w,h,hk⟩ := s.property.1
  rw [hk] at ha hb hc ⊢
  have r := M.rot h
  have rr := M.rot r
  have f := M.flip h
  have fr := M.flip r
  have frr := M.flip rr
  constructor
  · simp only [corners] at ha hb hc
    grind
  · funext z; apply propext
    simp only [corners] at *; grind

theorem parent_exists
    (color : Vertex M fill → Fin 7) (t : Fin 3 → Vertex M fill)
    (child : (stack M fill).face (t 0) (t 1) (t 2)) (colors : ∀ i, color (t i) = tag i)
    (anchor : ∀ (s : Star M fill) (j : Fin 3), color (.inr s) = tag j →
      ∃ v, s.val v ∧ color (.inl v) = color (.inr s)) :
    ∃ p, Parent M fill color t p := by
  classical
  have project (i : Fin 3) : ∃ v : V, color (.inl v) = tag i ∧
      (∀ a, t i = .inl a → v=a) ∧ (∀ s, t i = .inr s → s.val v) := by
    cases h : t i with
    | inl a => exact ⟨a,h ▸ colors i,by simp,by simp⟩
    | inr s =>
      obtain ⟨v,hv,eq⟩ := anchor s i (h ▸ colors i)
      exact ⟨v,eq.trans (h ▸ colors i),by simp,by simpa using hv⟩
  let p := fun i => (project i).choose
  have col (i) : color (.inl (p i)) = tag i := (project i).choose_spec.1
  have old {i a} (h : t i = .inl a) : p i=a := (project i).choose_spec.2.1 a h
  have atStar {i s} (h : t i = .inr s) : s.val (p i) := (project i).choose_spec.2.2 s h
  have neq {i j} (h : i ≠ j) : p i ≠ p j := by
    intro eq
    exact h (tag_inj ((col i).symm.trans ((congrArg (fun v => color (.inl v)) eq).trans (col j))))
  have ab := neq (by decide : (0:Fin 3)≠1)
  have bc := neq (by decide : (1:Fin 3)≠2)
  have ac := neq (by decide : (0:Fin 3)≠2)
  have mixed (s : Star M fill) (j : Fin 3) (hs : t j=.inr s)
      (ha : s.val (p 0)) (hb : s.val (p 1)) (hc : s.val (p 2))
      (keep : ∀ i, i ≠ j → t i = .inl (p i)) : Parent M fill color t p := by
    obtain ⟨hf,hkey⟩ := from_star M fill s ab bc ac ha hb hc
    refine ⟨hf,col,Or.inr ⟨s,hkey,j,hs ▸ colors j,?_⟩⟩
    intro i; by_cases eq : i=j
    · simpa [eq] using hs
    · simp [eq,keep i eq]
  refine ⟨p,?_⟩
  change Stacking.face M fill (t 0) (t 1) (t 2) at child
  cases ha : t 0 with
  | inl a =>
    cases hb : t 1 with
    | inl b =>
      cases hc : t 2 with
      | inl c =>
        rw [ha,hb,hc] at child
        change M.face a b c ∧ ¬fill (corners a b c) at child
        refine ⟨by simpa [old ha,old hb,old hc] using child.1,col,Or.inl ⟨?_,?_⟩⟩
        · simpa [old ha,old hb,old hc] using child.2
        · intro i; rcases three i with rfl|rfl|rfl <;> simp [ha,hb,hc,old ha,old hb,old hc]
      | inr s =>
        rw [ha,hb,hc] at child
        change a≠b ∧ s.val a ∧ s.val b at child
        apply mixed s 2 hc (old ha ▸ child.2.1) (old hb ▸ child.2.2) (atStar hc)
        intro i hi; rcases three i with rfl|rfl|rfl <;> simp_all [old ha,old hb]
    | inr s =>
      cases hc : t 2 with
      | inl c =>
        rw [ha,hb,hc] at child
        change c≠a ∧ s.val c ∧ s.val a at child
        apply mixed s 1 hb (old ha ▸ child.2.2) (atStar hb) (old hc ▸ child.2.1)
        intro i hi; rcases three i with rfl|rfl|rfl <;> simp_all [old ha,old hc]
      | inr u => rw [ha,hb,hc] at child; exact False.elim child
  | inr s =>
    cases hb : t 1 with
    | inl b =>
      cases hc : t 2 with
      | inl c =>
        rw [ha,hb,hc] at child
        change b≠c ∧ s.val b ∧ s.val c at child
        apply mixed s 0 ha (atStar ha) (old hb ▸ child.2.1) (old hc ▸ child.2.2)
        intro i hi; rcases three i with rfl|rfl|rfl <;> simp_all [old hb,old hc]
      | inr u => rw [ha,hb,hc] at child; exact False.elim child
    | inr u => cases hc : t 2 <;> rw [ha,hb,hc] at child <;> exact False.elim child

theorem parent_injective {color : Vertex M fill → Fin 7} {t u : Fin 3 → Vertex M fill} {p : Fin 3 → V}
    (a : Parent M fill color t p) (b : Parent M fill color u p) : t=u := by
  rcases a.form with ⟨na,ha⟩|⟨s,hs,j,cj,tj⟩ <;> rcases b.form with ⟨nb,hb⟩|⟨r,hr,k,ck,uk⟩
  · exact funext (fun i => (ha i).trans (hb i).symm)
  · exact False.elim (na (hr ▸ r.property.2))
  · exact False.elim (nb (hs ▸ s.property.2))
  · have eq : s=r := Subtype.ext (hs.trans hr.symm)
    subst r
    have eq := tag_inj (cj.symm.trans ck)
    subst k
    exact funext fun i => (tj i).trans (uk i).symm

end Recognition.Tricolor
