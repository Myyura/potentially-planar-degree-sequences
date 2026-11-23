import DiskFullerene.CircuitCut
import DiskFullerene.CutSides

namespace DiskFullerene.Dual
open Separation

variable {M : MapData} {G : IsDiskFullerene M h} {n : Nat}
  {v : Fin (n+1) → Face M}

def CycleSide.color (S : CycleSide G v) (x : Nat) : Prop :=
  ∃ b : x<M.ord, S.part.left ⟨x,b⟩

private theorem colorFin (S : CycleSide G v) (x : Fin M.ord) : S.color x ↔ S.part.left x :=
  ⟨fun ⟨_,p⟩ => p, fun p => ⟨x.isLt,p⟩⟩

theorem CycleSide.flip (S : CycleSide G v) {a b : Nat} {e : Edge M}
    (orient : endpoints e=(a,b) ∨ endpoints e=(b,a)) :
    (¬(S.color a ↔ S.color b)) ↔ ∃ i, e=S.edge i := by
  rw [S.part.crosses]
  have p := colorFin S (primal G e).1; have q := colorFin S (primal G e).2
  change S.color (endpoints e).1 ↔ _ at p
  change S.color (endpoints e).2 ↔ _ at q
  rcases orient with t|t <;> rw [t] at p q <;> simp only at p q <;> grind

theorem CycleSide.stable_on_face (S : CycleSide G v) {f : Face M} (off : ∀ i, f ≠ v i)
    {a b} (side : incident M f (a,b)) : S.color a ↔ S.color b := by
  apply Classical.byContradiction
  intro flip
  obtain ⟨e,orient⟩ := repr_dart G (incident_dart G side)
  obtain ⟨i,rfl⟩ := (S.flip orient).mp flip
  have p := crossTable G orient (Or.inl ⟨side,reverse_owner G side⟩)
  rcases p with p|p <;> rcases S.spans i with q|q <;> rw [p] at q <;>
    simp only [Prod.mk.injEq] at q <;> first | exact off _ q.1 | exact off _ q.2

def CycleSide.faceColor (S : CycleSide G v) (f : Face M) : Prop := ∃ a ∈ M.faces[f.val], S.color a

theorem CycleSide.color_at (S : CycleSide G v) {f : Face M} (off : ∀ i, f≠v i)
    {a : Nat} (ha : a ∈ M.faces[f.val]) : S.faceColor f ↔ S.color a := by
  let W := M.faces[f.val]
  have linear (k : Nat) (hk : k<W.length) : S.color W[0] ↔ S.color W[k] := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have lt : k<W.length := by omega
      apply (ih lt).trans
      have step : (W[k],W[next W.length k]'(next_bound lt)) ∈ sides W :=
        List.mem_iff_getElem.mpr ⟨k,by simpa [sides_size] using lt,side_at W k lt⟩
      simpa [next,hk] using S.stable_on_face off step
  refine ⟨?_,fun p => ⟨a,ha,p⟩⟩
  rintro ⟨b,hb,p⟩
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp (show b∈W from hb)
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp (show a∈W from ha)
  exact ((linear i hi).symm.trans (linear j hj)).mp p

theorem CycleSide.walk_stays (S : CycleSide G v) {x y}
    (p : Walk (fun a b : Face M => (∀ i, a≠v i) ∧ (∀ i, b≠v i) ∧ b ∈ dualRow G a) x y) :
    S.faceColor x ↔ S.faceColor y := by
  induction p with
  | refl => rfl
  | step _ edge ih =>
    obtain ⟨a,b,adj⟩ := edge
    obtain ⟨d,di,dj⟩ := (mem_row_iff G _ _).mp adj
    exact ih.trans ((S.color_at a (sideEnds di).1).trans (S.color_at b (sideEnds dj).2).symm)

theorem CycleSide.around_changes (S : CycleSide G v) (hh : 3≤h) (vi : Function.Injective v)
    (i : Fin (n+1)) (k : Fin M.faces[(v i).val].length) :
    (¬(S.color (sideDart M (v i) k).1 ↔ S.color (sideDart M (v i) k).2)) ↔
      atSide G (v i) k = v (cyclicNext i) ∨ atSide G (v i) k = v (cyclicPrev i) := by
  have wd := sideDart_mem M (v i) k
  obtain ⟨e,orient⟩ := repr_dart G (incident_dart G wd)
  refine (S.flip (a := (sideDart M (v i) k).1) (b := (sideDart M (v i) k).2) orient).trans ?_
  have across := crossTable G orient (Or.inl ⟨wd,reverse_owner G wd⟩)
  change Across (dual G) e (v i) (atSide G (v i) k) at across
  have prev (j : Fin (n+1)) : cyclicPrev (cyclicNext j)=j := by
    apply Fin.ext; dsimp [cyclicNext,cyclicPrev]; split <;> split <;> omega
  have nprev (j : Fin (n+1)) : cyclicNext (cyclicPrev j)=j := by
    apply Fin.ext; dsimp [cyclicNext,cyclicPrev]; split <;> split <;> omega
  constructor
  · rintro ⟨j,rfl⟩
    have cases' : (v i=v j ∧ atSide G (v i) k=v (cyclicNext j)) ∨
        (v i=v (cyclicNext j) ∧ atSide G (v i) k=v j) := by
      rcases across with a|a <;> rcases S.spans j with b|b <;> rw [a] at b <;>
        simp only [Prod.mk.injEq] at b <;> grind
    rcases cases' with ⟨r,hj⟩|⟨r,hj⟩
    · exact Or.inl (by simpa [vi r] using hj)
    · have pi : cyclicPrev i=j := by simp [vi r, prev]
      exact Or.inr (by simpa [pi] using hj)
  · rintro (nxt|prv)
    · exact ⟨i,uniqueAcross G hh (nxt ▸ across) (S.spans i)⟩
    · have s := (S.spans (cyclicPrev i)).symm
      rw [nprev] at s
      exact ⟨_,uniqueAcross G hh (prv ▸ across) s⟩

end DiskFullerene.Dual

namespace DiskFullerene.Dual
open Separation

private theorem different_after {n : Nat} {P : Fin n → Prop} (i j : Fin n) (ne : i≠j)
    (go : Fin n → Fin n) (linear : ∀ k, ∀ h : k+1<n, go ⟨k,by omega⟩ = ⟨k+1,h⟩)
    (flip : ∀ k, (¬(P k ↔ P (go k))) ↔ k=i ∨ k=j) : ¬(P (go i) ↔ P (go j)) := by
  have chain {a b : Fin n} (lt : a<b) (pair : (a=i ∧ b=j) ∨ (a=j ∧ b=i)) :
      ¬(P (go a) ↔ P (go b)) := by
    let t := a.val+1
    have ht : t<n := by dsimp [t]; omega
    have seq (k : Nat) (le : t≤k) (upper : k≤b.val) : P ⟨t,ht⟩ ↔ P ⟨k,by omega⟩ := by
      induction k with
      | zero => dsimp [t] at le; omega
      | succ k ih =>
        by_cases start : t=k+1
        · simp [start]
        · have safe : ¬((⟨k,by omega⟩ : Fin n)=i ∨ (⟨k,by omega⟩ : Fin n)=j) := by
            rcases pair with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> dsimp [t] at * <;> intro h <;>
              rcases h with h|h <;> have z := congrArg Fin.val h <;> dsimp at z <;> omega
          have same := Classical.byContradiction fun f => safe ((flip _).mp f)
          exact (ih (by omega) (by omega)).trans (by simpa [linear k (by omega)] using same)
    have toB := seq b.val (by dsimp [t];omega) (by omega)
    have eq : go a = ⟨t,ht⟩ := linear _ ht
    rw [← eq] at toB
    intro same
    exact (flip b).2 (by grind) (toB.symm.trans same)
  by_cases lt : i<j
  · exact chain lt (Or.inl ⟨rfl,rfl⟩)
  · exact fun same => chain (a:=j) (b:=i) (by omega) (Or.inr ⟨rfl,rfl⟩) same.symm

/-- The two sectors following the two cycle edges at a vertex have
opposite colours whenever the two following neighbours are off the cycle. -/
theorem CycleSide.sectors_separate {M : MapData} {G : IsDiskFullerene M h} {n : Nat}
    {v : Fin (n+1) → Face M} (S : CycleSide G v) (hh : 3≤h) (vi : Function.Injective v)
    (i : Fin (n+1)) {a b : Face M}
    (first : (v (cyclicNext i),a) ∈ sides (dualRow G (v i)))
    (last : (v (cyclicPrev i),b) ∈ sides (dualRow G (v i)))
    (distinct : v (cyclicNext i)≠v (cyclicPrev i))
    (ao : ∀ j, a≠v j) (bo : ∀ j, b≠v j) : ¬(S.faceColor a ↔ S.faceColor b) := by
  let u := v i
  let m := M.faces[u.val].length
  let N := atSide G u
  let go (k : Fin m) : Fin m := ⟨next m k.val,next_bound k.isLt⟩
  let P (k : Fin m) : Prop := S.color (M.faces[u.val][k.val]'k.isLt)
  have run {x y : Face M} (ed : (x,y)∈sides (dualRow G u)) : ∃ k : Fin m, N k=x ∧ N (go k)=y := by
    obtain ⟨j,hj,z⟩ := List.mem_iff_getElem.mp ed
    rw [sides_size] at hj; rw [side_at _ j hj] at z
    let r := dualRow G u
    have len : r.length=m := row_length G u
    let k : Fin m := ⟨j,by rw [←len]; exact hj⟩
    refine ⟨k,?_,?_⟩
    · exact (atSide_eq G u k).trans (Prod.mk.inj z).1
    · have index : (go k).val=next r.length j := by simp [go,k,len]
      have eq := (atSide_eq G u (go k))
      change N (go k) = (r[(go k).val]'(by rw [len];exact (go k).isLt)) at eq
      simpa [index] using eq.trans (by simpa [index] using (Prod.mk.inj z).2)
  obtain ⟨j,jx,ja⟩ := run first
  obtain ⟨k,ky,kb⟩ := run last
  have ne : j≠k := fun e => distinct (jx.symm.trans ((congrArg N e).trans ky))
  have compare (t : Fin m) : (¬(P t ↔ P (go t))) ↔ t=j ∨ t=k := by
    have step := S.around_changes hh vi i t
    have d := side_at M.faces[u.val] t.val t.isLt
    change sideDart M u t = _ at d
    change (¬(S.color (sideDart M u t).1 ↔ S.color (sideDart M u t).2)) ↔ N t=_ ∨ N t=_ at step
    rw [← jx,← ky] at step; simp only [d] at step
    exact step.trans (or_congr (atSide_inj G hh u).eq_iff (atSide_inj G hh u).eq_iff)
  have colors {t : Fin m} {x : Face M} (off : ∀ j, x≠v j) (eq : N t=x) : S.faceColor x ↔ P t := by
    have hinc := reverse_owner G (sideDart_mem M u t)
    have pm := (sideEnds hinc).2
    change (sideDart M u t).1 ∈ M.faces[(N t).val] at pm
    subst x
    have c := S.color_at off pm
    have desc := side_at M.faces[u.val] t.val t.isLt
    change sideDart M u t = _ at desc
    simpa [desc,P] using c
  have dis := different_after j k ne go (fun t ht => Fin.ext (by simp [go,next,ht])) compare
  exact fun h => dis ((colors ao ja).symm.trans (h.trans (colors bo kb)))

end DiskFullerene.Dual
