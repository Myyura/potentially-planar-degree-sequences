import DiskFullerene.EndChain
import DiskFullerene.DualIso

namespace DiskFullerene.Dual
open EndLabels Separation Dissection

theorem incidence_half {M} (G : IsDiskFullerene M h) (hh : 3≤h)
    (u : Fin M.ord) {f g : Face M} (uf : f∈triangle u) (ug : g∈triangle u) (ne : f≠g)
    (fb : IsBoundary G f) (gb : IsBoundary G g) (off : ¬OnCycle (dualRow G (apex M)) f g) :
    ∃ p : Fin M.ord → Bool, ChordHalf G p ∧ p u=false ∧
      ∀ {a b : Face M} {e : Edge M}, IsBoundary G a → IsBoundary G b →
        Across (dual G) e a b → ((p (primal G e).1≠p (primal G e).2) ↔
          ((a=f ∧ b=g) ∨ (a=g ∧ b=f))) := by
  classical
  obtain ⟨e,edge,_⟩ := common_edge_at G hh ne uf ug
  have adj {i j : Face M} {k : Edge M} (hit : Across (dual G) k i j) : j∈dualRow G i := by
    have src : (dual G k).2∈dualRow G (dual G k).1 := (mem_row_iff _ _ _).mpr
      ⟨endpoints k,left_incident G (endpoints_mem k),left_incident G (dart_reverse G (endpoints_mem k))⟩
    rcases hit with eq|eq <;> rw [eq] at src
    · exact src
    · exact (dual_adj_symmetric G _ _).mp src
  obtain ⟨i,j,C,order⟩ := indexed_chord G hh fb gb (adj edge) (fun m=>off (Or.inl m)) (fun m=>off (Or.inr m))
  let w := apex M
  let x := atSide G w i; let y := atSide G w j
  change ((x=f ∧ y=g) ∨ (x=g ∧ y=f)) at order
  have tgt : Across (dual G) e x y := by rcases order with ⟨rfl,rfl⟩|⟨rfl,rfl⟩; exact edge; exact Or.symm edge
  have base (k) : atSide G w k ∈ dualRow G w := by rw [atSide_eq]; exact List.getElem_mem _
  obtain ⟨S⟩ := hasSides G hh (base i) (adj tgt) ((dual_adj_symmetric G _ _).mp (base j))
  let color := fun v => decide (S.part.left v)
  let p := fun v => color v != color u
  have P : ChordHalf G p := by
    refine ⟨⟨i.val,j.val⟩,C,i,j,rfl,rfl,S,!color u,fun v => ?_⟩
    by_cases a : S.part.left u <;> by_cases b : S.part.left v <;> simp [p,color,a,b]
  refine ⟨p,P,by simp [p],?_⟩
  intro a b k ac bc endpoints
  have test : (p (primal G k).1 ≠ p (primal G k).2) ↔ ThreeEdges S.wx S.xy S.yw k := by
    rw [S.part.crosses]
    by_cases c : S.part.left u <;> by_cases d : S.part.left (primal G k).1 <;>
      by_cases t : S.part.left (primal G k).2 <;> simp [p,color,c,d,t]
  rw [test]
  have aw : a≠w := fun eq => row_no_loop G hh _ (eq ▸ ac)
  have bw : b≠w := fun eq => row_no_loop G hh _ (eq ▸ bc)
  have mid : Across (dual G) S.xy x y := S.middle
  have same {a b c d : Face M} {k : Edge M} (A : Across (dual G) k a b) (D : Across (dual G) k c d) :
      (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
    rcases A with l|l <;> rcases D with r|r <;> rw [l] at r <;> simp only [Prod.mk.injEq] at r <;> grind
  constructor
  · rintro (rfl|rfl|rfl)
    · have := same endpoints S.first; grind
    · have := same endpoints mid; grind
    · have := same endpoints S.last; grind
  · intro hit
    have ord : (a=x ∧ b=y) ∨ (a=y ∧ b=x) := by grind
    rcases ord with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Or.inr (Or.inl (uniqueAcross G hh endpoints mid))
    · exact Or.inr (Or.inl (uniqueAcross G hh endpoints (Or.symm mid)))

private theorem otherEnd {M} (G : IsDiskFullerene M h) (e : Edge M) (u : Fin M.ord)
    (ends : u=(primal G e).1 ∨ u=(primal G e).2) :
    ∃ v, ∀ f : Fin M.ord → Bool, (f v≠f u ↔ f (primal G e).1≠f (primal G e).2) := by
  rcases ends with rfl|rfl
  · exact ⟨_,fun _ => ne_comm⟩
  · exact ⟨_,fun _ => Iff.rfl⟩

/-- A facial triangle with all three vertices on the outer link cannot
have three chords as its sides in an equality map. Three such chords
would lead to three different terminal halves. -/
theorem middle_has_boundary_edge {M} (G : IsDiskFullerene M h) (hh : 3≤h)
    (cut : HasChord G) (six : M.hexagons=6) (u : Fin M.ord) {a b c : Face M}
    (au : a∈triangle u) (bu : b∈triangle u) (cu : c∈triangle u)
    (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (A : IsBoundary G a) (B : IsBoundary G b) (C : IsBoundary G c) :
    let row := dualRow G (apex M)
    OnCycle row a b ∨ OnCycle row b c ∨ OnCycle row c a := by
  classical
  apply Classical.byContradiction; intro none
  dsimp only at none
  have na : ¬OnCycle (dualRow G (apex M)) a b := fun h => none (Or.inl h)
  have nb : ¬OnCycle (dualRow G (apex M)) b c := fun h => none (Or.inr (Or.inl h))
  have nc : ¬OnCycle (dualRow G (apex M)) c a := fun h => none (Or.inr (Or.inr h))
  obtain ⟨p,P,pu,ep⟩ := incidence_half G hh u au bu ab A B na
  obtain ⟨q,Q,qu,eq⟩ := incidence_half G hh u bu cu bc B C nb
  obtain ⟨r,R,ru,er⟩ := incidence_half G hh u cu au ac.symm C A nc
  have endpoint {i j : Face M} (iu : i∈triangle u) (ju : j∈triangle u) (ij : i≠j)
      (I : IsBoundary G i) (J : IsBoundary G j) :
      ∃ v, (p v=true ↔ (i=a ∧ j=b) ∨ (i=b ∧ j=a)) ∧
        (q v=true ↔ (i=b ∧ j=c) ∨ (i=c ∧ j=b)) ∧ (r v=true ↔ (i=c ∧ j=a) ∨ (i=a ∧ j=c)) := by
    obtain ⟨k,T,l⟩ := common_edge_at G hh ij iu ju
    obtain ⟨v,V⟩ := otherEnd G k u l
    have p' := (V p).trans (ep I J T)
    have q' := (V q).trans (eq I J T)
    have r' := (V r).trans (er I J T)
    exact ⟨v,by simpa [pu] using p',by simpa [qu] using q',by simpa [ru] using r'⟩
  obtain ⟨v,vp,vq,vr⟩ := endpoint au bu ab A B
  obtain ⟨z,zp,zq,zr⟩ := endpoint bu cu bc B C
  obtain ⟨t,tp,tq,tr⟩ := endpoint cu au ac.symm C A
  have dis {P Q : Fin M.ord → Bool} (hp : ChordHalf G P) (hq : ChordHalf G Q)
      (x y : Fin M.ord) (x1 : P x=true) (x2 : Q x=false) (y1 : P y=false) (y2 : Q y=true)
      (a : P u=false) (b : Q u=false) : ∀ v, P v=true → Q v=true → False := by
    obtain ⟨⟨i,j⟩,empty⟩ := half_laminar hh hp hq
    intro v vh wh
    have := empty v; have := empty x; have := empty y; have := empty u
    cases i <;> cases j <;> simp_all
  have pq := dis P Q v z (by grind) (by grind) (by grind) (by grind) pu qu
  have qr := dis Q R z t (by grind) (by grind) (by grind) (by grind) qu ru
  have pr := dis P R v t (by grind) (by grind) (by grind) (by grind) pu ru
  obtain ⟨d,e,_,ends,_⟩ := equality_chain G hh cut six
  obtain ⟨p',ph,pl⟩ := P.contains_terminal hh
  obtain ⟨q',qh,ql⟩ := Q.contains_terminal hh
  obtain ⟨r',rh,rl⟩ := R.contains_terminal hh
  have unequal {a b x y : Fin M.ord → Bool} (A : TerminalHalf G a)
      (ax : ∀ v, a v=true → x v=true) (by' : ∀ v, b v=true → y v=true)
      (dis : ∀ v, x v=true → y v=true → False) : a≠b := by
    rintro rfl; obtain ⟨v,hv⟩ := A.1.some_vertex
    exact dis v (ax v hv) (by' v hv)
  have notPQ := unequal ph pl ql pq
  have notQR := unequal qh ql rl qr
  have notPR := unequal ph pl rl pr
  have i := (ends _).mp ph
  have j := (ends _).mp qh
  have k := (ends _).mp rh
  grind

end DiskFullerene.Dual
