import DiskFullerene.ThreeCut

namespace DiskFullerene.Dual
open Separation

/-- A triangular seam in the dual, together with the actual two components
of the primal after crossing edges are removed. -/
structure TriangleSide {M : MapData} (G : IsDiskFullerene M h) (w x y : Face M) where
  wx : Edge M
  xy : Edge M
  yw : Edge M
  first : Across (dual G) wx w x
  middle : Across (dual G) xy x y
  last : Across (dual G) yw y w
  part : Bipartition (primal G) (ThreeEdges wx xy yw)

theorem hasSides {M} (G : IsDiskFullerene M h) (hh : 3≤h) {w x y : Face M}
    (a : x ∈ dualRow G w) (b : y ∈ dualRow G x) (c : w ∈ dualRow G y) :
    Nonempty (TriangleSide G w x y) := by
  obtain ⟨i,j,k,hi,hj,hk,⟨p⟩⟩ := triangle_separates G hh a b c
  exact ⟨⟨i,j,k,hi,hj,hk,p⟩⟩

/-- Use a total predicate on labels; outside the vertex range it is false. -/
def TriangleSide.color {M : MapData} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) (v : Nat) : Prop := ∃ bound : v<M.ord, S.part.left ⟨v,bound⟩

private theorem colourFin {M : MapData} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) (v : Fin M.ord) : S.color v ↔ S.part.left v :=
  ⟨fun ⟨_,hp⟩ => hp,fun hp => ⟨v.isLt,hp⟩⟩

/-- A side of a primal face flips colour precisely if its edge is one
of the three dual seam edges. -/
theorem TriangleSide.flip_iff {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) {a b : Nat} {e : Edge M}
    (orientation : endpoints e = (a,b) ∨ endpoints e = (b,a)) :
    (¬(S.color a ↔ S.color b)) ↔ ThreeEdges S.wx S.xy S.yw e := by
  rw [S.part.crosses]
  have e1 := colourFin S (primal G e).1
  have e2 := colourFin S (primal G e).2
  change S.color (endpoints e).1 ↔ _ at e1
  change S.color (endpoints e).2 ↔ _ at e2
  rcases orientation with r|r <;> rw [r] at e1 e2 <;> simp only at e1 e2 <;> grind

private theorem seamAcross {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) {e : Edge M} (mark : ThreeEdges S.wx S.xy S.yw e) :
    ∀ z, Separation.incident (dual G) e z → z=w ∨ z=x ∨ z=y := by
  intro z hz
  rcases mark with rfl|rfl|rfl
  · rcases S.first with hh|hh <;> simp [Separation.incident, hh] at hz <;> grind
  · rcases S.middle with hh|hh <;> simp [Separation.incident, hh] at hz <;> grind
  · rcases S.last with hh|hh <;> simp [Separation.incident, hh] at hz <;> grind

theorem TriangleSide.stable {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) {f : Face M} (nf : f≠w ∧ f≠x ∧ f≠y) {a b}
    (side : incident M f (a,b)) : S.color a ↔ S.color b := by
  obtain ⟨e,eq⟩ := repr_dart G (incident_dart G side)
  have cross := crossTable G eq (Or.inl ⟨side,reverse_owner G side⟩)
  by_cases c : S.color a ↔ S.color b
  · exact c
  · have hit := (S.flip_iff eq).mp c
    have mark := seamAcross S hit f (by rcases cross with he|he <;> simp [Separation.incident,he])
    grind

private theorem faceWord_constant {f : List Nat} {P : Nat → Prop}
    (steady : ∀ a b, (a,b) ∈ sides f → (P a ↔ P b)) (u v : Nat) (hu : u∈f) (hv : v∈f) : P u ↔ P v := by
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hu
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hv
  have path (k) (hk : k < f.length) : P f[0] ↔ P f[k] := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have lt : k < f.length := by omega
      apply (ih lt).trans
      apply steady
      have e := side_at f k lt
      have n : next f.length k = k+1 := by simp [next,hk]
      simpa [n] using (show (f[k], f[next f.length k]'(next_bound lt)) ∈ sides f by
        rw [← e]; exact List.getElem_mem _)
  exact (path i hi).symm.trans (path j hj)

theorem TriangleSide.face_constant {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) {f : Face M} (nf : f≠w ∧ f≠x ∧ f≠y)
    {a b : Nat} (ha : a ∈ M.faces[f.val]) (hb : b ∈ M.faces[f.val]) :
    S.color a ↔ S.color b :=
  faceWord_constant (fun _ _ e => S.stable nf e) a b ha hb

theorem sideEnds {f : List Nat} {d : Dart} (m : d ∈ sides f) : d.1 ∈ f ∧ d.2 ∈ f := by
  obtain ⟨k,h,e⟩ := List.mem_iff_getElem.mp m
  rw [sides_size] at h
  rw [side_at _ _ h] at e
  subst d
  exact ⟨List.getElem_mem h,List.getElem_mem _⟩

def TriangleSide.faceColor {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) (f : Face M) : Prop := ∃ a ∈ M.faces[f.val], S.color a

theorem TriangleSide.color_at {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) {f : Face M} (nf : f≠w ∧ f≠x ∧ f≠y)
    {a : Nat} (ha : a ∈ M.faces[f.val]) : S.faceColor f ↔ S.color a := by
  exact ⟨fun ⟨b,hb,h⟩ => (S.face_constant nf hb ha).mp h,fun hv => ⟨a,ha,hv⟩⟩

theorem TriangleSide.edge_stays {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) {f g : Face M} (nf : f≠w ∧ f≠x ∧ f≠y)
    (ng : g≠w ∧ g≠x ∧ g≠y) (adj : g ∈ dualRow G f) :
    S.faceColor f ↔ S.faceColor g := by
  obtain ⟨d,hf,hg⟩ := (mem_row_iff G f g).mp adj
  exact (S.color_at nf (sideEnds hf).1).trans (S.color_at ng (sideEnds hg).2).symm


theorem uniqueAcross {M} (G : IsDiskFullerene M h) (hh : 3 ≤ h) {a b : Edge M} {i j}
    (ha : Across (dual G) a i j) (hb : Across (dual G) b i j) : a=b := by
  by_cases eq : a=b
  · exact eq
  · exfalso
    apply parallel_of_sphere (by have := G.connectivity.1; omega)
      (show 0<M.faces.length by simp [MapData.faces]) (table_euler G)
      (fun x y => liftDual G (fun _ _ _ _ => trivial) (dual_connected G hh x y))
      (vertexBypassTable G) eq _ (primalResilient G a b)
    intro z
    rcases ha with H|H <;> rcases hb with K|K <;> simp [Separation.incident,H,K,or_comm]

/-- The primal edge encountered by crossing the k-th side of face w. -/
def sideDart (M : MapData) (w : Face M) (k : Fin M.faces[w.val].length) : Dart :=
  (sides M.faces[w.val])[k.val]'(by simp [sides_size])
theorem sideDart_mem (M : MapData) (w : Face M) (k : Fin M.faces[w.val].length) :
    incident M w (sideDart M w k) := List.getElem_mem _

noncomputable def atSide {M} (G : IsDiskFullerene M h) (w : Face M)
    (k : Fin M.faces[w.val].length) : Face M := owner G (sideDart M w k).swap

theorem atSide_eq {M} (G : IsDiskFullerene M h) (w : Face M) (k : Fin M.faces[w.val].length) :
    atSide G w k = (dualRow G w)[k.val]'(by rw [row_length];exact k.isLt) := by
  simp [dualRow, atSide, sideDart]

theorem atSide_inj {M} (G : IsDiskFullerene M h) (hh : 3≤h) (w : Face M) :
    Function.Injective (atSide G w) := by
  intro i j eq
  rw [atSide_eq,atSide_eq] at eq
  have nd := row_nodup G (noRepeatOnSphere G hh) w
  have idx := congrArg (fun x => (dualRow G w).idxOf x) eq
  rw [nd.idxOf_getElem,nd.idxOf_getElem] at idx
  exact Fin.ext idx

theorem around_changes {M} {G : IsDiskFullerene M h} (hh : 3≤h) {w x y}
    (S : TriangleSide G w x y) (wx : w≠x) (yw : y≠w)
    (k : Fin M.faces[w.val].length) :
    (¬(S.color (sideDart M w k).1 ↔ S.color (sideDart M w k).2)) ↔
      atSide G w k = x ∨ atSide G w k = y := by
  have wd := sideDart_mem M w k
  have opposite := reverse_owner G wd
  obtain ⟨e,orient⟩ := repr_dart G (incident_dart G wd)
  refine (S.flip_iff (a := (sideDart M w k).1) (b := (sideDart M w k).2) orient).trans ?_
  have across := crossTable G orient (Or.inl ⟨wd,opposite⟩)
  change Across (dual G) e w (atSide G w k) at across
  constructor
  · rintro (rfl|rfl|rfl)
    · rcases across with a|a <;> rcases S.first with b|b <;> rw [a] at b <;> simp at b <;> grind
    · rcases across with a|a <;> rcases S.middle with b|b <;> rw [a] at b <;> simp at b <;> grind
    · rcases across with a|a <;> rcases S.last with b|b <;> rw [a] at b <;> simp at b <;> grind
  · rintro (hx|hy)
    · exact Or.inl (uniqueAcross G hh (hx ▸ across) S.first)
    · exact Or.inr (Or.inr (uniqueAcross G hh (hy ▸ across) S.last.symm))

/-- Changes of colour on a linear interval of a facial boundary. -/
private theorem alongInterval {P : Nat → Prop} {i j : Nat} (le : i≤j)
    (step : ∀ k, i≤k → k<j → (P k ↔ P (k+1))) : P i ↔ P j := by
  induction j with
  | zero =>
    have e : i=0 := by omega
    rw [e]
  | succ j ih =>
    by_cases eq : i=j+1
    · rw [eq]
    · exact (ih (by omega) (fun k lo hi => step k lo (by omega))).trans (step j (by omega) (by omega))

/-- Four interleaved indices in the cyclic rotation of any face cannot
be joined by both diagonals in its simple spherical dual. In particular
this gives noncrossing for all chords of the outside neighbour cycle. -/
theorem noInterleaved {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h) (w : Face M)
    (i j k l : Fin M.faces[w.val].length) (ij : i<j) (jk : j<k) (kl : k<l)
    (first : atSide G w k ∈ dualRow G (atSide G w i)) :
    atSide G w l ∉ dualRow G (atSide G w j) := by
  let N := atSide G w
  have inj : Function.Injective N := atSide_inj G hh w
  have adj (a) : N a ∈ dualRow G w := by
    dsimp [N]; rw [atSide_eq]; exact List.getElem_mem _
  have away (a) : N a ≠ w := fun eq => row_no_loop G hh w (eq ▸ adj a)
  obtain ⟨S⟩ := hasSides G hh (adj i) first ((dual_adj_symmetric G w _).mp (adj k))
  let P := fun t : Nat => S.color (M.faces[w.val][t]?.getD 0)
  have changeAt (t : Nat) (ht : t+1 < M.faces[w.val].length) :
      (¬(P t ↔ P (t+1))) ↔ t=i.val ∨ t=k.val := by
    let z : Fin M.faces[w.val].length := ⟨t,by omega⟩
    have flip := around_changes hh S (Ne.symm (away i)) (away k) z
    have val (a) : N z = N a ↔ t=a.val := ⟨fun q => congrArg Fin.val (inj q),fun q => congrArg N (Fin.ext q)⟩
    change (¬(S.color (sideDart M w z).1 ↔ S.color (sideDart M w z).2)) ↔
      N z=N i ∨ N z=N k at flip
    rw [val i,val k] at flip
    have desc := side_at M.faces[w.val] t z.isLt
    change sideDart M w z = _ at desc
    have lt : t < M.faces[w.val].length := by omega
    simpa [desc,P,next,ht,lt] using flip
  have plain (t : Nat) (ht : t+1 < M.faces[w.val].length) (ti : t≠i.val) (tk : t≠k.val) :
      P t ↔ P (t+1) := by
    apply Classical.byContradiction; intro neg
    exact (changeAt t ht |>.mp neg).elim ti tk
  have jToK := alongInterval (P := P) (i:=j.val) (j:=k.val) (by omega)
    (fun t lo hi => plain t (by omega) (by omega) (by omega))
  have kToL := alongInterval (P := P) (i:=k.val+1) (j:=l.val) (by omega)
    (fun t lo hi => plain t (by omega) (by omega) (by omega))
  have switch := (changeAt k.val (by omega)).mpr (Or.inr rfl)
  intro crossing
  have safe (z : Fin M.faces[w.val].length) (a : z ≠ i) (b : z ≠ k) :
      N z ≠ w ∧ N z ≠ N i ∧ N z ≠ N k := ⟨away z,fun eq => a (inj eq),fun eq => b (inj eq)⟩
  have colour (z : Fin M.faces[w.val].length) (a : z ≠ i) (b : z ≠ k) :
      S.faceColor (N z) ↔ P z.val := by
    have hinc := reverse_owner G (sideDart_mem M w z)
    have primalVertex := (sideEnds hinc).2
    have q := S.color_at (safe z a b) primalVertex
    have desc := side_at M.faces[w.val] z.val z.isLt
    change sideDart M w z = _ at desc
    change S.faceColor (N z) ↔ S.color (sideDart M w z).1 at q
    simpa [desc,P] using q
  have ji : j ≠ i := by omega
  have jnk : j ≠ k := by omega
  have li : l ≠ i := by omega
  have lk : l ≠ k := by omega
  have stable := S.edge_stays (safe j ji jnk) (safe l li lk) crossing
  exact switch (jToK.symm.trans ((colour j ji jnk).symm.trans
    (stable.trans ((colour l li lk).trans kToL.symm))))

end DiskFullerene.Dual
