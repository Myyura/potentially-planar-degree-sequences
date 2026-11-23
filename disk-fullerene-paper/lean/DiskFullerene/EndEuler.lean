import DiskFullerene.CutSides

namespace DiskFullerene.EndEuler
open Separation

abbrev num {n} (P : Fin n → Bool) := (List.finRange n).countP P

def sideEdge {V E : Type} (ends : E → V × V) (P : V → Bool) (e : E) :=
  P (ends e).1 && P (ends e).2

private theorem add_counts {α} (xs : List α) (a b c : α → Bool)
    (point : ∀ x, (if a x then 1 else 0) + (if b x then 1 else 0) =
      (if c x then 1 else 0)) : xs.countP a + xs.countP b = xs.countP c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h := point x
    simp only [List.countP_cons]
    cases ha : a x <;> cases hb : b x <;> cases hc : c x <;> simp [ha,hb,hc] at h ⊢ <;> omega

private theorem single_count {n} (a : Fin n) :
    num (fun i => decide (i = a)) = 1 := by
  let xs := (List.finRange n).filter (fun i => decide (i=a))
  have nd : xs.Nodup := List.filter_sublist.nodup (List.nodup_finRange n)
  have le := nd.length_le_of_subset (l₂:=[a]) (by intro i m; simpa [xs] using m)
  have ge : a ∈ xs := by simp [xs]
  have pos : 0 < xs.length := List.length_pos_of_mem ge
  change (List.finRange n).countP _ = _
  rw [List.countP_eq_length_filter]
  change xs.length = 1
  simp at le; omega

/-- Follow descending parents from a vertex of color different from the
root until the first color change. The child at that change lies on the
opposite side from the root. -/
private theorem first_cross {n E} {ends : E → Fin (n+1) × Fin (n+1)} {keep}
    (T : Tree ends keep) (P : Fin (n+1) → Bool) (v : Fin (n+1)) (away : P v ≠ P 0) :
    ∃ i : Fin n, P i.succ ≠ P 0 ∧ P (ends (T.pick i)).1 ≠ P (ends (T.pick i)).2 := by
  generalize hh : T.height v = k
  induction k using Nat.strongRecOn generalizing v with
  | ind k ih =>
    rcases Fin.eq_zero_or_eq_succ v with rfl|⟨i,rfl⟩
    · contradiction
    obtain ⟨_,w,cross,less⟩ := T.choice i
    by_cases eq : P w = P 0
    · exact ⟨i,away,by rcases cross with h|h <;> rw [h] <;> simp_all <;> grind⟩
    · exact ih (T.height w) (by omega) w eq rfl

/-- For any tree using at most one crossing edge, its edges internal
to either side are exactly one fewer than the vertices of that side. -/
theorem tree_side_count {n E} {ends : E → Fin (n+1) × Fin (n+1)} {keep}
    (T : Tree ends keep) (P : Fin (n+1) → Bool) (both : ∃v, P v ≠ P 0)
    (bottleneck : ∀ i j, P (ends (T.pick i)).1 ≠ P (ends (T.pick i)).2 →
      P (ends (T.pick j)).1 ≠ P (ends (T.pick j)).2 → i = j) :
    num (fun i => sideEdge ends P (T.pick i)) + 1 = num P := by
  obtain ⟨v,hv⟩ := both
  obtain ⟨k,pk,xk⟩ := first_cross T P v hv
  let a i := sideEdge ends P (T.pick i)
  let b (i : Fin n) := decide (i=k) && P i.succ
  have h : num a + num b = num (fun i : Fin n => P i.succ) := by
    apply add_counts
    intro i
    obtain ⟨_,p,edge,_⟩ := T.choice i
    by_cases eq : i=k
    · subst i
      rcases edge with e|e <;> simp [a,b,sideEdge,e] at xk ⊢ <;>
        cases h₀ : P k.succ <;> cases h₁ : P p <;> simp_all
    · have same : P (ends (T.pick i)).1 = P (ends (T.pick i)).2 := by
        by_cases same : P (ends (T.pick i)).1 = P (ends (T.pick i)).2
        · exact same
        · exact False.elim (eq (bottleneck i k same xk))
      rcases edge with e|e <;> simp [a,b,sideEdge,e,eq] at same ⊢ <;> simp [same]
  have hb : num b = if P k.succ then 1 else 0 := by
    cases ek : P k.succ
    · apply List.countP_eq_zero.mpr
      intro i _
      by_cases eq : i=k <;> simp [b,eq,ek]
    · rw [←single_count k]
      apply List.countP_congr
      intro i _
      by_cases eq : i=k <;> simp [b,eq,ek]
  change num a + 1 = num P
  rw [show num P = (if P 0 then 1 else 0) + num (fun i : Fin n => P i.succ) by
    simp only [num,List.finRange_succ,List.countP_cons,List.countP_map,Function.comp_def]
    omega]
  cases er : P 0 <;> cases ek : P k.succ <;> simp_all <;> omega

end DiskFullerene.EndEuler

namespace DiskFullerene.EndEuler
open Separation

theorem tree_partition {v f e} {p : Fin e → Fin (v+1) × Fin (v+1)}
    {d : Fin e → Fin (f+1) × Fin (f+1)} {keep} (T : Tree p keep)
    (D : Tree d (fun e => ∀ i, T.pick i ≠ e))
    (cover : ∀ e, (∃i, T.pick i=e) ∨ ∃j, D.pick j=e) (W : Fin e → Bool) :
    num W = num (fun i => W (T.pick i)) + num (fun j => W (D.pick j)) := by
  let a := (List.finRange v).map T.pick
  let b := (List.finRange f).map D.pick
  have nd {k} (pick : Fin k → Fin e) (inj : Function.Injective pick) :
      ((List.finRange k).map pick).Nodup :=
    List.pairwise_map.mpr ((List.nodup_finRange _).imp (fun h e => h (inj e)))
  have nodup : (a++b).Nodup := by
    refine List.nodup_append.mpr ⟨nd _ T.injective,nd _ D.injective,?_⟩
    intro e he z hz eq
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
    exact (D.choice j).1 i eq
  have perm : (List.finRange e).Perm (a++b) := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_finRange _) nodup).mpr
    intro t
    simp only [List.mem_finRange,true_iff,List.mem_append,List.mem_map,a,b]
    simpa using cover t
  simpa [a,b,num,List.countP_map,Function.comp_def] using perm.countP_eq W

/-- Abstract incidence version of Euler on either side of a triangular
seam. Face 0 is the apex on the seam. Colors P and Q respectively name
primal vertices on the chosen side and primal faces strictly on that side.
Only nonseam faces enter the face count. -/
theorem triangular_side_euler {v f e} (p : Fin e → Fin (v+1) × Fin (v+1))
    (d : Fin e → Fin (f+1) × Fin (f+1)) (P : Fin (v+1) → Bool) (Q : Fin (f+1) → Bool)
    (a b c : Fin e) (x y : Fin (f+1))
    (bc : b ≠ c)
    (ab : Across d b x y) (ac : Across d c y 0)
    (cross : ∀ t, (P (p t).1 ≠ P (p t).2) ↔ ThreeEdges a b c t)
    (both : ∃ z, P z ≠ P 0)
    (seam : Q 0=false ∧ Q x=false ∧ Q y=false)
    (inner : ∀ t z, z≠0 → z≠x → z≠y → incident d t z → sideEdge p P t = Q z)
    (conn : ∀ z, Walk (Adj p (fun t => ¬(t=b ∨ t=c))) 0 z)
    (dc : ∀ z, Walk (Adj d (fun _ => True)) 0 z) (vb : FaceBypass d p)
    (sphere : v+f=e) : num (sideEdge p P) + 1 = num P + num Q := by
  classical
  let T := makeTree p _ conn
  obtain ⟨D,cover⟩ := complement_spans T dc vb sphere
  have primalCount := tree_side_count T P both (by
    intro i j hi hj
    have ci := (cross _).mp hi
    have cj := (cross _).mp hj
    have ni := (T.choice i).1
    have nj := (T.choice j).1
    apply T.injective
    dsimp [ThreeEdges] at ci cj; grind)
  have chosen (t) (ht : t=b ∨ t=c) : ∃j, D.pick j=t := by
    rcases cover t with ⟨i,rfl⟩|right
    · exact False.elim ((T.choice i).1 ht)
    · exact right
  obtain ⟨j,hj⟩ := chosen b (Or.inl rfl)
  obtain ⟨k,hk⟩ := chosen c (Or.inr rfl)
  have different : j ≠ k := by intro eq; subst k; exact bc (hj.symm.trans hk)
  have chordChild {i : Fin f} : incident d (D.pick i) i.succ := by
    obtain ⟨_,z,hz,_⟩ := D.choice i
    rcases hz with he|he <;> simp [incident,he]
  have jy : j.succ=x ∨ j.succ=y := by
    have h := chordChild (i:=j)
    rw [hj] at h
    rcases ab with he|he <;> simp [incident,he] at h <;> grind
  have ky : k.succ=y := by
    have h := chordChild (i:=k)
    rw [hk] at h
    rcases ac with he|he <;> simp [incident,he] at h <;> grind [Fin.succ_ne_zero]
  have jx : j.succ=x := jy.resolve_right (fun he => different (Fin.succ_inj.mp (he.trans ky.symm)))
  have noEdge {t} (h : t=b ∨ t=c) : sideEdge p P t = false := by
    have nc := (cross t).mpr (Or.inr h)
    unfold sideEdge
    cases l : P (p t).1 <;> cases r : P (p t).2 <;> simp_all
  have sec : num (fun i => sideEdge p P (D.pick i)) = num Q := by
    rw [show num Q = num (fun i : Fin f => Q i.succ) by simp [num,List.finRange_succ,List.countP_map,Function.comp_def,seam.1]]
    apply List.countP_congr
    intro i _
    by_cases ix : i.succ=x
    · have eq := Fin.succ_inj.mp (ix.trans jx.symm)
      subst i; simp [hj,noEdge (Or.inl rfl),jx,seam.2.1]
    by_cases iy : i.succ=y
    · have eq := Fin.succ_inj.mp (iy.trans ky.symm)
      subst i; simp [hk,noEdge (Or.inr rfl),ky,seam.2.2]
    rw [inner _ _ (Fin.succ_ne_zero _) ix iy chordChild]
  have sum := tree_partition T D cover (sideEdge p P)
  omega

end DiskFullerene.EndEuler

namespace DiskFullerene.EndEuler
open Separation

private theorem indexed {v f e} (p : Fin e → Fin v × Fin v) (d : Fin e → Fin f × Fin f)
    (P : Fin v → Bool) (Q : Fin f → Bool) (a b c : Fin e) (w x y : Fin f)
    (h0 : w.val=0) (bc : b ≠ c) (ab : Across d b x y) (ac : Across d c y w)
    (cross : ∀ t, (P (p t).1 ≠ P (p t).2) ↔ ThreeEdges a b c t)
    (both : ∃ l r, P l ≠ P r) (seam : Q w=false ∧ Q x=false ∧ Q y=false)
    (inner : ∀ t z, z≠w → z≠x → z≠y → incident d t z → sideEdge p P t = Q z)
    (conn : ∀ i j, Walk (Adj p (fun t => ¬(t=b ∨ t=c))) i j)
    (dc : ∀ i j, Walk (Adj d (fun _ => True)) i j) (vb : FaceBypass d p)
    (sphere : v+f=e+2) : num (sideEdge p P)+1 = num P+num Q := by
  cases v with
  | zero => obtain ⟨l,_,_⟩ := both; exact Fin.elim0 l
  | succ v =>
    cases f with
    | zero => exact Fin.elim0 w
    | succ f =>
      have wz : w=0 := Fin.ext h0
      subst w
      apply triangular_side_euler p d P Q a b c x y bc ab ac cross _ seam inner (conn _) (dc _) vb (by omega)
      obtain ⟨l,r,h⟩ := both
      by_cases eq : P l = P 0
      · exact ⟨r,by grind⟩
      · exact ⟨l,eq⟩

open Dual

noncomputable def vertexSide {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) (side : Bool) (v : Fin M.ord) : Bool := by
  classical
  exact decide (S.part.left v) == side

noncomputable def faceSide {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) (side : Bool) (v : Face M) : Bool := by
  classical
  exact decide (v≠w ∧ v≠x ∧ v≠y) && (decide (S.faceColor v) == side)

private theorem edge_vertices {ls : List Nat} {uv : Dart} (hi : uv ∈ sides ls) :
    uv.1 ∈ ls ∧ uv.2 ∈ ls := by
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp hi
  have hl : i < ls.length := by simpa [sides_size] using hi
  rw [side_at ls i hl] at eq
  subst uv
  exact ⟨List.getElem_mem _,List.getElem_mem _⟩

/-- Euler count for the two actual components of the original 3-edge
cut. Counts are finite filters on original vertices, edges and faces.
There is no disk Euler assumption for either side. -/
theorem sideEuler {M : MapData} {G : IsDiskFullerene M h} (hh : 3≤h) {x y}
    (S : TriangleSide G (apex M) x y) (side : Bool) :
    num (sideEdge (primal G) (vertexSide S side)) + 1 =
      num (vertexSide S side) + num (faceSide S side) := by
  classical
  let w := apex M
  have nx : x ≠ w := by
    have h := left_ne_right G hh S.wx
    rcases S.first with e|e <;> rw [e] at h <;> simp_all [w,ne_comm]
  have bc : S.xy ≠ S.yw := by
    intro eq
    have h₁ := S.middle
    rw [eq] at h₁
    have h₂ := S.last
    rcases h₁ with he|he <;> rcases h₂ with hj|hj <;> rw [he] at hj <;>
      simp only [Prod.mk.injEq] at hj <;> grind
  apply indexed (primal G) (dual G) (vertexSide S side) (faceSide S side)
    S.wx S.xy S.yw (apex M) x y rfl bc S.middle S.last _ _ _ _
    (primalResilient G _ _) (fun i j => liftDual G (fun _ _ _ _ => trivial) (dual_connected G hh i j))
    (vertexBypassTable G) (table_euler G)
  · intro t
    rw [S.part.crosses]
    by_cases l : S.part.left ((primal G t).1) <;>
      by_cases r : S.part.left ((primal G t).2) <;> cases side <;> simp [vertexSide,l,r]
  · obtain ⟨l,hl⟩ := S.part.inhabitedLeft
    obtain ⟨r,hr⟩ := S.part.inhabitedRight
    exact ⟨l,r,by cases side <;> simp [vertexSide,hl,hr]⟩
  · simp [faceSide]
  · intro t z zw zx zy inc
    have h : Dual.incident M z (endpoints t) ∨ Dual.incident M z (endpoints t).swap := by
      rcases inc with i|j
      · exact Or.inl (i ▸ left_incident G (endpoints_mem t))
      · exact Or.inr (j ▸ left_incident G (dart_reverse G (endpoints_mem t)))
    have edge : (endpoints t).1 ∈ M.faces[z.val] ∧ (endpoints t).2 ∈ M.faces[z.val] := by
      rcases h with h|h
      · exact edge_vertices h
      · have hb := edge_vertices h; exact ⟨hb.2,hb.1⟩
    have link (v : Fin M.ord) : S.color v ↔ S.part.left v :=
      ⟨fun ⟨_,l⟩ => l,fun l => ⟨v.isLt,l⟩⟩
    have l := (S.color_at ⟨zw,zx,zy⟩ edge.1).trans (link (primal G t).1)
    have r := (S.color_at ⟨zw,zx,zy⟩ edge.2).trans (link (primal G t).2)
    simp [sideEdge,vertexSide,faceSide,zw,zx,zy,←l,←r]

end DiskFullerene.EndEuler

namespace DiskFullerene.EndEuler
open Separation Dual

private theorem pathParity {α} (P : α → Bool) (a z : α) (xs : List α) :
    2*(a::xs).countP P + (if P z then 1 else 0) =
      2*((a::xs).zip (xs++[z])).countP (fun e => P e.1 && P e.2) +
      ((a::xs).zip (xs++[z])).countP (fun e => P e.1 != P e.2) +
      (if P a then 1 else 0) := by
  induction xs generalizing a with
  | nil =>
    cases he : P a <;> cases hz : P z <;> simp [he,hz]
  | cons b bs ih =>
    have rest := ih b
    simp only [List.countP_cons, List.cons_append,List.zip_cons_cons] at rest ⊢
    cases ha : P a <;> cases hb : P b <;> simp [hb] at rest ⊢ <;> omega

private theorem parity {α} (P : α → Bool) (r : List α) :
    2*r.countP P = 2*(sides r).countP (fun e => P e.1 && P e.2) +
      (sides r).countP (fun e => P e.1 != P e.2) := by
  cases r with
  | nil => simp [sides]
  | cons a xs => have h := pathParity P a a xs; simp only [sides]; omega

private theorem neighborOf {M} (G : IsDiskFullerene M h) {e : Edge M} {w z : Face M}
    (edge : Across (dual G) e w z) : z ∈ dualRow G w := by
  have base : (dual G e).2 ∈ dualRow G (dual G e).1 :=
    (mem_row_iff _ _ _).mpr ⟨endpoints e,left_incident G (endpoints_mem e),left_incident G (dart_reverse G (endpoints_mem e))⟩
  rcases edge with eq|eq <;> rw [eq] at base
  · exact base
  · exact (dual_adj_symmetric G z w).mp base

private theorem elem_two {α} [DecidableEq α] (l : List α) (nd : l.Nodup) (x y : α)
    (hx : x ∈ l) (hy : y ∈ l) (ne : x ≠ y) :
    l.countP (fun t => decide (t=x ∨ t=y)) = 2 := by
  let keep := l.filter (fun t => decide (t=x ∨ t=y))
  have kt : keep.Nodup := List.filter_sublist.nodup nd
  have target : [x,y].Nodup := by simp [ne]
  have lt := kt.length_le_of_subset (l₂:=[x,y]) (by intro u hu; simp_all [keep])
  have gt := target.length_le_of_subset (l₂:=keep) (by intro u hu; simp only [List.mem_cons,List.not_mem_nil,or_false] at hu; rcases hu with rfl|rfl <;> simp [keep,hx,hy])
  rw [List.countP_eq_length_filter]; change keep.length=2
  simp at lt gt; omega

noncomputable def primalLabelSide {M} {G : IsDiskFullerene M h} {w x y}
    (S : TriangleSide G w x y) (side : Bool) (v : Nat) : Bool := by
  classical
  exact decide (S.color v) == side

/-- On an actual face boundary, the number of incident triangles in the
chosen sector is one more than the number of strict sector vertices in its
dual neighbor cycle. This also gives the exact correction when removing
the apex from the triangular disk counted by sideEuler. -/
theorem sector_count {M : MapData} {G : IsDiskFullerene M h} (hh : 3≤h) {w x y}
    (S : TriangleSide G w x y) (B : Bool) :
    M.faces[w.val].countP (primalLabelSide S B) =
      (dualRow G w).countP (faceSide S B) + 1 := by
  classical
  let W := M.faces[w.val]
  let P := primalLabelSide S B
  have wx := neighborOf G S.first
  have xy := neighborOf G S.middle
  have wy := neighborOf G S.last.symm
  have dist {a b : Face M} (hab : b ∈ dualRow G a) : b≠a := fun he =>
    row_no_loop G hh a (he ▸ hab)
  have d₁ := dist wx
  have d₂ := dist wy
  have d₃ := dist xy
  have changes (e : Dart) (he : e ∈ sides W) :
      (P e.1 != P e.2) = decide (owner G e.swap=x ∨ owner G e.swap=y) := by
    obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp he
    have hl : k < M.faces[w.val].length := by simpa [sides_size,W] using hk
    let i : Fin M.faces[w.val].length := ⟨k,hl⟩
    have pick : sideDart M w i = e := eq
    have alt := Dual.around_changes hh S d₁.symm d₂ i
    simp only [atSide,pick] at alt
    by_cases l : S.color e.1 <;> by_cases r : S.color e.2 <;>
      cases B <;> simp [primalLabelSide,P,l,r] at alt ⊢ <;> grind
  have same (e : Dart) (he : e ∈ sides W) :
      (P e.1 && P e.2) = faceSide S B (owner G e.swap) := by
    have flip := changes e he
    have hrev := reverse_owner G (show Dual.incident M w e from he)
    have other : owner G e.swap ≠ w := by
      apply dist
      exact List.mem_map.mpr ⟨e,he,rfl⟩
    by_cases mark : owner G e.swap=x ∨ owner G e.swap=y
    · simp only [mark,decide_true] at flip
      rcases mark with mark|mark <;> simp [mark,faceSide] <;>
        cases h₁ : P e.1 <;> cases h₂ : P e.2 <;> simp_all
    · have nf : owner G e.swap≠w ∧ owner G e.swap≠x ∧ owner G e.swap≠y := by grind
      have m := edge_vertices hrev
      have c₁ := S.color_at nf m.2
      have c₂ := S.color_at nf m.1
      simp only [Prod.fst_swap,Prod.snd_swap] at c₁ c₂
      simp [primalLabelSide,P,faceSide,nf,←c₁,←c₂]
  have fl : (sides W).countP (fun e => P e.1 != P e.2) =
      (dualRow G w).countP (fun t => decide (t=x ∨ t=y)) := by
    unfold dualRow; rw [List.countP_map]; apply List.countP_congr
    intro e he; rw [changes _ he]; rfl
  have born : (sides W).countP (fun e => P e.1 && P e.2) =
      (dualRow G w).countP (faceSide S B) := by
    unfold dualRow; rw [List.countP_map]; apply List.countP_congr
    intro e he; rw [same _ he]; rfl
  have c := elem_two _ (row_nodup G (noRepeatOnSphere G hh) w) x y wx wy d₃.symm
  have bal := parity P W
  rw [born,fl,c] at bal
  change W.countP P = _
  omega

end DiskFullerene.EndEuler

namespace DiskFullerene.EndEuler
open Separation Dual

private theorem partition_count {α : Type} [DecidableEq α] (xs ys : List α)
    (nx : xs.Nodup) (ny : ys.Nodup) (sub : xs ⊆ ys) (P : α → Bool) :
    xs.countP P + (ys.filter (fun x => !xs.contains x)).countP P = ys.countP P := by
  let keep := ys.filter (fun x => !xs.contains x)
  have nd : (xs++keep).Nodup := by
    refine List.nodup_append.mpr ⟨nx,List.filter_sublist.nodup ny,?_⟩
    intro a ha b hb eq
    subst b; have h := (List.mem_filter.mp hb).2; simp [ha] at h
  have perm : (xs++keep).Perm ys := by
    apply (List.perm_ext_iff_of_nodup nd ny).mpr
    intro a
    by_cases h : a ∈ xs
    · simp [keep,h,sub h]
    · simp [keep,h]
  simpa [keep] using perm.countP_eq P

theorem interior_split {M} {G : IsDiskFullerene M h} (hh : 3≤h) {x y}
    (S : TriangleSide G (apex M) x y) (B : Bool) :
    (diskInterior G).countP (faceSide S B) + (dualRow G (apex M)).countP (faceSide S B) =
      num (faceSide S B) := by
  classical
  let C := dualRow G (apex M)
  have nd : (apex M::C).Nodup := List.nodup_cons.mpr ⟨row_no_loop G hh _,row_nodup G (noRepeatOnSphere G hh) _⟩
  have eq := partition_count (apex M::C) (List.finRange M.faces.length) nd (List.nodup_finRange _)
    (fun z _ => List.mem_finRange z) (faceSide S B)
  change (apex M::C).countP _ + (diskInterior G).countP _ = num _ at eq
  have off : faceSide S B (apex M) = false := by simp [faceSide]
  simp [off,C] at eq
  omega

private theorem vertexInRange {M : MapData} (G : IsDiskFullerene M h) (z : Face M)
    {v : Nat} (hv : v ∈ M.faces[z.val]) : v < M.ord := by
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hv
  let dart := sideDart M z ⟨i,hi⟩
  have h := (dart_info G (incident_dart G (sideDart_mem M z ⟨i,hi⟩))).1
  change ((sides M.faces[z.val])[i]'(by simpa [sides_size] using hi)).1 < M.ord at h
  rw [side_at _ _ hi] at h
  exact h

def offBoundary (M : MapData) :=
  (List.finRange M.ord).filter fun i => !M.outer.contains i.val

theorem primal_sector_split {M} {G : IsDiskFullerene M h} {x y}
    (S : TriangleSide G (apex M) x y) (B : Bool) :
    M.outer.countP (primalLabelSide S B) + (offBoundary M).countP (vertexSide S B) =
      num (vertexSide S B) := by
  classical
  let allVertices := (List.finRange M.ord).map Fin.val
  have allNd : allVertices.Nodup :=
    List.pairwise_map.mpr ((List.nodup_finRange _).imp (fun h eq => h (Fin.ext eq)))
  have o := List.all_eq_true.mp G.faceOrbits M.outer (by simp [MapData.faces])
  have nd : M.outer.Nodup := by simpa [MapData.faceOK] using (Bool.and_eq_true_iff.mp o).1
  have sub : M.outer ⊆ allVertices := by
    intro a ha
    have h := vertexInRange G (apex M) ha
    exact List.mem_map.mpr ⟨⟨a,h⟩,List.mem_finRange _,rfl⟩
  have cmp (i : Fin M.ord) : primalLabelSide S B i.val = vertexSide S B i := by
    have eq : S.color i.val ↔ S.part.left i := ⟨fun ⟨_,hp⟩ => hp,fun hp => ⟨i.isLt,hp⟩⟩
    simp [primalLabelSide,vertexSide,eq]
  have h := partition_count M.outer allVertices nd allNd sub (primalLabelSide S B)
  simpa only [allVertices,offBoundary,List.countP_filter,List.countP_map,Function.comp_def,cmp,num] using h

/-- After removing the apex and its full sector, the remaining region
has boundary length open+2, true interior labels given by diskInterior
on this side, and faces indexed by the selected off-boundary primal
vertices. Its edges consist of the seam xy and the within-side primal
edges minus those crossing from the apex into its open sector. -/
theorem cut_region_euler {M} {G : IsDiskFullerene M h} (hh : 3≤h) {x y}
    (S : TriangleSide G (apex M) x y) (B : Bool) :
    let arc := (dualRow G (apex M)).countP (faceSide S B)
    let interior := (diskInterior G).countP (faceSide S B)
    let triangles := (offBoundary M).countP (vertexSide S B)
    let innerEdges := num (sideEdge (primal G) (vertexSide S B))
    (arc+2+interior) + triangles = (innerEdges-arc+1)+1 := by
  have e := sideEuler hh S B
  have s := sector_count hh S B
  have n := interior_split hh S B
  have p := primal_sector_split S B
  change M.outer.countP _ = _ at s
  dsimp only
  omega

end DiskFullerene.EndEuler
