import DiskFullerene.EndMixed
import DiskFullerene.InteriorTriangles

namespace DiskFullerene.EndEuler
open Separation

private theorem steps_of_walk {R : α → α → Prop} {r x} (w : Walk R r x) :
    ∃n, Steps R r n x := by
  induction w with
  | refl => exact ⟨0,.zero⟩
  | step _ e ih => obtain ⟨n,h⟩ := ih; exact ⟨n+1,.next h e⟩

private theorem least {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ k, P k → n≤k := by
  classical
  obtain ⟨n,hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases e : ∃ k, k<n ∧ P k
    · obtain ⟨k,hk,hp⟩ := e; exact ih k hk hp
    · exact ⟨n,hn,by intro k hk; by_cases le : k<n; exact False.elim (e ⟨k,le,hk⟩); omega⟩

private theorem leSum {xs : List Nat} (h : x∈xs) : x≤xs.sum := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl|h
    · omega
    · have := ih h; omega

/-- Build a spanning tree whose parent edges at vertices of the connected
set B, apart from the root, lie wholly in B. No numbering of B other than
having vertex 0 in B is needed. -/
private theorem preferredTree {n e} (edges : Fin e → Fin (n+1) × Fin (n+1))
    (B : Fin (n+1) → Bool) (conn : ∀ v, Walk (Adj edges (fun _ => True)) 0 v)
    (inB : ∀ v, B v=true → Walk (Adj edges (fun t => sideEdge edges B t=true)) 0 v) :
    ∃ T : Tree edges (fun _ => True),
      ∀ i, B i.succ=true → sideEdge edges B (T.pick i)=true := by
  classical
  let T := makeTree edges (fun _ => True) conn
  let R := Adj edges (fun t => sideEdge edges B t=true)
  have best (v) (hv : B v=true) := least (steps_of_walk (inB v hv))
  let heightB (v) := if hv : B v=true then (best v hv).choose else 0
  have spec (v) (hv : B v=true) :
      Steps R 0 (heightB v) v ∧ ∀ m, Steps R 0 m v → heightB v ≤ m := by
    simpa [heightB,hv,R] using (best v hv).choose_spec
  let maxB := ((List.finRange (n+1)).map heightB).sum
  have bound (v) : heightB v≤maxB := leSum (List.mem_map.mpr ⟨v,List.mem_finRange _,rfl⟩)
  let height (v) := if B v then heightB v else maxB+1+T.height v
  have pick (i : Fin n) : ∃ e, (B i.succ=true → sideEdge edges B e=true) ∧
      ∃ p, Across edges e i.succ p ∧ height p < height i.succ := by
    by_cases hB : B i.succ = true
    · have walk := (spec _ hB).1
      generalize hd : heightB i.succ = k at walk
      generalize hi : i.succ = v at walk
      cases walk with
      | zero => exact (i.succ_ne_zero hi).elim
      | @next m p v w edge =>
        obtain ⟨t,bb,ac⟩ := edge
        have bp : B p=true := by
          rcases ac with he|he <;> simp [sideEdge,he] at bb <;> grind
        have hp := (spec _ bp).2 m w
        subst v
        exact ⟨t,fun _=>bb,p,ac.symm,by simp [height,bp,hB]; omega⟩
    · obtain ⟨_,p,ac,lt⟩ := T.choice i
      refine ⟨T.pick i,by simp [hB],p,ac,?_⟩
      by_cases bp : B p=true
      · have := bound p; simp [height,hB,bp]; omega
      · simp [height,hB,bp,lt]
  let tr : Tree edges (fun _ => True) := ⟨height,fun i => (pick i).choose,
    fun i => ⟨trivial,(pick i).choose_spec.2⟩⟩
  exact ⟨tr,fun i => (pick i).choose_spec.1⟩

/-- Each vertex in a marked subset C accounts for a distinct edge touching
C in a spanning tree, provided the complementary set is nonempty. If the
root lies in C, an edge entering C's complement accounts for the root. -/
private theorem touches_lower {n e} {ends : Fin e → Fin (n+1) × Fin (n+1)} {keep}
    (T : Tree ends keep) (C : Fin (n+1) → Bool) (eligible : Fin e → Bool)
    (outside : ∃ v, C v=false)
    (touch : ∀ t v, incident ends t v → C v=true → eligible t=true) :
    num C ≤ num (fun i => eligible (T.pick i)) := by
  let marked := (List.finRange n).filter (fun i => C i.succ)
  let choices := (List.finRange n).filter (fun i => eligible (T.pick i))
  have used : marked ⊆ choices := by
    intro i hi
    obtain ⟨_,p,ac,_⟩ := T.choice i
    exact List.mem_filter.mpr ⟨List.mem_finRange _,touch _ _ (by
      rcases ac with he|he <;> simp [incident,he]) (List.mem_filter.mp hi).2⟩
  have nd : marked.Nodup := List.filter_sublist.nodup (List.nodup_finRange _)
  change num C ≤ (List.finRange n).countP _
  rw [List.countP_eq_length_filter]
  change num C ≤ choices.length
  have tot : num C = marked.length + (if C 0 then 1 else 0) := by
    unfold num; rw [List.finRange_succ,List.countP_cons,List.countP_map,List.countP_eq_length_filter]; rfl
  rw [tot]
  cases root : C 0 with
  | false => simp; exact nd.length_le_of_subset used
  | true =>
    obtain ⟨v,cv⟩ := outside
    -- Follow a vertex outside C up to its first ancestor in C.
    have enter (v) (cv : C v=false) : ∃ i, C i.succ=false ∧ eligible (T.pick i)=true := by
      generalize hd : T.height v=k
      induction k using Nat.strongRecOn generalizing v with
      | ind k ih =>
        rcases Fin.eq_zero_or_eq_succ v with rfl|⟨i,rfl⟩
        · simp_all
        obtain ⟨_,p,ac,lt⟩ := T.choice i
        cases cp : C p with
        | false => exact ih (T.height p) (by omega) p cp rfl
        | true => exact ⟨i,cv,touch _ _ (by rcases ac with he|he <;> simp [incident,he]) cp⟩
    obtain ⟨i,ci,ei⟩ := enter v cv
    have ext : (i::marked).Nodup := List.nodup_cons.mpr ⟨by simp [marked,ci],nd⟩
    have sub : i::marked ⊆ choices := by
      intro j hj; rcases List.mem_cons.mp hj with rfl|him
      · simp [choices,ei]
      · exact used him
    exact ext.length_le_of_subset sub

end DiskFullerene.EndEuler

namespace DiskFullerene.EndEuler
open Separation

private theorem count_mono {α} (l : List α) (p q : α → Bool)
    (imp : ∀ x ∈ l, p x=true → q x=true) : l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have i := ih (fun x hx => imp x (by simp [hx]))
    have h := imp a (by simp)
    cases ha : p a <;> cases hb : q a <;> simp [ha,hb] at h ⊢ <;> omega

theorem connected_side_bound {v f e} (d : Fin e → Fin (f+1) × Fin (f+1))
    (p : Fin e → Fin (v+1) × Fin (v+1)) (B : Fin (f+1) → Bool) (C : Fin (v+1) → Bool)
    (root : B 0=true) (conn : ∀ z, Walk (Adj d (fun _ => True)) 0 z)
    (induced : ∀ z, B z=true → Walk (Adj d (fun t => sideEdge d B t=true)) 0 z)
    (pc : ∀ z, Walk (Adj p (fun _ => True)) 0 z)
    (vb : FaceBypass p d) (sphere : v+f=e)
    (touch : ∀ t z, incident p t z → C z=true → sideEdge d B t=true)
    (outside : ∃z,C z=false) :
    num B + num C ≤ num (sideEdge d B)+1 := by
  obtain ⟨T,ht⟩ := preferredTree d B conn induced
  obtain ⟨D,cover⟩ := complement_spans T pc vb (by omega)
  have small := count_mono (List.finRange f) (fun i => B i.succ)
    (fun i => sideEdge d B (T.pick i)) (fun i _ => ht i)
  have nb : num B = num (fun i : Fin f => B i.succ) + 1 := by
    unfold num; rw [List.finRange_succ,List.countP_cons,List.countP_map]; simp [root,Function.comp_def]
  have add := tree_partition T D cover (sideEdge d B)
  have low := touches_lower D C _ outside touch
  change num (fun i : Fin f => B i.succ) ≤ num (fun i => sideEdge d B (T.pick i)) at small
  omega

private theorem indexed_bound {v f e} (d : Fin e → Fin f × Fin f) (p : Fin e → Fin v × Fin v)
    (w : Fin f) (zero : w.val=0) (z : Fin v) (B : Fin f → Bool) (C : Fin v → Bool)
    (root : B w=true) (conn : ∀ u, Walk (Adj d (fun _ => True)) w u)
    (induced : ∀ u, B u=true → Walk (Adj d (fun t => sideEdge d B t=true)) w u)
    (pc : ∀ u v, Walk (Adj p (fun _ => True)) u v)
    (vb : FaceBypass p d) (sphere : v+f=e+2)
    (touch : ∀ t z, incident p t z → C z=true → sideEdge d B t=true)
    (outside : C z=false) : num B + num C ≤ num (sideEdge d B)+1 := by
  cases v with
  | zero => exact Fin.elim0 z
  | succ v =>
    cases f with
    | zero => exact Fin.elim0 w
    | succ f =>
      have eq : w=0 := Fin.ext zero
      subst w
      exact connected_side_bound _ _ _ _ root conn induced (pc _) vb (by omega) touch ⟨z,outside⟩

end DiskFullerene.EndEuler

namespace DiskFullerene.EndEuler
open Separation Dual

private def valOf (b : Bool) : Nat := if b then 1 else 0

private theorem count_three {α} (l : List α) (p q r : α → Bool)
    (localEq : ∀ i ∈ l, valOf (p i)+valOf (q i)+valOf (r i)=1) :
    l.countP p+l.countP q+l.countP r=l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have one := localEq a (by simp)
    have prev := ih (fun z hz => localEq z (by simp [hz]))
    simp only [List.countP_cons,List.length_cons]
    unfold valOf at one
    omega

/-- A monochromatic dual triangle: both incident faces at every dart of
its corresponding cubic primal vertex have the stated color. -/
noncomputable def solid {M} (G : IsDiskFullerene M h) (P : Face M → Bool) (b : Bool)
    (u : Fin M.ord) : Bool :=
  (M.rows[u.val]'u.isLt).all fun a =>
    (P (owner G (u.val,a)) == b) && (P (owner G (a,u.val)) == b)

private theorem vertex_partition {M} (G : IsDiskFullerene M h) (P : Face M → Bool) :
    num (solid G P true)+num (solid G P false)+num (mixedVertex G P)=M.ord := by
  refine (count_three (List.finRange M.ord) _ _ _ ?_).trans List.length_finRange
  intro v _
  let r := M.rows[v.val]'v.isLt
  have len := G.cubic r (List.getElem_mem v.isLt)
  have ok := List.all_eq_true.mp G.simpleRotation (r,v.val)
    (List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem v.isLt))
  have nd : r.Nodup := by simpa using (Bool.and_eq_true_iff.mp ok).1
  obtain ⟨a,b,c,eq⟩ : ∃a b c, r=[a,b,c] := ⟨_,_,_,List.eq_getElem_of_length_eq_three r len⟩
  rw [eq] at nd; simp at nd
  have row : M.rows[v.val]?.getD [] = [a,b,c] := by rw [List.getElem?_eq_getElem v.isLt]; exact eq
  have turn (i j : Nat) (m : i∈[a,b,c]) (t : M.turn (i,v.val)=(v.val,j)) :
      owner G (i,v.val) = owner G (v.val,j) := by
    have e : (v.val,i)∈M.darts := dart_iff.mpr (by simp [MapData.adj,row,m])
    exact (owner_eq G (t ▸ incident_turn G (owner_incident G (dart_reverse G e)))).symm
  have t1 := turn a b (by simp) (by simp [MapData.turn,row])
  have t2 := turn b c (by simp) (by simp [MapData.turn,row,nd,List.idxOf_cons])
  have t3 := turn c a (by simp) (by simp [MapData.turn,row,nd,List.idxOf_cons])
  unfold solid mixedVertex
  change valOf (r.all _) + valOf (r.all _) + valOf (r.any _) = 1
  rw [eq]
  cases pa : P (owner G (v.val,a)) <;> cases pb : P (owner G (v.val,b)) <;>
    cases pc : P (owner G (v.val,c)) <;> simp [mixedDart,valOf,t1,t2,t3,pa,pb,pc]

private theorem edge_partition {M} (G : IsDiskFullerene M h) (P : Face M → Bool) :
    num (sideEdge (dual G) P)+num (sideEdge (dual G) (fun v=> !P v))+
      num (fun e => P (dual G e).1 != P (dual G e).2) = (edges M).length := by
  have eq := count_three (List.finRange (edges M).length) (sideEdge (dual G) P)
    (sideEdge (dual G) (fun v=> !P v)) (fun e => P (dual G e).1 != P (dual G e).2)
    (by intro i _; cases h₁ : P (dual G i).1 <;> cases h₂ : P (dual G i).2 <;> simp [sideEdge,h₁,h₂,valOf])
  simpa [num] using eq

private theorem all_edges {M} (G : IsDiskFullerene M h) (P : Face M → Bool) {e : Edge M}
    {v : Fin M.ord} (inc : Separation.incident (primal G) e v) (s : solid G P false v=true) :
    sideEdge (dual G) (fun i=> !P i) e=true := by
  let t := endpoints e
  have owner₁ : owner G t = (dual G e).1 := owner_eq G (left_incident G (endpoints_mem e))
  have owner₂ : owner G t.swap = (dual G e).2 := owner_eq G (left_incident G (dart_reverse G (endpoints_mem e)))
  have use (w : Nat) (m : M.adj v.val w) :
      P (owner G (v.val,w))=false ∧ P (owner G (w,v.val))=false := by
    have mw : w∈M.rows[v.val]'v.isLt := by simpa [MapData.adj,List.getElem?_eq_getElem v.isLt] using m
    simpa using List.all_eq_true.mp s w mw
  unfold Separation.incident at inc
  simp [sideEdge,←owner₁,←owner₂]
  rcases inc with eq|eq
  · have hv : t.1=v.val := congrArg Fin.val eq
    have m := dart_iff.mp (endpoints_mem e)
    change M.adj t.1 t.2 at m; rw [hv] at m
    have both := use t.2 m
    rw [← hv] at both
    exact both
  · have hv : t.2=v.val := congrArg Fin.val eq
    have m := dart_iff.mp (dart_reverse G (endpoints_mem e))
    change M.adj t.2 t.1 at m; rw [hv] at m
    have both := use t.1 m
    rw [←hv] at both
    exact both.symm

/-- Euler inequality for the actual induced complex of any set of dual
vertices that avoids the apex and has connected complement. #vertices is
the number of chosen dual vertices; #faces counts only *actual* triangular
faces with three chosen vertices (not arbitrary 3-cycles). -/
theorem induced_euler_bound {M} (G : IsDiskFullerene M h) (hh : 3≤h)
    (A : Face M → Bool) (apexOut : A (apex M)=false)
    (outside : ∃ z, solid G A false z = false)
    (conn : ∀ z, A z=false →
      Walk (Adj (dual G) (fun t => sideEdge (dual G) (fun i=> !A i) t=true)) (apex M) z) :
    num (sideEdge (dual G) A)+1 ≤ num A + num (solid G A true) := by
  obtain ⟨z,hz⟩ := outside
  have primalConn (u v : Fin M.ord) : Walk (Adj (primal G) (fun _ => True)) u v := by
    obtain ⟨e,_⟩ : ∃ e : Edge M, True := by
      have e := table_euler G; have := G.connectivity.1
      exact ⟨⟨0,by omega⟩,trivial⟩
    have p := primalResilient G e e u v
    induction p with
    | refl => exact .refl
    | step _ he ih =>
      obtain ⟨k,_,ac⟩ := he
      exact ih.step ⟨k,trivial,ac⟩
  have h := indexed_bound (dual G) (primal G) (apex M) rfl z (fun i=> !A i) (solid G A false)
    (by simp [apexOut]) (fun i => liftDual G (fun _ _ _ _ => trivial) (dual_connected G hh _ i))
    (fun i hi => conn i (by simpa using hi)) primalConn (faceBypassTable G hh) (by have := table_euler G;omega)
    (fun _ _ inc present => all_edges G A inc present) hz
  have count := (List.filter_append_perm A (List.finRange M.faces.length)).length_eq
  simp only [List.length_append,List.length_finRange,←List.countP_eq_length_filter] at count
  change num A + num (fun i=> !A i) = M.faces.length at count
  have h₁ := vertex_partition G A
  have h₂ := edge_partition G A
  have h₃ := mixed_count G A
  have sphere := table_euler G
  rw [h₃] at h₂
  let B := fun i => !A i
  change num B + num (solid G A false) ≤ num (sideEdge (dual G) B)+1 at h
  change num (sideEdge (dual G) A)+num (sideEdge (dual G) B)+num (mixedVertex G A) = _ at h₂
  change num A + num B = _ at count
  omega

end DiskFullerene.EndEuler

namespace DiskFullerene.EndEuler
open Separation Dual

noncomputable def sectorCore {M} {G : IsDiskFullerene M h} {x y}
    (S : TriangleSide G (apex M) x y) (B : Bool) (f : Face M) : Bool := by
  classical
  exact decide (f ∈ diskInterior G) && faceSide S B f

private theorem dualNeighbors {M} (G : IsDiskFullerene M h) {e : Edge M} {a b : Face M}
    (cut : Across (dual G) e a b) : b ∈ dualRow G a := by
  have base : (dual G e).2 ∈ dualRow G (dual G e).1 :=
    (mem_row_iff _ _ _).mpr ⟨endpoints e,left_incident G (endpoints_mem e),
      left_incident G (dart_reverse G (endpoints_mem e))⟩
  rcases cut with eq|eq <;> rw [eq] at base
  · exact base
  · exact (dual_adj_symmetric G b a).mp base

/-- The complement of the strict interior of a sector is connected, in
the actual dual graph. Along an unrestricted dual walk, any step leaving
the chosen interior lands on the apex boundary; that vertex is reached
immediately from the apex. -/
theorem sector_complement_connected {M} {G : IsDiskFullerene M h} (hh : 3≤h) {x y}
    (S : TriangleSide G (apex M) x y) (B : Bool) (z : Face M) (hz : sectorCore S B z=false) :
    Walk (Adj (dual G) (fun t => sideEdge (dual G) (fun i=> !sectorCore S B i) t=true)) (apex M) z := by
  classical
  let root := apex M
  let A := sectorCore S B
  let R := Adj (dual G) (fun t => sideEdge (dual G) (fun i=> !A i) t=true)
  have hx := dualNeighbors G S.first
  have hy := dualNeighbors G S.last.symm
  have base : A root=false := by simp [A,sectorCore,root,mem_diskInterior]
  have join {a b : Face M} (ha : A a=false) (hb : A b=false) (nb : b∈dualRow G a) : R a b := by
    obtain ⟨d,di,dj⟩ := (mem_row_iff G a b).mp nb
    obtain ⟨e,eq⟩ := repr_dart G (incident_dart G di)
    have ac := crossTable G eq (Or.inl ⟨di,dj⟩)
    exact ⟨e,by rcases ac with he|he <;> simp [sideEdge,he,ha,hb],ac⟩
  have nf {i : Face M} (im : i ∈ diskInterior G) : i≠root ∧ i≠x ∧ i≠y := by
    have ⟨other,notBound⟩ := (mem_diskInterior G i).mp im
    exact ⟨other,fun eq => notBound (eq ▸ hx),fun eq => notBound (eq ▸ hy)⟩
  have frontier {a b : Face M} (ha : A a=true) (hb : A b=false) (nb : b∈dualRow G a) :
      b=root ∨ b ∈ dualRow G root := by
    by_cases br : b=root
    · exact .inl br
    by_cases cb : b ∈ dualRow G root
    · exact .inr cb
    have bin := (mem_diskInterior G b).mpr ⟨br,cb⟩
    have ⟨ain,ap⟩ := Bool.and_eq_true_iff.mp ha
    have ai : a ∈ diskInterior G := of_decide_eq_true ain
    have eq := S.edge_stays (nf ai) (nf bin) nb
    simp [A,sectorCore,faceSide,ai,bin,nf ai,nf bin,eq] at ha hb
    grind
  have path := liftDual G (K:=fun _=> True) (fun _ _ _ _ => trivial) (dual_connected G hh root z)
  change Walk R root z
  induction path with
  | refl => exact .refl
  | @step v z prev step ih =>
    obtain ⟨e,_,ac⟩ := step
    have nb := dualNeighbors G ac
    cases va : A v with
    | false => exact (ih va).step (join va hz nb)
    | true =>
      rcases frontier va hz nb with eq|boundary
      · exact eq ▸ .refl
      · exact .step .refl (join base hz boundary)

theorem nonsolid {M} (G : IsDiskFullerene M h) (hh : 3≤h) (A : Face M → Bool)
    {f : Face M} (chosen : A f=true) : ∃ v, solid G A false v=false := by
  obtain ⟨u,v,mem⟩ := face_dart G hh f
  have bounds := dart_endpoints G (incident_dart G mem)
  let t : Fin M.ord := ⟨u,bounds.1⟩
  refine ⟨t,?_⟩
  have nei := dart_iff.mp (incident_dart G mem)
  have m : v ∈ M.rows[t.val]'t.isLt := by simpa [MapData.adj,List.getElem?_eq_getElem bounds.1,t] using nei
  cases s : solid G A false t with
  | false => rfl
  | true =>
    have imp := List.all_eq_true.mp s v m
    simp [t,owner_eq G mem,chosen] at imp

/-- On either side of any actual chord, nonempty strict interior data
satisfy the Euler inequality needed in the finite core ear lemma. No
assumption of a region dissection or of connectedness of the core. -/
theorem sector_core_bound {M} {G : IsDiskFullerene M h} (hh : 3≤h) {x y}
    (S : TriangleSide G (apex M) x y) (B : Bool) (nonempty : ∃ z, sectorCore S B z=true) :
    num (sideEdge (dual G) (sectorCore S B))+1 ≤
      num (sectorCore S B) + num (solid G (sectorCore S B) true) := by
  obtain ⟨z,hz⟩ := nonempty
  exact induced_euler_bound G hh _ (by simp [sectorCore,mem_diskInterior])
    (nonsolid G hh _ hz) (sector_complement_connected hh S B)

end DiskFullerene.EndEuler
