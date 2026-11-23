import DiskFullerene.ConstructionWords

namespace DiskFullerene.PrimalSplice

def walkFrom (x : Nat) : Word → List Dart
  | [] => []
  | y::ys => (x,y)::walkFrom y ys

def walkDarts : Word → List Dart
  | [] => []
  | x::xs => walkFrom x xs

private theorem walk_append (x : Nat) (u v : Word) :
    walkFrom x (u++v) = walkFrom x u ++ walkFrom (u.getLastD x) v := by
  induction u generalizing x with
  | nil => rfl
  | cons a u ih => simp [walkFrom,ih,List.getLast?_cons]

private theorem sides_eq (x : Nat) (xs : Word) : sides (x::xs) =
    walkFrom x xs ++ [(xs.getLastD x,x)] := by
  have core (a b : Nat) (us : Word) : (a::us).zip (us++[b]) =
        walkFrom a us ++ [(us.getLastD a,b)] := by
    induction us generalizing a with
    | nil => rfl
    | cons u us ih => simp [walkFrom,List.getLast?_cons,ih]
  exact core x x xs

private theorem path_sn (w : Word) (ne : w ≠ []) (x : Nat) :
    walkDarts (w++[x]) = walkDarts w ++ [(w.getLastD 0,x)] := by
  cases w with
  | nil => contradiction
  | cons u us => simp [walkDarts,walk_append,walkFrom,List.getLast?_cons]

private theorem path_cn (w : Word) (ne : w≠[]) (x : Nat) :
    walkDarts (x::w) = (x,w.headD 0)::walkDarts w := by cases w <;> simp_all [walkDarts,walkFrom]

private theorem reverseWalk (w : Word) :
    walkDarts w.reverse = ((walkDarts w).map Prod.swap).reverse := by
  induction w with
  | nil => rfl
  | cons h t ih =>
    cases t with
    | nil => rfl
    | cons z zs =>
      rw [List.reverse_cons,path_sn _ (by simp) h,ih]
      simp [walkDarts,walkFrom,List.getLast?_cons]

private theorem cycle_eq (w : Word) (ne : w≠[]) :
    sides w = walkDarts w ++ [(w.getLastD 0,w.headD 0)] := by
  cases w with
  | nil => contradiction
  | cons a as => simp [sides_eq,walkDarts,List.getLast?_cons]

private theorem reverseCycle (w : Word) : (sides w.reverse).Perm ((sides w).map Prod.swap) := by
  cases w with
  | nil => exact .nil
  | cons x xs =>
    rw [cycle_eq _ (by simp),cycle_eq _ (by simp),reverseWalk,List.map_append]
    simp [List.getLast?_cons]
    exact List.Perm.append_right _ (List.reverse_perm _)

def OpenPatch.darts (p : OpenPatch) :=
  p.closed.flatMap sides ++ walkDarts p.w ++ walkDarts p.x ++ walkDarts p.y

private theorem revedFlat (ws : List Word) :
    ((ws.map List.reverse).flatMap sides).Perm ((ws.flatMap sides).map Prod.swap) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [List.map_append] using (reverseCycle w).append ih

private theorem countSwap (xs : List Dart) (x y : Nat) :
    (xs.map Prod.swap).count (x,y) = xs.count (y,x) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases a with
    | mk b c => simp [List.count_cons,ih,Bool.beq_eq_decide_eq,and_comm]

private theorem path_join (a b : Word) (ha : a ≠ []) (hb : b ≠ []) :
    walkDarts (a++b) = walkDarts a ++ (a.getLastD 0,b.headD 0)::walkDarts b := by
  cases a with
  | nil => contradiction
  | cons x xs =>
    cases b with
    | nil => contradiction
    | cons y ys => simp [walkDarts,walk_append,walkFrom,List.getLast?_cons]

structure ArcEnds (w : Word) (a b : Nat) : Prop where
  start : w.head? = some a
  finish : w.getLast? = some b

theorem ArcEnds.nonempty (h : ArcEnds w a b) : w≠[] := by
  intro eq; have e := h.start; simp [eq] at e

structure OpenPatch.Ports (p : OpenPatch) (a b c : Nat) : Prop where
  w : ArcEnds p.w a b
  x : ArcEnds p.x b c
  y : ArcEnds p.y c a

theorem portsInitial : leftPatch.Ports 21 17 10 ∧ rightPatch.Ports 17 21 10 := by
  constructor <;> constructor <;> constructor <;> rfl

theorem OpenPatch.Ports.step {p : OpenPatch} (h : p.Ports a b c) (m : Nat) :
    (p.step m).Ports (m+2) a (m+3) := by
  have nw := h.w.nonempty
  obtain ⟨⟨w0,w1⟩,⟨x0,x1⟩,⟨y0,y1⟩⟩ := h
  have ny : p.y≠[] := fun eq => by simp [eq] at y0
  constructor <;> constructor <;>
    simp [OpenPatch.step,List.head?_append,List.getLast?_cons_of_ne_nil (xs:=p.w.reverse) (by simpa using nw),w0,y1]

def newDarts (b c P S : Nat) : List Dart := [(b,P),(P,b),(c,S),(S,c),(P,S),(S,P)]

/-- Enumerating directed sides after a strip step adds the six darts of the
three new edges and reverses the old facial orientations. -/
theorem stepDarts (p : OpenPatch) (h : p.Ports a b c) (m : Nat) :
    (p.step m).darts.Perm (p.darts.map Prod.swap ++ newDarts b c (m+2) (m+3)) := by
  apply List.perm_iff_count.mpr
  rintro ⟨i,j⟩
  have ne := h.x.nonempty
  have cw := (revedFlat ((p.x++[m+3,m+2])::p.closed)).count_eq (i,j)
  rw [countSwap] at cw
  have cx := cycle_eq (p.x++[m+3,m+2]) (by simp)
  rw [path_join _ _ ne (by simp)] at cx
  simp [List.head?_append,h.x.start,h.x.finish,walkDarts,walkFrom] at cx
  simp only [List.flatMap_cons,List.count_append,cx] at cw
  simp only [OpenPatch.step,OpenPatch.darts,List.count_append,countSwap,cw,reverseWalk,
    List.count_reverse,path_sn _ h.w.nonempty,path_cn _ h.y.nonempty]
  simp [List.count_cons,newDarts,walkDarts,walkFrom,
    h.w.finish,h.y.start, Bool.beq_eq_decide_eq,and_comm]
  omega

theorem openPorts (k : Nat) : (openWords k).Ports
    ((partialArm k).port 0) ((partialArm k).port 1) ((partialArm k).port 2) := by
  induction k with
  | zero => exact portsInitial.1
  | succ k ih =>
    obtain ⟨p0,p1,p2⟩ := portAdvance k
    rw [p0,p1,p2]; exact ih.step _

structure ExactDarts (ds : List Dart) (E : Nat → Nat → Prop) : Prop where
  unique : ds.Nodup
  edges : ∀ u v, (u,v) ∈ ds ↔ E u v

private theorem baseDarts (p : OpenPatch) (which : p=leftPatch ∨ p=rightPatch) :
    ExactDarts p.darts ((partialArm 0).interiorEdge) := by
  have data : p.darts.Nodup ∧
      (p.darts.all (fun d => decide (d.1<22 ∧ d.2<22))) ∧
      ∀ a b : Fin 22, ((a.val,b.val) ∈ p.darts ↔ capRows.adj a.val b.val ∧ a.val≠16 ∧ b.val≠16) := by
    rcases which with rfl|rfl <;> unfold MapData.adj <;> decide
  refine ⟨data.1,?_⟩
  intro u v; rw [partialBase]
  constructor
  · intro h
    have ⟨a,b⟩ := of_decide_eq_true (List.all_eq_true.mp data.2.1 _ h)
    exact (data.2.2 ⟨u,a⟩ ⟨v,b⟩).mp h
  · intro h
    have ⟨a,b⟩ := capBounds h.1
    exact (data.2.2 ⟨u,a⟩ ⟨v,b⟩).mpr h

private theorem newNodup (hb : b<P) (hc : c<P) (lt : P<S) :
    (newDarts b c P S).Nodup := by
  simp [newDarts,Prod.mk.injEq]
  omega

theorem openCoverage (k : Nat) : ExactDarts (openWords k).darts (partialArm k).interiorEdge := by
  induction k with
  | zero => exact baseDarts leftPatch (Or.inl rfl)
  | succ k ih =>
    let A := partialArm k
    let m := 22+4*k
    have perm := stepDarts (openWords k) (openPorts k) m
    have b := partialBound k _ (A.portsValid 1).1
    have c := partialBound k _ (A.portsValid 2).1
    change A.port 1 < m at b; change A.port 2 < m at c
    obtain ⟨uniq,edge⟩ := ih
    have disj (d : Dart) (old : d ∈ (openWords k).darts.map Prod.swap)
        (fresh : d ∈ newDarts (A.port 1) (A.port 2) (m+2) (m+3)) : False := by
      obtain ⟨⟨u,v⟩,uv,rfl⟩ := List.mem_map.mp old
      obtain ⟨hu,hv⟩ := A.edgeBound ((edge u v).mp uv)
      have smallu := partialBound k u hu.1
      have smallv := partialBound k v hv.1
      change u<m at smallu; change v<m at smallv
      simp [newDarts] at fresh
      omega
    constructor
    · apply perm.nodup_iff.mpr
      apply List.nodup_append.mpr
      exact ⟨List.pairwise_map.mpr (uniq.imp (fun {a b} h (e : a.swap=b.swap) => h (by simpa using congrArg Prod.swap e))),
        newNodup (b:=A.port 1) (c:=A.port 2) (P:=m+2) (S:=m+3) (by omega) (by omega) (by omega),fun d hd e he eq => disj d hd (eq ▸ he)⟩
    · intro u v
      have stage := partialAdvance k u v
      dsimp only at stage
      rw [stage]
      change (u,v) ∈ ((openWords k).step m).darts ↔ _
      rw [perm.mem_iff,List.mem_append]
      change (_ ∨ _) ↔ (A.interiorEdge u v ∨ _)
      apply or_congr_left
      simp only [List.mem_map]
      constructor
      · rintro ⟨⟨a,b⟩,hab,eq⟩; cases eq; exact A.interiorSymm ((edge a b).mp hab)
      · intro h; exact ⟨(v,u),(edge v u).mpr (A.interiorSymm h),rfl⟩

private theorem cycleJoin (l r : Word) (hl : ArcEnds l a b) (hr : ArcEnds r c d) (i j : Nat) :
    (sides (l++r.reverse)).count (i,j) =
      (walkDarts l).count (i,j) + (walkDarts r).count (j,i) + [(b,d),(c,a)].count (i,j) := by
  have ne := hl.nonempty
  have nr : r.reverse≠[] := by simpa using hr.nonempty
  rw [cycle_eq _ (by simp [ne]),path_join l r.reverse ne nr, reverseWalk]
  simp [List.count_append,List.count_cons,countSwap,List.getLast?_append,List.head?_append,
    hl.start,hl.finish,hr.start,hr.finish]
  omega

def bridges (a b c A B C : Nat) : List Dart := [(a,A),(A,a),(b,B),(B,b),(c,C),(C,c)]

theorem joinDarts (l r : OpenPatch) (hl : l.Ports a b c) (hr : r.Ports A B C) :
    (((l.join r).1 :: (l.join r).2).flatMap sides).Perm
      (l.darts ++ r.darts.map Prod.swap ++ bridges a b c A B C) := by
  apply List.perm_iff_count.mpr
  rintro ⟨i,j⟩
  have rc := (revedFlat r.closed).count_eq (i,j)
  rw [countSwap] at rc
  simp only [OpenPatch.join,List.flatMap_cons,List.flatMap_append,List.count_append,
    cycleJoin _ _ hl.w hr.w i j,cycleJoin _ _ hl.x hr.x i j,cycleJoin _ _ hl.y hr.y i j,
    rc,countSwap,OpenPatch.darts]
  simp [bridges,List.count_cons]
  omega

private theorem mapFrom (f : Nat → Nat) (x : Nat) (xs : Word) :
    walkFrom (f x) (xs.map f) = (walkFrom x xs).map (Prod.map f f) := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih => simp [walkFrom,ih]

private theorem mapWalk (f : Nat → Nat) (w : Word) :
    walkDarts (w.map f) = (walkDarts w).map (Prod.map f f) := by
  cases w <;> simp [walkDarts,mapFrom]

private theorem mapCycle (f : Nat → Nat) (w : Word) :
    sides (w.map f) = (sides w).map (Prod.map f f) := by
  cases w with
  | nil => rfl
  | cons a as =>
    simpa [sides,List.map_append] using (List.zip_map (f:=f) (g:=f) (l₁:=a::as) (l₂:=as++[a]))

private theorem raiseDarts (p : OpenPatch) (m : Nat) :
    (p.raise m).darts = p.darts.map (Prod.map (m+·) (m+·)) := by
  have flat (ws : List Word) : (ws.map (List.map (m+·))).flatMap sides =
      (ws.flatMap sides).map (Prod.map (m+·) (m+·)) := by
    induction ws with
    | nil => rfl
    | cons w ws ih => simp [mapCycle,List.map_append,ih]
  simp [OpenPatch.raise,OpenPatch.darts,List.map_append,mapWalk,flat]

private theorem raisePorts (p : OpenPatch) (h : p.Ports a b c) (m : Nat) :
    (p.raise m).Ports (m+a) (m+b) (m+c) := by
  obtain ⟨⟨wa,wb⟩,⟨xb,xc⟩,⟨yc,ya⟩⟩ := h
  constructor <;> constructor <;> simp [OpenPatch.raise,wa,wb,xb,xc,yc,ya]

private def endPatch (n : Nat) := rightPatch.raise (22+4*(n+2))

private theorem endPorts (n : Nat) : (endPatch n).Ports
    ((rightArm n).port 0) ((rightArm n).port 1) ((rightArm n).port 2) :=
  raisePorts _ portsInitial.2 _

private theorem endCoverage (n : Nat) : ExactDarts (endPatch n).darts (rightArm n).interiorEdge := by
  let m := 22+4*(n+2)
  obtain ⟨unique,edge⟩ := baseDarts rightPatch (Or.inr rfl)
  change ExactDarts (rightPatch.raise m).darts _
  rw [raiseDarts]
  constructor
  · apply List.pairwise_map.mpr
    apply unique.imp
    rintro ⟨a,b⟩ ⟨c,d⟩ ne eq; simp at eq; exact ne (Prod.ext eq.1 eq.2)
  · intro u v
    rw [rightEdge]
    change _ ↔ m≤u ∧ m≤v ∧ capRows.adj (u-m) (v-m) ∧ u≠m+16 ∧ v≠m+16
    constructor
    · intro h
      obtain ⟨⟨a,b⟩,md,eq⟩ := List.mem_map.mp h
      have src := (partialBase a b).mp ((edge a b).mp md)
      cases eq; simpa [Nat.add_left_cancel_iff] using src
    · rintro ⟨lu,lv,adj,nu,nv⟩
      apply List.mem_map.mpr
      refine ⟨(u-m,v-m),(edge _ _).mpr ((partialBase ..).mpr ⟨adj,by omega,by omega⟩),?_⟩
      apply Prod.ext <;> simp <;> omega

private def portDarts (A B : Arm) :=
  bridges (A.port 0) (A.port 1) (A.port 2) (B.port 0) (B.port 1) (B.port 2)

private theorem portDarts_mem (A B : Arm) (u v : Nat) : (u,v) ∈ portDarts A B ↔
    (∃ i, u=A.port i ∧ v=B.port i) ∨ (∃ i, u=B.port i ∧ v=A.port i) := by
  simp only [portDarts,bridges,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq]
  constructor
  · rintro (e|e|e|e|e|e)
    all_goals first | exact Or.inl ⟨_,e⟩ | exact Or.inr ⟨_,e⟩
  · rintro (⟨i,rfl,rfl⟩|⟨i,rfl,rfl⟩)
    all_goals
      have cases_i : i=0 ∨ i=1 ∨ i=2 := by
        have := i.isLt
        by_cases h : i.val=0
        · exact Or.inl (Fin.ext h)
        by_cases h : i.val=1
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Fin.ext (by omega)))
      rcases cases_i with rfl|rfl|rfl <;> simp

private theorem mergeCovered (A B : Arm) (disj : ∀ v, A.vertex v → ¬B.vertex v)
    (ls rs : List Dart) (L : ExactDarts ls A.interiorEdge) (R : ExactDarts rs B.interiorEdge) :
    ExactDarts (ls ++ rs.map Prod.swap ++ portDarts A B) (Edge A B) := by
  have rev u v : (u,v) ∈ rs.map Prod.swap ↔ B.interiorEdge u v := by
    constructor
    · intro h
      obtain ⟨⟨a,b⟩,ab,eq⟩ := List.mem_map.mp h; cases eq
      exact B.interiorSymm ((R.edges ..).mp ab)
    · intro h
      exact List.mem_map.mpr ⟨(v,u),(R.edges ..).mpr (B.interiorSymm h),rfl⟩
  have dist i j : A.port i ≠ B.port j :=
    fun e => disj _ (e ▸ (A.portsValid i).1) (B.portsValid j).1
  have dist' i j : B.port j ≠ A.port i := (dist i j).symm
  have injA (i j) : A.port i=A.port j ↔ i=j := ⟨fun h => A.portsDifferent h,congrArg _⟩
  have injB (i j) : B.port i=B.port j ↔ i=j := ⟨fun h => B.portsDifferent h,congrArg _⟩
  have nb : (portDarts A B).Nodup := by simp [portDarts,bridges,dist,dist',injA,injB]
  have nr : (rs.map Prod.swap).Nodup :=
    List.pairwise_map.mpr (R.unique.imp (fun {a b} n (e : a.swap=b.swap) => n (by simpa using congrArg Prod.swap e)))
  have nd : (ls++rs.map Prod.swap).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨L.unique,nr,?_⟩
    rintro ⟨a,b⟩ mem _ rmem rfl
    exact disj a (A.edgeBound ((L.edges ..).mp mem)).1.1 (B.edgeBound ((rev ..).mp rmem)).1.1
  constructor
  · apply List.nodup_append.mpr
    refine ⟨nd,nb,?_⟩
    rintro ⟨a,b⟩ mem _ mb rfl
    rcases List.mem_append.mp mem with left|right
    · have h := A.edgeBound ((L.edges ..).mp left)
      rcases (portDarts_mem ..).mp mb with ⟨i,_,rfl⟩|⟨i,rfl,_⟩
      · exact disj _ h.2.1 (B.portsValid i).1
      · exact disj _ h.1.1 (B.portsValid i).1
    · have h := B.edgeBound ((rev ..).mp right)
      rcases (portDarts_mem ..).mp mb with ⟨i,rfl,_⟩|⟨i,_,rfl⟩
      · exact disj _ (A.portsValid i).1 h.1.1
      · exact disj _ (A.portsValid i).1 h.2.1
  · intro u v
    simp only [List.mem_append,L.edges,rev,portDarts_mem]
    constructor
    · rintro ((a|b)|e)
      · exact .left (A.edgeBound a).1 (A.edgeBound a).2 a.1
      · exact .right (B.edgeBound b).1 (B.edgeBound b).2 b.1
      · rcases e with ⟨i,rfl,rfl⟩|⟨i,rfl,rfl⟩
        · exact .bridge i
        · exact .back i
    · intro e; cases e with
      | left a b e => exact Or.inl (Or.inl ⟨e,a.2,b.2⟩)
      | right a b e => exact Or.inl (Or.inr ⟨e,a.2,b.2⟩)
      | bridge i => exact Or.inr (Or.inl ⟨i,rfl,rfl⟩)
      | back i => exact Or.inr (Or.inr ⟨i,rfl,rfl⟩)

/-- The actual oriented facial boundary words use every directed edge of the
actual cubic splice graph once, across all h = n+12. -/
theorem primalCoverage (n : Nat) :
    ExactDarts (((primalWords n).1 :: (primalWords n).2).flatMap sides) (primalEdge n) := by
  let L := openWords (n+2)
  let R := endPatch n
  have perm := joinDarts L R (openPorts (n+2)) (endPorts n)
  have data := mergeCovered (leftArm n) (rightArm n) (fun v low high =>
    Nat.not_le_of_lt (partialBound (n+2) v low) high.1)
    L.darts R.darts (openCoverage (n+2)) (endCoverage n)
  exact ⟨perm.nodup_iff.mpr data.unique,fun u v => perm.mem_iff.trans (data.edges u v)⟩

end DiskFullerene.PrimalSplice
