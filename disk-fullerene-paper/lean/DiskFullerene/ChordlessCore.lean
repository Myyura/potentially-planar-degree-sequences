import DiskFullerene.DualCore

namespace DiskFullerene.Dual
open Separation

/-- A facial neighbor list of length five or six, read cyclically starting
at a prescribed face. -/
structure Reroot {α : Type} (C : List α) (root : α) where
  atPos : Nat → α
  first : atPos 0 = root
  last : atPos C.length = root
  inject : ∀ i j, i<C.length → j<C.length → atPos i = atPos j → i=j
  covers : ∀ y, y ∈ C ↔ ∃ k, k<C.length ∧ atPos k = y
  side : ∀ k<C.length, (atPos k, atPos (k+1)) ∈ sides C

private theorem posFacts {n : Nat} (sz : n=5 ∨ n=6) :
    (∀ a b : Fin n, ∃ c : Fin n, (a.val+c.val)%n = b.val) ∧
    (∀ a b c : Fin n, (a.val+b.val)%n = (a.val+c.val)%n → b=c) ∧
    (∀ a k : Fin n, next n ((a.val+k.val)%n) = (a.val+(k.val+1))%n) := by
  rcases sz with rfl|rfl <;> decide

theorem reroot {C : List α} (nd : C.Nodup) (sz : C.length=5 ∨ C.length=6)
    (m : x ∈ C) : Nonempty (Reroot C x) := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp m
  have npos : 0 < C.length := by omega
  let v (j : Nat) := C[(i+j)%C.length]'(Nat.mod_lt _ npos)
  obtain ⟨sur,inj,step⟩ := posFacts sz
  refine ⟨⟨v,by simp [v,Nat.mod_eq_of_lt hi,he],by simpa [v,Nat.add_mod_right,Nat.mod_eq_of_lt hi] using he,?_,?_,?_⟩⟩
  · intro a b ha hb eq
    have e := index_eq nd (Nat.mod_lt _ npos) (Nat.mod_lt _ npos) eq
    exact congrArg Fin.val (inj ⟨i,hi⟩ ⟨a,ha⟩ ⟨b,hb⟩ e)
  · intro y
    constructor
    · intro hy
      obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp hy
      obtain ⟨k,ek⟩ := sur ⟨i,hi⟩ ⟨j,hj⟩
      exact ⟨k.val,k.isLt,by simpa [v,ek] using eq⟩
    · rintro ⟨k,_,rfl⟩; exact List.getElem_mem _
  · intro k hk
    let j := (i+k)%C.length
    have hj : j < C.length := Nat.mod_lt _ npos
    have eq := step ⟨i,hi⟩ ⟨k,hk⟩
    exact List.mem_iff_getElem.mpr ⟨j,by simpa [sides_size] using hj,by
      rw [side_at C j hj]; simp [j, v, eq]⟩

def InteriorAdj {M : MapData} (G : IsDiskFullerene M h) (a b : Face M) : Prop :=
  a ∈ diskInterior G ∧ b ∈ diskInterior G ∧ b ∈ dualRow G a

theorem InteriorAdj.symm {M : MapData} (G : IsDiskFullerene M h) :
    ∀ a b, InteriorAdj G a b → InteriorAdj G b a :=
  fun _ _ e => ⟨e.2.1,e.1,(dual_adj_symmetric G _ _).1 e.2.2⟩

theorem endsOfWordSide {α} {C : List α} {a b : α} (xy : (a,b) ∈ sides C) :
    a ∈ C ∧ b ∈ C := by
  obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp xy
  rw [sides_size] at hk; rw [side_at C k hk] at he
  exact ⟨(Prod.mk.inj he).1 ▸ List.getElem_mem hk, (Prod.mk.inj he).2 ▸ List.getElem_mem (next_bound hk)⟩

/-- The consecutive interior vertices exposed by one boundary face. Node 0
and node steps are the first and last vertices, so this piece of the outer
walk of the induced graph has precisely steps edge-sides. -/
structure BoundaryArc {M : MapData} (G : IsDiskFullerene M h) (x : Face M) where
  steps : Nat
  length_eq : steps + 4 = (dualRow G x).length
  node : Nat → Face M
  entry : Face M
  exitVertex : Face M
  entryRim : IsBoundary G entry
  exitRim : IsBoundary G exitVertex
  fromApex : (apex M,entry) ∈ sides (dualRow G x)
  toApex : (exitVertex,apex M) ∈ sides (dualRow G x)
  startSide : (entry,node 0) ∈ sides (dualRow G x)
  endSide : (node steps,exitVertex) ∈ sides (dualRow G x)
  stepSide : ∀ k < steps, (node k,node (k+1)) ∈ sides (dualRow G x)
  inside : ∀ k ≤ steps, node k ∈ diskInterior G
  complete : ∀ y ∈ dualRow G x, y ∈ diskInterior G → ∃ k ≤ steps, node k = y

private structure Fan {M : MapData} (G : IsDiskFullerene M h) (x : Face M) where
  center : Face M
  inside : center ∈ diskInterior G
  neighbor : center ∈ dualRow G x
  reaches : ∀ v ∈ dualRow G x, v ∈ diskInterior G → Walk (InteriorAdj G) center v
  shared : ∀ y ∈ dualRow G x, IsBoundary G y → ∃ z, z ∈ dualRow G x ∧ z ∈ dualRow G y ∧ z ∈ diskInterior G
  arc : BoundaryArc G x

private theorem makeFan {M : MapData} (G : IsDiskFullerene M h) (hh : 3 ≤ h)
    (hc : ¬ HasChord G) {x : Face M} (xc : IsBoundary G x) : Nonempty (Fan G x) := by
  let C := dualRow G (apex M)
  have nx : x ≠ apex M := fun e => row_no_loop G hh _ (e ▸ xc)
  have size := inner_degree G nx
  change (dualRow G x).length=5 ∨ (dualRow G x).length=6 at size
  have adjroot := (dual_adj_symmetric G _ _).1 xc
  obtain ⟨w⟩ := reroot (row_nodup G (noRepeatOnSphere G hh) x) size adjroot
  let last := (dualRow G x).length-1
  have lastBound : last < (dualRow G x).length := by dsimp [last]; omega
  have finish : last+1 = (dualRow G x).length := by dsimp [last]; omega
  have s1 := w.side 0 (by omega)
  have sl := w.side last lastBound
  rw [w.first] at s1
  rw [finish,w.last] at sl
  have s1' := (turn_triangle G s1).1
  have sl' := (turn_triangle G sl).2
  have pC := (endsOfWordSide s1').1
  have qC := (endsOfWordSide sl').2
  have npq : w.atPos 1 ≠ w.atPos last := by
    intro e
    have := w.inject _ _ (by omega) lastBound e
    dsimp [last] at this; omega
  obtain ⟨bnd,ln,link⟩ := boundary_cycle G hh
  obtain ⟨p,_,q,_,_,_,_,only⟩ := cycle_at bnd (by omega) xc
  have pside := only _ (Or.inr s1')
  have qside := only _ (Or.inl sl')
  have eitherBoundary {y : Face M} (a : y ∈ dualRow G x) (rim : IsBoundary G y) :
      y = w.atPos 1 ∨ y = w.atPos last := by
    have e : OnCycle C x y := by
      by_cases forward : (x,y) ∈ sides C
      · exact Or.inl forward
      by_cases back : (y,x) ∈ sides C
      · exact Or.inr back
      exact False.elim (hc ⟨x,xc,y,rim,a,forward,back⟩)
    have xy := only _ e
    grind
  have interiorAt (k : Nat) (low : 2 ≤ k) (high : k < last) : w.atPos k ∈ diskInterior G := by
    have kr := (w.covers _).2 ⟨k, by omega, rfl⟩
    rw [mem_diskInterior]
    constructor
    · intro e
      have z := w.inject k 0 (by omega) (by omega) (e.trans w.first.symm)
      omega
    · intro rim
      rcases eitherBoundary kr rim with e|e
      · have z := w.inject k 1 (by omega) (by omega) e; omega
      · have z := w.inject k last (by omega) (by omega) e; omega
  have lastBig : 3 < last := by dsimp [last]; omega
  have home := interiorAt 2 (by decide) (by omega)
  refine ⟨⟨w.atPos 2,home,(w.covers _).2 ⟨2,by omega,rfl⟩,?_,?_,?_⟩⟩
  · intro y yr yi
    obtain ⟨k,hk,rfl⟩ := (w.covers y).1 yr
    have facts := (mem_diskInterior G _).1 yi
    have lo : 2 ≤ k := by
      by_cases z : k=0
      · subst k; exact False.elim (facts.1 w.first)
      by_cases o : k=1
      · subst k; exact False.elim (facts.2 pC)
      omega
    have hi : k < last := by
      have ne : k ≠ last := fun e => facts.2 (e ▸ qC)
      dsimp [last] at *; omega
    suffices go : ∀ k, 2≤k → k<last → Walk (InteriorAdj G) (w.atPos 2) (w.atPos k) from go k lo hi
    intro k lo hi
    induction k with
    | zero => omega
    | succ k ih =>
      by_cases orig : k+1=2
      · rw [orig]; exact .refl
      · have w1 := interiorAt k (by omega) (by omega)
        have step := cyclic_link G x (w.side k (by omega))
        exact (ih (by omega) (by omega)).step ⟨w1,interiorAt _ lo hi,step⟩
  · intro y hy rim
    rcases eitherBoundary hy rim with e|e
    · subst y
      exact ⟨_,(w.covers _).2 ⟨2,by omega,rfl⟩,cyclic_link G x (w.side 1 (by omega)),home⟩
    · subst y
      have pos := interiorAt (last-1) (by omega) (by omega)
      have step := cyclic_link G x (w.side (last-1) (by omega))
      have eq : last-1+1=last := by omega
      rw [eq] at step
      exact ⟨_,(w.covers _).2 ⟨last-1,by omega,rfl⟩,(dual_adj_symmetric G _ _).1 step,pos⟩

  · let steps := (dualRow G x).length-4
    have length_eq : steps+4 = (dualRow G x).length := by dsimp [steps]; omega
    have end_eq : steps+2+1 = last := by dsimp [last,steps]; omega
    refine ⟨steps,length_eq,fun k => w.atPos (k+2),w.atPos 1,w.atPos last,
      pC,qC,s1,sl,w.side 1 (by omega),?_,?_,?_,?_⟩
    · have e := w.side (steps+2) (by omega)
      simpa [end_eq] using e
    · intro j hj
      exact w.side (j+2) (by omega)
    · intro j hj
      apply interiorAt <;> omega
    · intro y yr yi
      obtain ⟨k,hk,rfl⟩ := (w.covers y).1 yr
      have sep := (mem_diskInterior G _).1 yi
      have ne0 : k≠0 := fun e => sep.1 (e ▸ w.first)
      have ne1 : k≠1 := fun e => sep.2 (e ▸ pC)
      have neL : k≠last := fun e => sep.2 (e ▸ qC)
      exact ⟨k-2,by omega,congrArg w.atPos (by omega)⟩

theorem traverseWord {α β : Type} (C : List α) (f : α → β) (R : β → β → Prop)
    (symm : ∀ x y, R x y → R y x)
    (step : ∀ x y, (x,y) ∈ sides C → Walk R (f x) (f y))
    {x y : α} (hx : x ∈ C) (hy : y ∈ C) : Walk R (f x) (f y) := by
  have start {i : Nat} (hi : i<C.length) :
      Walk R (f (C[0]'(by omega))) (f C[i]) := by
    induction i with
    | zero => exact .refl
    | succ i ih =>
      have e : (C[i]'(by omega),C[i+1]) ∈ sides C := List.mem_iff_getElem.mpr
        ⟨i,by simp [sides_size]; omega, by rw [side_at C i (by omega)]; simp [next,hi]⟩
      exact (ih (by omega)).trans (step _ _ e)
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hy
  exact ((start hi).symm symm).trans (start hj)

/-- For an actual chordless dual disk, deletion of its entire boundary and
the apex leaves a connected induced graph. Every vertex in a detour lies in
the strict interior. -/
theorem interior_connected {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (hc : ¬HasChord G) {u v : Face M} (hu : u ∈ diskInterior G) (hv : v ∈ diskInterior G) :
    Walk (InteriorAdj G) u v := by
  classical
  let C := dualRow G (apex M)
  let fan (x : Face M) (bx : IsBoundary G x) := Classical.choice (makeFan G hh hc bx)
  let proxy (x : Face M) := if bx : IsBoundary G x then (fan x bx).center else x
  have isProxy (x : Face M) (bx : IsBoundary G x) : proxy x = (fan x bx).center := by simp [proxy,bx]
  have isInside (x : Face M) (ix : x ∈ diskInterior G) : proxy x = x :=
    by have out := ((mem_diskInterior G x).1 ix).2; simp [proxy,IsBoundary,out]
  have neither (x : Face M) (nx : x ≠ apex M) (off : ¬IsBoundary G x) :
      x ∈ diskInterior G := (mem_diskInterior G x).2 ⟨nx,off⟩
  have nonAp {x y : Face M} (nx : x ≠ apex M) (ny : y ≠ apex M) (xy : y ∈ dualRow G x) :
      Walk (InteriorAdj G) (proxy x) (proxy y) := by
    have yx := (dual_adj_symmetric G _ _).1 xy
    by_cases bx : IsBoundary G x <;> by_cases byy : IsBoundary G y
    · obtain ⟨z,zx,zy,zi⟩ := (fan x bx).shared y xy byy
      rw [isProxy _ bx,isProxy _ byy]
      exact ((fan x bx).reaches z zx zi).trans (((fan y byy).reaches z zy zi).symm (InteriorAdj.symm G))
    · have iy := neither y ny byy
      rw [isInside _ iy,isProxy _ bx]
      exact (fan x bx).reaches y xy iy
    · have ix := neither x nx bx
      rw [isInside _ ix,isProxy _ byy]
      exact ((fan y byy).reaches x yx ix).symm (InteriorAdj.symm G)
    · have ix := neither x nx bx; have iy := neither y ny byy
      rw [isInside _ ix,isInside _ iy]
      exact .step .refl ⟨ix,iy,xy⟩
  have napex {x : Face M} (hx : IsBoundary G x) : x ≠ apex M :=
    fun eq => row_no_loop G hh _ (eq ▸ hx)
  obtain ⟨_,len,cycle⟩ := boundary_cycle G hh
  let first := C[0]'(by change 0 < (dualRow G (apex M)).length; omega)
  have firstC : first ∈ C := List.getElem_mem _
  have rim {x y : Face M} (hx : x ∈ C) (hy : y ∈ C) : Walk (InteriorAdj G) (proxy x) (proxy y) :=
    traverseWord C proxy _ (InteriorAdj.symm G)
      (fun _ _ e => nonAp (napex (endsOfWordSide e).1) (napex (endsOfWordSide e).2) (cycle _ _ e)) hx hy
  let lift (x : Face M) := if x=apex M then proxy first else proxy x
  have liftStep {x y : Face M} (xy : y ∈ dualRow G x) : Walk (InteriorAdj G) (lift x) (lift y) := by
    by_cases ax : x=apex M
    · subst x
      have yn := napex xy
      simpa [lift,yn] using (rim firstC xy)
    by_cases ay : y=apex M
    · subst y
      have xc := (dual_adj_symmetric G _ _).1 xy
      simpa [lift,ax] using (rim xc firstC)
    simpa [lift,ax,ay] using nonAp ax ay xy
  have liftPath (a b : Face M) (p : Walk (Step M (fun _ => True)) a b) :
      Walk (InteriorAdj G) (lift a) (lift b) := by
    induction p with
    | refl => exact .refl
    | step _ e ih =>
      obtain ⟨d,_,de|de⟩ := e
      · exact ih.trans (liftStep ((mem_row_iff G _ _).2 ⟨d,de⟩))
      · exact ih.trans (liftStep ((dual_adj_symmetric G _ _).1 ((mem_row_iff G _ _).2 ⟨d,de⟩)))
  have result := liftPath _ _ (dual_connected G hh u v)
  simpa [lift, (mem_diskInterior G u).mp hu |>.1, (mem_diskInterior G v).mp hv |>.1,
    isInside u hu, isInside v hv] using result

/-- The outer contour of the induced interior graph, split at successive
vertices of the surrounding boundary. -/
noncomputable def boundaryArc {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    (hc : ¬HasChord G) (x : Face M) (bx : IsBoundary G x) : BoundaryArc G x :=
  (Classical.choice (makeFan G hh hc bx)).arc

theorem same_next_word {C : List α} (nd : C.Nodup) {x a b : α}
    (xa : (x,a) ∈ sides C) (xb : (x,b) ∈ sides C) : a = b := by
  obtain ⟨i,hi,ei⟩ := List.mem_iff_getElem.mp xa
  obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp xb
  rw [sides_size] at hi hj; rw [side_at C i hi] at ei; rw [side_at C j hj] at ej
  have eq := index_eq nd hi hj ((Prod.mk.inj ei).1.trans (Prod.mk.inj ej).1.symm)
  subst j; exact (Prod.mk.inj ei).2.symm.trans (Prod.mk.inj ej).2

/-- Consecutive pieces agree at their common endpoint, including the
last-to-first join. The identification follows from the actual rotations. -/
theorem contour_closes {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h) {x y : Face M}
    (xy : (x,y) ∈ sides (dualRow G (apex M))) (A : BoundaryArc G x) (B : BoundaryArc G y) :
    A.node A.steps = B.node 0 := by
  have eA := same_next_word (row_nodup G (noRepeatOnSphere G hh) _) (turn_triangle G A.toApex).2 xy
  have eB := same_next_word (row_nodup G (noRepeatOnSphere G hh) _) B.fromApex (turn_triangle G xy).2
  have endSide : (A.node A.steps,y) ∈ sides (dualRow G x) := eA ▸ A.endSide
  have startSide : (x,B.node 0) ∈ sides (dualRow G y) := eB ▸ B.startSide
  exact same_next_word (row_nodup G (noRepeatOnSphere G hh) _) (turn_triangle G endSide).2 startSide

/-- Every consecutive interior-interior pair in a boundary link occurs in
its contour piece. Conversely each recorded step is such a pair. -/
theorem contour_side_iff {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h)
    {x u v : Face M} (A : BoundaryArc G x) :
    (∃ j<A.steps, A.node j=u ∧ A.node (j+1)=v) ↔
      ((u,v) ∈ sides (dualRow G x) ∧ u ∈ diskInterior G ∧ v ∈ diskInterior G) := by
  constructor
  · rintro ⟨j,hj,rfl,rfl⟩
    exact ⟨A.stepSide j hj,A.inside _ (by omega), A.inside _ (by omega)⟩
  · rintro ⟨side,iu,iv⟩
    obtain ⟨j,hj,eq⟩ := A.complete u (endsOfWordSide side).1 iu
    subst u
    have nd := row_nodup G (noRepeatOnSphere G hh) x
    by_cases eq : j=A.steps
    · subst j
      have same := same_next_word nd side A.endSide
      exact False.elim (((mem_diskInterior G v).1 iv).2 (same ▸ A.exitRim))
    · have lt : j<A.steps := by omega
      exact ⟨j,lt,rfl,same_next_word nd (A.stepSide j lt) side⟩

noncomputable def contourLength {M : MapData} (G : IsDiskFullerene M h) :=
  ((dualRow G (apex M)).map fun x => (dualRow G x).length - 4).sum

/-- The total counts one step for a pentagonal boundary face and two for a
hexagonal boundary face. -/
theorem contour_length_eq {M : MapData} (G : IsDiskFullerene M h) (hh : 3≤h) :
    contourLength G = h + ((dualRow G (apex M)).filter (fun x => (dualRow G x).length == 6)).length := by
  have fan (xs : List (Face M)) (good : ∀ x ∈ xs, x ≠ apex M) :
      (xs.map (fun x => (dualRow G x).length-4)).sum =
        xs.length + (xs.filter (fun x => (dualRow G x).length == 6)).length := by
    induction xs with
    | nil => simp
    | cons t ts ih =>
      have tail := ih (fun a ha => good a (by simp [ha]))
      have deg := inner_degree G (good t (by simp))
      rcases deg with d|d <;> simp [d] <;> omega
  have all := fan (dualRow G (apex M)) (fun x hx eq => row_no_loop G hh _ (eq ▸ hx))
  exact all.trans (congrArg (· + _) (boundary_cycle G hh).2.1)

end DiskFullerene.Dual
