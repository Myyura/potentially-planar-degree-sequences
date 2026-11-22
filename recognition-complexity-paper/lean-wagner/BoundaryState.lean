import OverlayRead
import QuotientDP

/-! Decode the marked, anonymous overlay into the actual orientation-symmetric
state of the face transition algorithm. The first slots carry one active
vertex per distinct key; all other slots are inactive. -/
namespace Recognition.BoundaryState
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep Recognition.Overlay Recognition.OverlayMinor
open Recognition.QuotientDP Recognition.OverlayRead Recognition.OverlayCoverage Recognition.MarkedPlane

def unique (key : Fin k → Nat) : List (Fin k) → List (Fin k)
  | [] => []
  | a::xs => if (xs.map key).contains (key a) then unique key xs else a::unique key xs

private theorem keys_mem (g : Fin k → Nat) (xs : List (Fin k)) (o : Nat) :
    o∈(unique g xs).map g ↔ o∈xs.map g := by
  induction xs with
  | nil => simp [unique]
  | cons a xs ih =>
    by_cases m : g a∈xs.map g <;> simp [unique,m,ih]; grind

private theorem keys_nodup (g : Fin k → Nat) (xs : List (Fin k)) : ((unique g xs).map g).Nodup := by
  induction xs with
  | nil => simp [unique]
  | cons a xs ih => by_cases m : g a∈xs.map g <;> simp [unique,m,ih,keys_mem]

private theorem unique_sub (g : Fin k → Nat) (xs : List (Fin k)) : unique g xs ⊆ xs := by
  induction xs with
  | nil => simp [unique]
  | cons a xs ih =>
    by_cases h : g a∈xs.map g <;> simp [unique,h]
    · exact fun _ m => .tail _ (ih m)
    · exact fun _ m => .tail _ (ih m)

def activeReps (C : View) := unique (fun x : Fin C.ribbon.length => (C.vertexKey x).val)
  ((List.finRange C.ribbon.length).filter (fun a => tag C a == 0))

/-- The two endpoint lookups are symmetric. Self-pairs are never sides. -/
private def pairRead (reps : List (Fin d)) (test : Fin d → Fin d → Bool) (e : Side n) :=
  e.1!=e.2 && (reps[e.1.val]?).any (fun x => (reps[e.2.val]?).any (test x))

private def blockRead (C : View) (reps : List (Fin k)) (e f : Side n) :=
  e.1!=e.2 && f.1!=f.2 && (reps[e.1.val]?).any fun x => (reps[e.2.val]?).any fun y =>
    (reps[f.1.val]?).any fun u => (reps[f.2.val]?).any fun v => block C x y u v

def fromView (names : Nat) (C : View) (rest : Multiset Nat) (used read : Nat) : Option (State names) :=
  let reps := activeReps C
  if reps.length>names then none else
  some ⟨pairRead reps (fun x y => edgeKind C x y 1),pairRead reps (fun x y => edgeKind C x y 2),
    blockRead C reps,fun x => (reps[x.val]?.map C.counter).getD 0,rest,used,read⟩

def blank (n : Nat) (rest : Multiset Nat) (used read : Nat) : State n :=
  ⟨fun _ => false,fun _ => false,fun _ _ => false,fun _ => 0,rest,used,read⟩

def decode (names : Nat) (bits : List Bool) (rest : Multiset Nat) (used read : Nat) : Option (State names) :=
  if bits=[] then some (blank names rest used read)
  else (MarkedPlane.decode bits).bind (fun C => fromView names C rest used read)

/-- Attach a concrete candidate row to every short code and allowed choice
of residual histogram and two global counters. -/
def table (n cutoff faceLimit : Nat) (remaining : List (Multiset Nat)) : List (State n) :=
  (words cutoff).flatMap fun bs => remaining.flatMap fun rest =>
    (List.range (n+1)).flatMap fun used =>
      (List.range (faceLimit+1)).filterMap fun faces => decode n bs rest used faces

theorem table_mem {n cutoff faceLimit} {remaining : List (Multiset Nat)} {t : State n} :
    t∈table n cutoff faceLimit remaining ↔
    ∃ bs rest used faces, bs.length≤cutoff ∧ rest∈remaining ∧ used≤n ∧ faces≤faceLimit ∧
      decode n bs rest used faces=some t := by
  simp only [table,List.mem_flatMap,List.mem_filterMap,List.mem_range,words_spec]
  grind

/-- This cutoff counts boundary bits; residuals and the two counters form
separate enumerated fields. -/
def cutoff (n : Nat) := 1220 * Nat.sqrt (220^2*n) + 1

theorem length_cut (w len n : Nat) (a : len≤1220*w+1) (b : w*w≤220^2*n) : len≤cutoff n :=
  a.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 1220 (Nat.le_sqrt.mpr b)) 1)

private theorem edgeKind_swap (C : View) (x y : Fin n) (t) : edgeKind C x y t=edgeKind C y x t := by
  simp only [edgeKind,middle]
  congr 1
  funext m
  ac_rfl

private theorem block_flip (C : View) (x y u v : Fin n) :
    block C y x u v=block C x y u v ∧ block C x y v u=block C x y u v := by
  have mid (a b c : Fin n) : middle C a b c 1=middle C b a c 1 := by unfold middle; ac_rfl
  constructor <;> unfold block
  · simp_rw [mid y x]
  · simp_rw [mid v u]

/-- Unordered endpoint interpretation of a side in permanent names. -/
def ends (e : Edge) (a b : Nat) := (a=e.lo ∧ b=e.hi) ∨ (a=e.hi ∧ b=e.lo)
def has (xs : List Edge) (a b : Nat) := ∃ e∈xs, ends e a b
def linked (fs : List Face) (s : Inventory) (a b c d : Nat) :=
  ∃ e∈s.pending, ∃ f∈s.pending, ends e a b ∧ ends f c d ∧ sameBlock fs e f

structure Model (fs : List Face) (s : Inventory) (t : State n) : Prop where
  pending : ∀ a b : Fin n, t.pending (a,b) ↔ has s.pending a.val b.val
  sealed : ∀ a b : Fin n, t.sealed (a,b) ↔ has (retain (live s) s) a.val b.val
  blocks : ∀ a b c d : Fin n, t.blocks (a,b) (c,d) ↔ linked fs s a.val b.val c.val d.val
  current : ∀ a : Fin n, t.current a = if live s a.val then s.redDegree a.val else 0

private theorem act (s : Inventory) (x : Nat) : x∈(activeNames s).eraseDups ↔ live s x := by
  simp [activeNames,List.mem_flatMap,touches,live,List.any_eq_true]

theorem hasVertex (s : Inventory) {fs : List Face} {v : Nat} :
    Node.vertex v ∈ Overlay.vertices fs s ↔ live s v := by simp [Overlay.vertices,← act]

private theorem repr_subset (C : View) : ∀ a∈activeReps C, tag C a=0 := by
  intro a m; exact beq_iff_eq.mp (List.mem_filter.mp (unique_sub _ _ m)).2

private theorem active_named (L : Labels fs s C.ribbon.length C) {a : Fin C.ribbon.length}
    (m : a∈activeReps C) : ∃ v, (L.tail a).val=.vertex v ∧ live s v := by
  have h := repr_subset C a m
  have t : tag C a=(role s (L.tail a).val).val := by simp [tag,(L.marks a).1]
  cases eq : (L.tail a).val with
  | vertex v => exact ⟨v,rfl,(hasVertex s).mp (eq ▸ (L.tail a).property)⟩
  | point e => by_cases k : e∈s.pending <;> simp [eq,role,k,h] at t
  | centre p => simp [eq,role,h] at t

private theorem represented (L : Labels fs s C.ribbon.length C) {a : Nat} (live_ : live s a) :
    ∃ i : Fin (activeReps C).length, (L.tail ((activeReps C).get i)).val=.vertex a := by
  obtain ⟨d,hd⟩ := L.onto ⟨_,(hasVertex s).mpr live_⟩
  have tag_ : tag C d=0 := by simp [tag,(L.marks d).1,hd,role]
  let key := fun j : Fin C.ribbon.length => (C.vertexKey j).val
  have occ : key d ∈ (activeReps C).map key := (keys_mem ..).mpr
    (List.mem_map.mpr ⟨d,List.mem_filter.mpr ⟨List.mem_finRange _,by simp [tag_]⟩,rfl⟩)
  obtain ⟨z,m,k⟩ := List.mem_map.mp occ
  obtain ⟨i,eq⟩ := List.mem_iff_get.mp m
  have same := (L.same z d).mp (Fin.ext k)
  exact ⟨i,eq ▸ congrArg Subtype.val (same.trans hd)⟩

structure Naming (fs : List Face) (s : Inventory) (n : Nat) (C : View)
    (L : Labels fs s C.ribbon.length C) where
  perm : Equiv.Perm (Fin n)
  next : (activeReps C).length≤n
  used : ∀ i : Fin (activeReps C).length,
    (L.tail ((activeReps C).get i)).val=.vertex (perm (i.castLE next)).val
  other : ∀ x : Fin n, (activeReps C).length≤x.val → live s (perm x).val=false

private theorem names (L : Labels fs s C.ribbon.length C) (n : Nat)
    (bounded : ∀ x, live s x → x<n) : Nonempty (Naming fs s n C L) := by
  classical
  let reps := activeReps C
  have hn (i : Fin reps.length) := active_named L (List.get_mem reps i)
  let go := fun i : Fin reps.length => (⟨(hn i).choose,bounded _ (hn i).choose_spec.2⟩ : Fin n)
  have mark (i : Fin reps.length) : (L.tail (reps.get i)).val=.vertex (go i).val := (hn i).choose_spec.1
  have inj : Function.Injective go := by
    intro i j eq
    have keys := (L.same (reps.get i) (reps.get j)).mpr (Subtype.ext ((mark i).trans (eq ▸ (mark j).symm)))
    have nd := keys_nodup (fun x : Fin C.ribbon.length => (C.vertexKey x).val)
      ((List.finRange _).filter (fun a => tag C a==0))
    apply Fin.ext
    apply (nd.getElem_inj_iff (hi := by simpa [-List.get_eq_getElem, reps,activeReps] using i.isLt)
      (hj := by simpa [-List.get_eq_getElem,reps,activeReps] using j.isLt)).mp
    rw [List.getElem_map,List.getElem_map]
    exact congrArg Fin.val keys
  have le : reps.length≤n := by simpa using Fintype.card_le_of_injective go inj
  obtain ⟨p,exts⟩ := Equiv.Perm.exists_extending_pair (Fin.castLE le) go (Fin.castLE_injective le) inj
  refine ⟨⟨p,le,fun i => (exts i).symm ▸ mark i,?_⟩⟩
  intro x later
  by_contra! yes
  obtain ⟨j,eq⟩ := represented L (show live s (p x).val=true by simpa using yes)
  have same : go j=p x := Fin.ext (Node.vertex.inj ((mark j).symm.trans eq))
  have h := congrArg Fin.val (p.injective ((exts j).trans same))
  have lt := j.isLt
  change j.val=x.val at h
  omega

private theorem sorted {x y : Nat} (ne : x≠y) : ∃ e : Edge, ends e x y := by
  by_cases h : x<y
  · exact ⟨⟨x,y,h⟩,.inl ⟨rfl,rfl⟩⟩
  · exact ⟨⟨y,x,by omega⟩,.inr ⟨rfl,rfl⟩⟩

theorem same_pair {e f : Edge} {x y} (h : ends e x y) (k : ends f x y) : e=f := by
  cases e; cases f
  simp only [ends] at h k
  grind

private theorem member {xs : List Edge} {e : Edge} {x y} (h : ends e x y) : has xs x y ↔ e∈xs :=
  ⟨fun ⟨_f,m,k⟩ => same_pair k h ▸ m,fun m => ⟨e,m,h⟩⟩

theorem relation {fs s e f x y u v} (p : ends e x y) (q : ends f u v) :
    linked fs s x y u v ↔ e∈s.pending ∧ f∈s.pending ∧ sameBlock fs e f := by
  constructor
  · rintro ⟨g,m,z,k,a,b,c⟩
    obtain rfl := same_pair a p; obtain rfl := same_pair b q
    exact ⟨m,k,c⟩
  · rintro ⟨m,k,c⟩; exact ⟨e,m,f,k,p,q,c⟩

theorem scope (s : Inventory) (ls : List Edge) (sub : ls⊆retained s) {a b}
    (h : has ls a b) : a≠b ∧ live s a ∧ live s b := by
  obtain ⟨e,m,eq⟩ := h
  have hold := sub m
  have p : live s e.lo ∧ live s e.hi := by
    simp only [retained,List.mem_eraseDups,List.mem_append,retain,List.mem_filter,Bool.and_eq_true] at hold
    rcases hold with inP|⟨_,l,r⟩
    · exact ⟨List.any_eq_true.mpr ⟨_,inP,by simp [touches]⟩,List.any_eq_true.mpr ⟨_,inP,by simp [touches]⟩⟩
    · exact ⟨l,r⟩
  rcases eq with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨e.increasing.ne,p⟩
  · exact ⟨e.increasing.ne',p.2,p.1⟩

theorem pending_sub (s : Inventory) : s.pending⊆retained s := by intro e m; simp [retained,m]
theorem sealed_sub (s : Inventory) : retain (live s) s⊆retained s := by intro e m; simp [retained,m]

private theorem query {fs s n C} (L : Labels fs s n C) (ok : replay (fs.flatMap Face.sides)=some s)
    (a b : Fin n) {x y : Nat} (ax : (L.tail a).val=.vertex x) (by_ : (L.tail b).val=.vertex y) (ne : x≠y) :
    (edgeKind C a b 1 ↔ has s.pending x y) ∧ (edgeKind C a b 2 ↔ has (retain (live s) s) x y) := by
  obtain ⟨e,g⟩ := sorted ne
  rw [member g,member g]
  rcases g with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact edges_read L ok a b e ax by_
  · rw [edgeKind_swap C a b 1,edgeKind_swap C a b 2]
    exact edges_read L ok b a e by_ ax

private theorem queryBlock {fs s n C} (L : Labels fs s n C) (a b c d : Fin n) {x y u v : Nat}
    (ax : (L.tail a).val=.vertex x) (by_ : (L.tail b).val=.vertex y)
    (cu : (L.tail c).val=.vertex u) (dv : (L.tail d).val=.vertex v) (xy : x≠y) (uv : u≠v) :
    block C a b c d ↔ linked fs s x y u v := by
  obtain ⟨e,g⟩ := sorted xy; obtain ⟨f,h⟩ := sorted uv
  rw [relation g h]
  rcases g with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact blocks_read L a b c d e f ax by_ cu dv
  · rw [(block_flip C a b d c).2]; exact blocks_read L a b d c e f ax by_ dv cu
  · rw [(block_flip C b a c d).1]; exact blocks_read L b a c d e f by_ ax cu dv
  · rw [(block_flip C b a c d).1,(block_flip C b a d c).2]
    exact blocks_read L b a d c e f by_ ax dv cu

private theorem is_slot (N : Naming fs s n C L) {x : Fin n} {d : Fin C.ribbon.length}
    (m : (activeReps C)[x.val]?=some d) : (L.tail d).val=.vertex (N.perm x).val := by
  obtain ⟨lt,eq⟩ := List.getElem?_eq_some_iff.mp m
  subst d
  exact N.used ⟨x.val,lt⟩

private theorem is_live (N : Naming fs s n C L) {x : Fin n} (h : live s (N.perm x).val) :
    ∃ d : Fin C.ribbon.length, (activeReps C)[x.val]?=some d := by
  have lt : x.val<(activeReps C).length := by
    by_contra! no
    have no' := N.other x no
    simp_all
  exact ⟨_,List.getElem?_eq_getElem lt⟩

private theorem pair_exact (N : Naming fs s n C L) (ls : List Edge) (sub : ls⊆retained s)
    (test : Fin C.ribbon.length → Fin C.ribbon.length → Bool)
    (pred : ∀ a b x y, (L.tail a).val=.vertex x → (L.tail b).val=.vertex y →
      x≠y → (test a b ↔ has ls x y)) (x y : Fin n) :
    pairRead (activeReps C) test (x,y) ↔ has ls (N.perm x).val (N.perm y).val := by
  simp only [pairRead,Bool.and_eq_true,bne_iff_ne,Option.any_eq_true]
  have diff (ne : x≠y) : (N.perm x).val≠(N.perm y).val := fun eq => ne (N.perm.injective (Fin.ext eq))
  constructor
  · rintro ⟨ne,a,am,b,bm,h⟩
    exact (pred _ _ _ _ (is_slot N am) (is_slot N bm) (diff ne)).mp h
  · intro yes
    obtain ⟨ne,hx,hy⟩ := scope _ _ sub yes
    obtain ⟨a,am⟩ := is_live N hx
    obtain ⟨b,bm⟩ := is_live N hy
    exact ⟨fun eq => ne (eq ▸ rfl),a,am,b,bm,(pred _ _ _ _ (is_slot N am) (is_slot N bm) ne).mpr yes⟩

private theorem blocks_exact (N : Naming fs s n C L) (x y u v : Fin n) :
    blockRead C (activeReps C) (x,y) (u,v) ↔
      linked fs s (N.perm x).val (N.perm y).val (N.perm u).val (N.perm v).val := by
  simp only [blockRead,Bool.and_eq_true,bne_iff_ne,Option.any_eq_true]
  have diff {a b : Fin n} (ne : a≠b) : (N.perm a).val≠(N.perm b).val := fun eq => ne (N.perm.injective (Fin.ext eq))
  constructor
  · rintro ⟨⟨xy,uv⟩,a,am,b,bm,c,cm,d,dm,yes⟩
    exact (queryBlock L a b c d (is_slot N am) (is_slot N bm) (is_slot N cm) (is_slot N dm) (diff xy) (diff uv)).mp yes
  · intro yes
    obtain ⟨e,em,f,fm,g,j,_⟩ := yes
    obtain ⟨xy,hx,hy⟩ := scope s s.pending (pending_sub s) (show has s.pending _ _ from ⟨e,em,g⟩)
    obtain ⟨uv,hu,hv⟩ := scope s s.pending (pending_sub s) (show has s.pending _ _ from ⟨f,fm,j⟩)
    obtain ⟨a,am⟩ := is_live N hx; obtain ⟨b,bm⟩ := is_live N hy
    obtain ⟨c,cm⟩ := is_live N hu; obtain ⟨d,dm⟩ := is_live N hv
    exact ⟨⟨fun eq => xy (eq ▸ rfl),fun eq => uv (eq ▸ rfl)⟩,a,am,b,bm,c,cm,d,dm,
      (queryBlock L a b c d (is_slot N am) (is_slot N bm) (is_slot N cm) (is_slot N dm) xy uv).mpr
        ⟨e,em,f,fm,g,j,by assumption⟩⟩

private theorem fill_exact (N : Naming fs s n C L) (ok : replay (fs.flatMap Face.sides)=some s)
    (t : State n) (M : Model fs s t) :
    ∃ d : State n, fromView n C t.remaining t.used t.faces=some d ∧ Same d t := by
  let reps := activeReps C
  let d : State n := ⟨pairRead reps (fun x y => edgeKind C x y 1),pairRead reps (fun x y => edgeKind C x y 2),
    blockRead C reps,fun x => (reps[x.val]?.map C.counter).getD 0,t.remaining,t.used,t.faces⟩
  refine ⟨d,by simp [fromView,show ¬n<(activeReps C).length from Nat.not_lt.mpr N.next,d,reps],
    N.perm,?_,?_,?_,?_,rfl,rfl,rfl⟩
  · rintro ⟨x,y⟩
    apply Bool.eq_iff_iff.mpr
    exact (M.pending _ _).trans (pair_exact N _ (pending_sub s) _ (fun a b _ _ h k ne =>
      (query L ok a b h k ne).1) x y).symm
  · rintro ⟨x,y⟩
    apply Bool.eq_iff_iff.mpr
    exact (M.sealed _ _).trans (pair_exact N _ (sealed_sub s) _ (fun a b _ _ h k ne =>
      (query L ok a b h k ne).2) x y).symm
  · rintro ⟨x,y⟩ ⟨u,v⟩
    apply Bool.eq_iff_iff.mpr
    exact (M.blocks ..).trans (blocks_exact N x y u v).symm
  · intro x
    rw [M.current]
    by_cases lt : x.val<(activeReps C).length
    · let a := (activeReps C)[x.val]
      have am : reps[x.val]?=some a := List.getElem?_eq_getElem lt
      have val := is_slot N am
      have yes := (hasVertex s).mp (val ▸ (L.tail a).property)
      have current := (L.marks a).2
      simp only [val,OverlayCoverage.value] at current
      simpa [d,am,yes] using current.symm
    · have no := N.other x (Nat.le_of_not_gt lt)
      simp [d,reps,List.getElem?_eq_none (by omega : (activeReps C).length≤x.val),no]

private theorem empty_exact (fs : List Face) (s : Inventory) (nil : Overlay.vertices fs s=[])
    (t : State n) (M : Model fs s t) : Same (blank n t.remaining t.used t.faces) t := by
  have no (x : Nat) : live s x=false := by
    by_contra! yes
    have m := (hasVertex (fs := fs) s).mpr (show live s x by simpa using yes)
    simp [nil] at m
  have absent (ls : List Edge) (subset : ls⊆retained s) : ∀ x y, ¬has ls x y := by
    intro x y h
    have := (scope s ls subset h).2.1
    simp [no] at this
  refine ⟨1,?_,?_,?_,?_,rfl,rfl,rfl⟩
  · rintro ⟨x,y⟩
    apply Bool.eq_false_iff.mpr
    exact fun h => absent _ (pending_sub s) _ _ ((M.pending ..).mp h)
  · rintro ⟨x,y⟩
    apply Bool.eq_false_iff.mpr
    exact fun h => absent _ (sealed_sub s) _ _ ((M.sealed ..).mp h)
  · rintro ⟨x,y⟩ ⟨u,v⟩
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨e,em,_,_,p,_⟩ := (M.blocks ..).mp h
    exact absent _ (pending_sub s) _ _ ⟨e,em,p⟩
  · intro x; simp [blank,M.current,no]

/-- The decoded row lies in the very same anonymous state class as the
permanently labelled target. No permanent vertex name enters the bitstream. -/
theorem state_round_trip {fs s bits} (cov : Covered fs s bits) (ok : replay (fs.flatMap Face.sides)=some s)
    (bounded : ∀ x, live s x → x<n) (t : State n) (M : Model fs s t) :
    ∃ d, decode n bits t.remaining t.used t.faces=some d ∧ Same d t := by
  classical
  rcases cov with ⟨rfl,nil⟩|⟨k,C,tail,onto,parsed,len,keys,roles,links⟩
  · exact ⟨_,rfl,empty_exact fs s nil t M⟩
  · subst k
    let L : Labels fs s C.ribbon.length C := ⟨tail,onto,keys,roles,links⟩
    obtain ⟨N⟩ := names L n bounded
    obtain ⟨d,yes,same⟩ := fill_exact N ok t M
    have nonempty : bits≠[] := by
      rintro rfl
      change none = some C at parsed
      contradiction
    exact ⟨d,by simp [decode,nonempty,parsed,yes],same⟩

#print axioms state_round_trip
end Recognition.BoundaryState
