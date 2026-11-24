import OverlayMinor
import TracePlanarity

/-! The permanent names of a terminal successful trace embed every prefix's
observed cells into the barycentric incidence graph of its sphere rotation. -/
namespace Recognition.TraceOverlay
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability PlanarDegrees.Frontier PlanarDegrees.Topology
open Recognition.Witness Recognition.Wagner Recognition.TracePlanarity Recognition.FlagRotation
open Recognition.Overlay Recognition.OverlayMinor

private def key (a b : Fin n) := (min a b,max a b)
private theorem key_eq (a b c d : Fin n) :
    key a b=key c d ↔ (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  simp only [key,Prod.mk.injEq]
  rcases le_total a b with h|h <;> rcases le_total c d with g|g <;>
    simp [h,g] <;> grind

private theorem neighbor {a b : Fin 3} (ne : a≠b) : a+1=b ∨ b+1=a := by
  exact (by decide : ∀ a b : Fin 3, a≠b → a+1=b ∨ b+1=a) a b ne

private theorem next {H : SimpleGraph (Fin n)} (R : Indexed H f) (i k) :
    (R.row (i,k+1)).fst=(R.row (i,k)).snd := by
  rw [← R.follows,PlaneMap.facePerm_apply,R.plane.isRotationSystem.fst_apply]
  rfl

private theorem unique_tail {H : SimpleGraph (Fin n)} (R : Indexed H f) (i)
    {k l : Fin 3} (eq : (R.row (i,k)).fst=(R.row (i,l)).fst) : k=l := by
  by_contra ne
  rcases neighbor ne with h|h
  · subst l; exact (R.row (i,k)).adj.ne (eq.trans (next R i k))
  · subst k; exact (R.row (i,l)).adj.ne (eq.symm.trans (next R i l))

private def coords {H : SimpleGraph (Fin n)} (R : Indexed H f) :
    Cells H.Dart (Fin n) (Fin n × Fin n) (Fin (f+1)) where
  vertex := fun d => d.fst
  edge := fun d => key d.fst d.snd
  face := fun d => (R.row.symm d).1
  tail_unique := by
    intro a b fst keys
    rcases (key_eq ..).mp keys with h|h
    · exact SimpleGraph.Dart.ext _ _ (Prod.ext fst h.2)
    · exact (a.adj.ne (fst.trans h.2.symm)).elim
  row_unique := by
    intro x y rows keys
    obtain ⟨⟨i,k⟩,rfl⟩ := R.row.surjective x
    obtain ⟨⟨j,l⟩,rfl⟩ := R.row.surjective y
    simp at rows
    subst j
    rcases (key_eq ..).mp keys with h|h
    · exact congrArg (fun k => R.row (i,k)) (unique_tail R i h.1)
    · have a : k=l+1 := unique_tail R i (h.1.trans (next R i l).symm)
      have b : l=k+1 := unique_tail R i (h.2.symm.trans (next R i k).symm)
      exact False.elim ((by decide : ∀ k l : Fin 3, k=l+1 → l=k+1 → False) k l a b)

private theorem coords_planar {H : SimpleGraph (Fin n)} (R : Indexed H f) : IsPlanar (coords R).graph := by
  let _ := Finite.of_equiv _ R.row
  apply graph_planar R.plane.rot (dartSymm H) (fun _ => rfl) R.plane.eulerDefect_eq_zero
  · intro a b
    refine ⟨R.plane.isRotationSystem.sameCycle a b,fun h => ?_⟩
    exact sameCycle_of_step (Setoid.ker (fun z : H.Dart => z.fst))
      (fun x => (R.plane.isRotationSystem.fst_apply x).symm) h
  · intro a b
    rw [sameCycle_dartSymm_iff]
    change key a.fst a.snd = key b.fst b.snd ↔ _
    rw [key_eq]
    constructor
    · rintro (h|h)
      · exact .inl (SimpleGraph.Dart.ext _ _ (Prod.ext h.1.symm h.2.symm))
      · exact .inr (SimpleGraph.Dart.ext _ _ (Prod.ext h.2.symm h.1.symm))
    · rintro (rfl|rfl)
      · exact .inl ⟨rfl,rfl⟩
      · exact .inr ⟨rfl,rfl⟩
  · intro a b; exact (R.orbit a b).symm

private def name (v : Nat) (rows : Overlay.Id fs → Fin (f+1)) :
    Node (Overlay.Id fs) → Cell (Fin (v+1)) (Fin (v+1) × Fin (v+1)) (Fin (f+1))
  | .vertex a => .inl (Fin.ofNat _ a)
  | .point e => .inr (.inl ((Fin.ofNat _ e.lo),(Fin.ofNat _ e.hi)))
  | .centre i => .inr (.inr (rows i))

private theorem side_data {fs : List Face} {i : Overlay.Id fs} {e : Edge} (h : e∈flags fs i) :
    e.lo ∈ cornerNames (fs.get i) ∧ e.hi ∈ cornerNames (fs.get i) ∧ e.hi ≤ (fs.get i).z := by
  have H := (fs[i.val]).yz
  simp [flags,Face.sides] at h
  rcases h with rfl|rfl|rfl <;> simp [cornerNames]; omega

/-- Place the finite observed cells using the row injection of this prefix.
All incidence and uniqueness facts come from the original three named
corners, including the case of repeated face *instances*. -/
private noncomputable def place {v f : Nat} (C : ClosedTrace v f) (R : Indexed (toSimple (host C)) f)
    (corn : ∀ i (x : Fin (v+1)), x.val∈cornerNames (C.faces i) ↔ ∃ k, (R.row (i,k)).fst=x)
    (fs : List Face) (rows : Overlay.Id fs → Fin (f+1)) (inj : Function.Injective rows)
    (same : ∀ i, fs.get i=C.faces (rows i)) : Placement fs (coords R).graph := by
  let H := toSimple (host C)
  have bound {i : Overlay.Id fs} {e} (s : e∈flags fs i) : e.lo<v+1 ∧ e.hi<v+1 := by
    have z := C.bounded (rows i)
    rw [← same] at z
    have t := (side_data s).2.2
    have incr := e.increasing
    omega
  have vbound {x : Nat} (obs : observed fs (.vertex x)) : x<v+1 := by
    obtain ⟨e,⟨i,m⟩,t⟩ := obs
    have b := bound m
    simp [touches] at t
    omega
  have ebound {e : Edge} (obs : observed fs (.point e)) : e.lo<v+1 ∧ e.hi<v+1 := by
    obtain ⟨i,m⟩ := obs
    exact bound m
  let cell := name v rows
  have incidentFace {e : Edge} {i : Overlay.Id fs} (inc : e∈flags fs i) :
      ∃ d : H.Dart, (coords R).edge d=(Fin.ofNat _ e.lo,Fin.ofNat _ e.hi) ∧ (coords R).face d=rows i := by
    obtain ⟨lo,hi⟩ := bound inc
    let a : Fin (v+1) := ⟨e.lo,lo⟩
    let b : Fin (v+1) := ⟨e.hi,hi⟩
    have lt : a<b := e.increasing
    have dc := side_data inc
    rw [same] at dc
    obtain ⟨k,hk⟩ := (corn (rows i) a).mp dc.1
    obtain ⟨l,hl⟩ := (corn (rows i) b).mp dc.2.1
    have ne : k≠l := by intro eq; subst l; exact lt.ne (hk.symm.trans hl)
    rcases neighbor ne with seq|seq
    · refine ⟨R.row (rows i,k),?_,by simp [coords]⟩
      have snd := (next R (rows i) k).symm
      rw [seq,hl] at snd
      simp [coords,key,hk,snd,min_eq_left lt.le,max_eq_right lt.le,a,b,Fin.ofNat,lo,hi,Nat.mod_eq_of_lt]
    · refine ⟨R.row (rows i,l),?_,by simp [coords]⟩
      have snd := (next R (rows i) l).symm
      rw [seq,hk] at snd
      simp [coords,key,hl,snd,min_eq_right lt.le,max_eq_left lt.le,a,b,Fin.ofNat,lo,hi,Nat.mod_eq_of_lt]
  refine ⟨cell,?_,?_⟩
  · intro x y ox oy eq
    cases x <;> cases y <;> simp only [cell,name,Sum.inl.injEq,Sum.inr.injEq,
      reduceCtorEq,Prod.mk.injEq,Node.vertex.injEq,Node.point.injEq,Node.centre.injEq] at eq ⊢
    · have val := congrArg Fin.val eq
      simpa [Fin.ofNat,Nat.mod_eq_of_lt (vbound ox),Nat.mod_eq_of_lt (vbound oy)] using val
    · have lo := congrArg Fin.val eq.1
      have hi := congrArg Fin.val eq.2
      have xb := ebound ox
      have yb := ebound oy
      simp [Fin.ofNat,Nat.mod_eq_of_lt xb.1,Nat.mod_eq_of_lt xb.2,Nat.mod_eq_of_lt yb.1,
        Nat.mod_eq_of_lt yb.2] at lo hi
      cases ‹Edge›; cases ‹Edge›; simp_all
    · exact inj eq
  · have ve (a : Nat) (e : Edge) (obs : observed fs (.point e)) (t : touches e a) :
        (coords R).graph.Adj (cell (.vertex a)) (cell (.point e)) := by
      obtain ⟨i,s⟩ := obs
      obtain ⟨d,h,_⟩ := incidentFace s
      obtain ⟨lo,hi⟩ := bound s
      have hkey : key d.fst d.snd = key (Fin.ofNat (v+1) e.lo) (Fin.ofNat _ e.hi) := by
        have lt : Fin.ofNat (v+1) e.lo < Fin.ofNat (v+1) e.hi := by
          simpa [Fin.lt_def,Fin.ofNat,Nat.mod_eq_of_lt lo,Nat.mod_eq_of_lt hi] using e.increasing
        have norm : key (Fin.ofNat (v+1) e.lo) (Fin.ofNat _ e.hi) = (Fin.ofNat _ e.lo,Fin.ofNat _ e.hi) :=
          Prod.ext (min_eq_left lt.le) (max_eq_right lt.le)
        exact h.trans norm.symm
      have flipkey : (coords R).edge d.symm=(coords R).edge d := by simp [coords,key,min_comm,max_comm]
      simp [touches] at t
      rcases (key_eq ..).mp hkey with case1|case2 <;> rcases t with rfl|rfl
      · exact ⟨(d,.vertex),congrArg Sum.inl case1.1,congrArg (fun x => Sum.inr (Sum.inl x)) h⟩
      · exact ⟨(d.symm,.vertex),congrArg Sum.inl case1.2,congrArg (fun x => Sum.inr (Sum.inl x)) (flipkey.trans h)⟩
      · exact ⟨(d.symm,.vertex),congrArg Sum.inl case2.2,congrArg (fun x => Sum.inr (Sum.inl x)) (flipkey.trans h)⟩
      · exact ⟨(d,.vertex),congrArg Sum.inl case2.1,congrArg (fun x => Sum.inr (Sum.inl x)) h⟩
    have fe (i : Overlay.Id fs) (e : Edge) (inc : e∈flags fs i) :
        (coords R).graph.Adj (cell (.centre i)) (cell (.point e)) := by
      obtain ⟨d,h,row⟩ := incidentFace inc
      exact ⟨(d,.face),congrArg (fun x => Sum.inr (Sum.inr x)) row,congrArg (fun x => Sum.inr (Sum.inl x)) h⟩
    intro x y ox oy edge
    cases x <;> cases y <;> first
      | contradiction
      | exact ve _ _ oy edge
      | exact (ve _ _ ox edge).symm
      | exact fe _ _ edge
      | exact (fe _ _ edge).symm

private theorem name_perm {A B : Type} (name : A → B) {xs ys : List B} (p : xs.Perm ys) :
    ∀ as : List A, as.map name=xs → ∃ bs : List A, bs.map name=ys ∧ as.Perm bs := by
  induction p with
  | nil =>
    rintro (_|⟨a,as⟩) m
    · exact ⟨[],rfl,.nil⟩
    · contradiction
  | cons x p ih =>
    rintro (_|⟨a,as⟩) m
    · contradiction
    obtain ⟨one,rest⟩ := List.cons.inj m
    obtain ⟨bs,good,move⟩ := ih as rest
    exact ⟨a::bs,by simp [one,good],.cons _ move⟩
  | swap x y zs =>
    rintro (_|⟨b,_|⟨a,as⟩⟩) m
    · contradiction
    · simp at m
    obtain ⟨one,two,rest⟩ := show name b=y ∧ name a=x ∧ as.map name=zs by simpa using m
    exact ⟨a::b::as,by simp [one,two,rest],.swap ..⟩
  | trans p q ih jh =>
    intro as m
    obtain ⟨bs,g,e⟩ := ih as m
    obtain ⟨cs,h,d⟩ := jh bs g
    exact ⟨cs,h,e.trans d⟩

/-- Every cut of every facial permutation of a genuine terminal trace has a
planar, labelled, simple overlay on exactly its appearing node types. -/
theorem prefix_planar {v f : Nat} (C : ClosedTrace v f) (count : (f+1)+4=2*(v+1))
    (read todo : List Face) (perm : (read++todo).Perm (List.ofFn C.faces))
    {s : Inventory} (ok : replay (read.flatMap Face.sides)=some s) : IsPlanar (shadow read s) := by
  classical
  obtain ⟨R,corn⟩ := host_rows C count
  obtain ⟨names,eq,p⟩ := name_perm C.faces perm.symm (List.finRange _) List.ofFn_eq_map.symm
  have nd := p.nodup (List.nodup_finRange _)
  have length : names.length=read.length+todo.length := by simpa using congrArg List.length eq
  let slot := fun i : Overlay.Id read => (⟨i.val,by have := i.isLt; omega⟩ : Fin names.length)
  let row := fun i => names.get (slot i)
  have inj : Function.Injective row := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin names.length => x.val) (nd.get_inj_iff.mp h))
  have same (i : Overlay.Id read) : read.get i=C.faces (row i) := by
    have r := congrArg (fun xs : List Face => xs[i.val]?) eq
    have less : i.val<names.length := (slot i).isLt
    simp [List.getElem?_append_left i.isLt,i.isLt,less] at r
    exact r.symm
  exact shadow_planar read s ok _ (coords_planar R) (place C R corn read row inj same)

#print axioms prefix_planar
end Recognition.TraceOverlay
