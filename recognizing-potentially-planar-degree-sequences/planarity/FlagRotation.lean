import TreeBands
import LeanPool.K5MinorFreeChoosability.Planar.Embedding

/-! The barycentric incidence graph joins original vertices and face centres
to edge midpoints. Its four kinds of darts carry an explicit rotation, and
the original Euler defect bounds that of the incidence graph. -/
namespace Recognition.FlagRotation
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability

inductive Tag where | vertex | toVertex | face | toFace deriving DecidableEq
open Tag
private def tagBits : Tag ≃ Bool × Bool where
  toFun | vertex => (false,false) | toVertex => (false,true) | face => (true,false) | toFace => (true,true)
  invFun | (false,false) => vertex | (false,true) => toVertex | (true,false) => face | (true,true) => toFace
  left_inv := by intro t; cases t <;> rfl
  right_inv := by rintro ⟨a,b⟩; cases a <;> cases b <;> rfl
instance : Fintype Tag := Fintype.ofEquiv _ tagBits.symm
abbrev Flag (D : Type) := D × Tag

def turn (σ α : Perm D) (undo : ∀ x, α (α x)=x) : Perm (Flag D) where
  toFun
    | (d,vertex) => (σ d,vertex)
    | (d,toVertex) => (d,toFace)
    | (d,face) => ((σ*α).symm d,face)
    | (d,toFace) => (α d,toVertex)
  invFun
    | (d,vertex) => (σ.symm d,vertex)
    | (d,toFace) => (d,toVertex)
    | (d,face) => ((σ*α) d,face)
    | (d,toVertex) => (α d,toFace)
  left_inv := by rintro ⟨d,t⟩; cases t <;> simp [undo]
  right_inv := by rintro ⟨d,t⟩; cases t <;> simp [undo]; exact (σ*α).symm_apply_apply d

def flipTag : Tag → Tag
  | vertex => toVertex
  | toVertex => vertex
  | face => toFace
  | toFace => face

def flip : Perm (Flag D) where
  toFun p := (p.1,flipTag p.2)
  invFun p := (p.1,flipTag p.2)
  left_inv := by rintro ⟨d,t⟩; cases t <;> rfl
  right_inv := by rintro ⟨d,t⟩; cases t <;> rfl

private theorem classify {U W : Type} (P : Perm U) (f : U → W)
    (one : ∀ z, f z=f (P z)) (cover : Function.Surjective f)
    (complete : ∀ a b, f a=f b → SameCycle P a b) : cycleCount P=Nat.card W := by
  let g : Quotient (SameCycle.setoid P) → W := Quotient.lift f
    (fun _ _ h => sameCycle_of_step (Setoid.ker f) one h)
  apply Nat.card_eq_of_bijective g
  constructor
  · intro x y
    exact Quotient.inductionOn₂ x y (fun a b e => Quotient.sound (s := SameCycle.setoid P) (complete a b e))
  · intro z
    obtain ⟨v,rfl⟩ := cover z
    exact ⟨Quotient.mk _ v,rfl⟩

private def orbit {D : Type} (A : Perm D) (d : D) := Quotient.mk (SameCycle.setoid A) d
private abbrev Orb {D : Type} (A : Perm D) := Quotient (SameCycle.setoid A)
private theorem step (P : Perm D) (x : D) : SameCycle P x (P x) :=
  sameCycle_apply_right.mpr (SameCycle.refl _ _)
private theorem ostep (P : Perm D) (x : D) : orbit P x = orbit P (P x) := Quotient.sound (step P x)

private def kind (σ α : Perm D) : Flag D → Orb σ ⊕ (Orb (σ*α).symm ⊕ Orb α)
  | (d,vertex) => .inl (orbit σ d)
  | (d,toVertex) => .inr (.inr (orbit α d))
  | (d,face) => .inr (.inl (orbit (σ*α).symm d))
  | (d,toFace) => .inr (.inr (orbit α d))

private theorem connected_kind (σ α : Perm D) (undo : ∀ x, α (α x)=x) (a b : Flag D)
    (eq : kind σ α a=kind σ α b) : SameCycle (turn σ α undo) a b := by
  let θ := turn σ α undo
  have vm {d e : D} (h : SameCycle σ d e) : SameCycle θ (d,vertex) (e,vertex) :=
    sameCycle_of_step (Setoid.comap (fun d : D => (d,vertex)) (SameCycle.setoid θ))
      (fun x => step θ (x,vertex)) h
  have fm {d e : D} (h : SameCycle (σ*α).symm d e) : SameCycle θ (d,face) (e,face) :=
    sameCycle_of_step (Setoid.comap (fun d : D => (d,face)) (SameCycle.setoid θ))
      (fun x => step θ (x,face)) h
  have pm (d : D) : SameCycle θ (d,toVertex) (d,toFace) := step θ _
  have em {d e : D} (h : SameCycle α d e) : SameCycle θ (d,toVertex) (e,toVertex) :=
    sameCycle_of_step (Setoid.comap (fun d : D => (d,toVertex)) (SameCycle.setoid θ))
      (fun x => (pm x).trans (step θ (x,toFace))) h
  obtain ⟨d,t⟩ := a
  obtain ⟨e,u⟩ := b
  have h := eq
  cases t <;> cases u <;> simp [kind] at h <;> first
      | exact vm (Quotient.exact h)
      | exact fm (Quotient.exact h)
      | exact em (Quotient.exact h)
      | exact (em (Quotient.exact h)).trans (pm e)
      | exact (pm d).symm.trans (em (Quotient.exact h))
      | exact (pm d).symm.trans ((em (Quotient.exact h)).trans (pm e))

private theorem vertex_cycles [Finite D] (σ α : Perm D) (undo : ∀ x, α (α x)=x) :
    cycleCount (turn σ α undo)=cycleCount σ+cycleCount (σ*α)+cycleCount α := by
  let θ := turn σ α undo
  have same := classify θ (kind σ α) (by
    rintro ⟨d,t⟩; cases t <;> simp only [kind,θ,turn,Equiv.coe_fn_mk,Sum.inl.injEq,Sum.inr.injEq]
    · exact ostep ..
    · exact ostep ..
    · exact ostep ..) (by
    rintro (q|q|q)
    · obtain ⟨d,rfl⟩ := Quotient.exists_rep q; exact ⟨(d,vertex),rfl⟩
    · obtain ⟨d,rfl⟩ := Quotient.exists_rep q; exact ⟨(d,face),rfl⟩
    · obtain ⟨d,rfl⟩ := Quotient.exists_rep q; exact ⟨(d,toVertex),rfl⟩) (connected_kind σ α undo)
  have inv : cycleCount (σ*α).symm=cycleCount (σ*α) :=
    numClasses_congr (fun a b => sameCycle_inv)
  rw [Nat.card_sum,Nat.card_sum] at same
  change cycleCount θ=cycleCount σ+(cycleCount (σ*α).symm+cycleCount α) at same
  simpa [inv,Nat.add_assoc] using same

private def edgeKey : Flag D → D × Bool
  | (d,vertex) | (d,toVertex) => (d,false)
  | (d,face) | (d,toFace) => (d,true)

private theorem edge_cycles [Finite D] : cycleCount (flip (D := D))=2*Nat.card D := by
  have h := classify (flip (D := D)) edgeKey (by rintro ⟨d,t⟩; cases t <;> rfl)
    (by rintro ⟨d,c⟩; cases c
        · exact ⟨(d,vertex),rfl⟩
        · exact ⟨(d,face),rfl⟩) (by
      rintro ⟨d,t⟩ ⟨e,u⟩ h
      cases t <;> cases u <;> simp [edgeKey] at h <;> subst e <;> first
        | exact SameCycle.refl _ _
        | exact step flip _)
  simpa [Nat.card_prod,Nat.mul_comm] using h

private def faceKey (σ α : Perm D) : Flag D → D
  | (d,vertex) | (d,toFace) => d
  | (d,face) => (σ*α) d
  | (d,toVertex) => σ d

private theorem face_cycles [Finite D] (σ α : Perm D) (undo : ∀ x, α (α x)=x) :
    cycleCount (turn σ α undo * flip)=Nat.card D := by
  let F := turn σ α undo * flip
  have rep (x : Flag D) : SameCycle F x (faceKey σ α x,vertex) := by
    obtain ⟨d,t⟩ := x
    cases t with
    | vertex => exact SameCycle.refl _ _
    | toVertex => exact step F _
    | face => exact (step F _).trans (step F _)
    | toFace =>
      have g := ((step F (d,toFace)).trans (step F _)).trans (step F _)
      change SameCycle F (d,toFace) (((σ*α) ((σ*α).symm d)),vertex) at g
      simpa [faceKey] using g
  apply classify F (faceKey σ α)
  · rintro ⟨d,t⟩; cases t <;> simp [F,flip,flipTag,turn,Perm.mul_apply,faceKey]
  · exact fun d => ⟨(d,vertex),rfl⟩
  · intro x y h
    exact (rep x).trans (h ▸ (rep y).symm)

private theorem components [Finite D] (σ α : Perm D) (undo : ∀ x, α (α x)=x) :
    numComponents (turn σ α undo) flip ≤ numComponents σ α := by
  let θ := turn σ α undo
  let S := compSetoid θ flip
  have link (d : D) (a b : Tag) : S (d,a) (d,b) := by
    have p : S (d,vertex) (d,toVertex) := compSetoid_right θ flip _
    have q : S (d,toVertex) (d,toFace) := compSetoid_left θ flip _
    have r : S (d,toFace) (d,face) := compSetoid_right θ flip _
    have bridge (k : Tag) : S (d,vertex) (d,k) := by
      cases k with
      | vertex => exact S.refl _
      | toVertex => exact p
      | face => exact S.trans (S.trans p q) r
      | toFace => exact S.trans p q
    exact S.trans (S.symm (bridge a)) (bridge b)
  have lift {a b : D} (h : compSetoid σ α a b) : S (a,vertex) (b,vertex) :=
    compSetoid_le (Setoid.comap (fun x : D => (x,vertex)) S)
      (fun z => compSetoid_left θ flip (z,vertex))
      (fun z => S.trans (link z vertex toFace)
        (S.trans (compSetoid_left θ flip (z,toFace)) (link (α z) toVertex vertex))) h
  let f : Quotient (compSetoid σ α) → Quotient S := Quotient.lift
    (fun d : D => Quotient.mk S (d,vertex)) (fun _ _ h => Quotient.sound (lift h))
  apply Nat.card_le_card_of_surjective f
  intro q
  obtain ⟨⟨d,t⟩,rfl⟩ := Quotient.exists_rep q
  exact ⟨Quotient.mk _ d, Quotient.sound (s := S) (link _ _ _)⟩

/-- Each triangular (or polygonal) plane rotation induces a planar
rotation on its vertex–edge–face incidence graph using four darts for
each original dart. The same construction works for disconnected maps. -/
theorem planar [Finite D] (σ α : Perm D) (undo : ∀ x, α (α x)=x)
    (zero : eulerDefect σ α=0) : eulerDefect (turn σ α undo) flip=0 := by
  have low := eulerDefect_nonneg (turn σ α undo) flip
  have high := components σ α undo
  have ct : Nat.card Tag=4 := by rw [Nat.card_congr tagBits,Nat.card_prod]; simp
  have ch : Nat.card (Flag D)=Nat.card D*4 := by rw [Nat.card_prod,ct]
  have le : eulerDefect (turn σ α undo) flip ≤ eulerDefect σ α := by
    unfold eulerDefect
    rw [vertex_cycles,edge_cycles,face_cycles,ch]
    push_cast
    omega
  omega

#print axioms planar
end Recognition.FlagRotation

namespace Recognition.FlagRotation
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability Tag

/-- A cell coordinate labelling of a map. Simplicity of the incidences means
that an end and edge, or a face and edge, specify at most one oriented dart.
For a triangulation these are precisely the two nonrepetition conditions. -/
structure Cells (D V E F : Type) where
  vertex : D → V
  edge : D → E
  face : D → F
  tail_unique : ∀ a b, vertex a=vertex b → edge a=edge b → a=b
  row_unique : ∀ a b, face a=face b → edge a=edge b → a=b

abbrev Cell (V E F : Type) := V ⊕ (E ⊕ F)

def Cells.start (X : Cells D V E F) : Flag D → Cell V E F
  | (d,.vertex) => .inl (X.vertex d)
  | (d,.toVertex) | (d,.toFace) => .inr (.inl (X.edge d))
  | (d,.face) => .inr (.inr (X.face d))

def Cells.graph (X : Cells D V E F) : SimpleGraph (Cell V E F) where
  Adj a b := ∃ p, X.start p=a ∧ X.start (flip p)=b
  symm := by
    constructor
    rintro _ _ ⟨⟨d,t⟩,rfl,rfl⟩
    refine ⟨flip (d,t),rfl,?_⟩; cases t <;> rfl
  loopless := by
    constructor; rintro a ⟨⟨d,t⟩,rfl,h⟩
    cases t <;> simp [Cells.start,flip,flipTag] at h

private def asDart (X : Cells D V E F) (p : Flag D) : X.graph.Dart :=
  ⟨(X.start p,X.start (flip p)),p,rfl,rfl⟩

private theorem dart_bij (X : Cells D V E F) : Function.Bijective (asDart X) := by
  constructor
  · rintro ⟨d,t⟩ ⟨u,v⟩ eq
    have a := congrArg (fun h : X.graph.Dart => h.fst) eq
    have b := congrArg (fun h : X.graph.Dart => h.snd) eq
    change X.start (d,t)=X.start (u,v) at a
    change X.start (flip (d,t))=X.start (flip (u,v)) at b
    cases t <;> cases v <;> simp [Cells.start,flip,flipTag] at a b ⊢ <;> first
      | exact X.tail_unique _ _ a b | exact X.tail_unique _ _ b a
      | exact X.row_unique _ _ a b | exact X.row_unique _ _ b a
  · intro z
    obtain ⟨p,tail,head⟩ := z.adj
    exact ⟨p,SimpleGraph.Dart.ext _ _ (Prod.ext tail head)⟩

/-- Planarity of the *labelled simple incidence graph* with vertex–midpoint
and midpoint–face edges. This exhibits a genuine upstream `PlaneMap`. -/
theorem graph_planar [Finite D] (σ α : Perm D) (undo : ∀ x, α (α x)=x)
    (zero : eulerDefect σ α=0) (X : Cells D V E F)
    (vert : ∀ a b, X.vertex a=X.vertex b ↔ SameCycle σ a b)
    (edge : ∀ a b, X.edge a=X.edge b ↔ SameCycle α a b)
    (face_ : ∀ a b, X.face a=X.face b ↔ SameCycle (σ*α) a b) : IsPlanar X.graph := by
  let e := Equiv.ofBijective (asDart X) (dart_bij X)
  let θ := turn σ α undo
  have tvirt (p) : e p = asDart X p := rfl
  have twin : e.permCongr flip = dartSymm X.graph := by
    ext1 z
    obtain ⟨⟨d,t⟩,rfl⟩ := e.surjective z
    rw [permCongr_apply,e.symm_apply_apply,tvirt,tvirt]
    cases t <;> rfl
  have hold (p : Flag D) : X.start (θ p)=X.start p := by
    obtain ⟨d,t⟩ := p
    have hface : X.face ((σ*α).symm d)=X.face d := (face_ ..).mpr
      (by simpa using step (σ*α) ((σ*α).symm d))
    cases t <;> simp only [θ,turn,Equiv.coe_fn_mk,Cells.start,Sum.inl.injEq,Sum.inr.injEq]
    · exact (vert ..).mpr (step σ d).symm
    · exact hface
    · exact (edge ..).mpr (step α d).symm
  refine ⟨⟨e.permCongr θ,⟨?_,?_⟩,?_⟩⟩
  · intro z
    obtain ⟨p,rfl⟩ := e.surjective z
    rw [permCongr_apply,e.symm_apply_apply]
    exact hold p
  · intro x y eq
    obtain ⟨⟨d,t⟩,rfl⟩ := e.surjective x
    obtain ⟨⟨u,v⟩,rfl⟩ := e.surjective y
    apply (sameCycle_permCongr_iff ..).mp
    apply connected_kind
    change X.start (d,t)=X.start (u,v) at eq
    have K {x y : D} (h : X.face x=X.face y) : orbit (σ*α).symm x=orbit (σ*α).symm y :=
      Quotient.sound (s := SameCycle.setoid (σ*α).symm) (sameCycle_inv.mpr ((face_ ..).mp h))
    cases t <;> cases v <;> simp [Cells.start,kind] at eq ⊢ <;> first
      | exact K eq
      | exact Quotient.sound (s := SameCycle.setoid σ) ((vert ..).mp eq)
      | exact Quotient.sound (s := SameCycle.setoid α) ((edge ..).mp eq)
  · rw [← twin,eulerDefect_permCongr]
    exact planar σ α undo zero

#print axioms graph_planar
end Recognition.FlagRotation
