import TargetLanguages
import StackedHistory

/-! Precisely stated interfaces to the classical geometric realization and
polarity theorems. The reduction, acceptance and positive truncation promise
below are deductions; only realization of an individual polytope and the
local operation at a single corner are supplied by geometry. -/

namespace Recognition.TargetLanguages
open SparseBoundary Recognition.Wagner LeanPool.K5MinorFreeChoosability

/-- An object of `P n` is a simple convex three-polytope with its facets
bijectively labelled by `Fin n`. Incidence duality reads each labelled facet
size from the degree of the corresponding primal vertex. -/
structure SteinitzPolarity (P : Nat → Type*) where
  size {n} : P n → Fin n → Nat
  dual {n} : P n → (G : Graph n) → PlaneMap (toSimple G) → Prop
  primal {n} (p : P n) : ∃ (G : Graph n) (M : PlaneMap (toSimple G)),
    4≤n ∧ Maximal IsPlanar (toSimple G) ∧ dual p G M
  realize {n} (G : Graph n) (M : PlaneMap (toSimple G)) :
    4≤n → Maximal IsPlanar (toSimple G) → ∃ p, dual p G M
  incidence {n} {p : P n} {G : Graph n} {M : PlaneMap (toSimple G)} :
    dual p G M → ∀ v, size p v=G.degree v

def FaceList {P} (S : SteinitzPolarity P) (ds : List Nat) : Prop :=
  ∃ p : P ds.length,∀ v : Fin ds.length,S.size p v=ds[v]

theorem geometric_face_list {P} (S : SteinitzPolarity P) (ds : List Nat) :
    FaceList S ds ↔ PolyhedralRow ds := by
  rw [polyhedral_row_iff]
  constructor
  · rintro ⟨p,r⟩
    obtain ⟨G,M,n,m,dual⟩ := S.primal p
    have rg : G.Realizes ds := fun v => (S.incidence dual v).symm.trans (r v)
    obtain ⟨guard,flat⟩ := (maximal_row_iff ds).mp ⟨G,rg,m⟩
    exact ⟨n,by simpa [guardRow,show ¬ ds.length<4 by omega] using guard,flat⟩
  · rintro ⟨n,t,flat⟩
    obtain ⟨G,reg,m⟩ := (maximal_row_iff ds).mpr
      ⟨by simp [guardRow,show ¬ ds.length<4 by omega,t],flat⟩
    obtain ⟨M⟩ := m.1
    obtain ⟨p,h⟩ := S.realize G M n m
    exact ⟨p,fun v => (S.incidence h v).trans (reg v)⟩

/-- Classical duality under a single small cut. The incidence relation
pairs each mesh vertex with a facet and each triangular mesh face with a
corner. The replacement in `SourceMap.stack` deletes precisely that corner
and introduces the three incidences around its new triangular facet. -/
structure CornerPolarity (P : Type*) where
  profile : P → Multiset Nat
  isTetrahedron : P → Prop
  cut : P → P → Prop
  dualMesh : P → SourceMap.Mesh → Prop
  base : ∃ p,isTetrahedron p ∧ dualMesh p SourceMap.tetra
  atCorner {p M f x} : dualMesh p M → M.face f → ¬ M.vertex x →
    ∃ q,cut p q ∧ dualMesh q (SourceMap.stack M f x)
  sizes {p M} : dualMesh p M → ∀ names : List Nat,names.Nodup →
    (∀v,M.vertex v ↔ v∈names) →
      profile p=(names.map (fun v => (M.neighbors v).length) : Multiset Nat)

theorem truncated_realization {P} (C : CornerPolarity P) {ds : Multiset Nat}
    (h : StackedHistory.SequentialRealization ds) : ∃ first last,
      C.isTetrahedron first ∧ Relation.ReflTransGen C.cut first last ∧ C.profile last=ds := by
  obtain ⟨M,hist,ns,nd,names,degs⟩ := h
  have reach {N} (history : SourceMap.Stacked N) :
      ∃ a b,C.isTetrahedron a ∧ Relation.ReflTransGen C.cut a b ∧ C.dualMesh b N := by
    induction history with
    | tetra => obtain ⟨p,t,m⟩ := C.base;exact ⟨p,p,t,.refl,m⟩
    | insert prior face fresh ih =>
      obtain ⟨a,b,start,path,d⟩ := ih
      obtain ⟨q,step,next⟩ := C.atCorner d face fresh
      exact ⟨a,q,start,path.tail step,next⟩
  obtain ⟨a,b,t,path,d⟩ := reach hist
  exact ⟨a,b,t,path,(C.sizes d ns nd names).trans degs⟩

theorem polytope_certificate {P} (S : SteinitzPolarity P) (ds : List Nat) :
    FaceList S ds ↔ ∃ w : List Bool,w.length≤5*(ds.length+1)^3 ∧
      checkPolyhedral ds w=true :=
  (geometric_face_list S ds).trans (polyhedral_certificate ds)

end Recognition.TargetLanguages
