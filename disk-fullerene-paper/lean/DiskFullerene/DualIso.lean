import DiskFullerene.EndTriangles
import DiskFullerene.CutSides

namespace DiskFullerene.Dual
open EndLabels Separation

theorem common_edge_at {M} (G : IsDiskFullerene M h) (hh : 3≤h) {u : Fin M.ord}
    {f g : Face M} (fg : f≠g) (uf : f∈triangle u) (ug : g∈triangle u) :
    ∃ e : Edge M, Across (dual G) e f g ∧ (u=(primal G e).1 ∨ u=(primal G e).2) := by
  obtain ⟨a,b,⟨p,q,ip,tr,rfl,rfl⟩,_,_,_,labels⟩ := corners_at G hh ((mem_triangle _ _).mp uf)
  have incoming := reverse_owner G ip
  have fq : incident M f (u.val,q) := tr ▸ incident_turn G ip
  rcases (labels g).mp ((mem_triangle _ _).mp ug) with eq|eq|eq
  · exact False.elim (fg eq.symm)
  · subst g
    obtain ⟨e,eo⟩ := repr_dart G (incident_dart G ip)
    refine ⟨e,crossTable G eo (Or.inl ⟨ip,incoming⟩),?_⟩
    rcases eo with eq|eq
    · exact Or.inr (Fin.ext (congrArg Prod.snd eq).symm)
    · exact Or.inl (Fin.ext (congrArg Prod.fst eq).symm)
  · subst g
    obtain ⟨e,eo⟩ := repr_dart G (incident_dart G fq)
    refine ⟨e,crossTable G eo (Or.inl ⟨fq,reverse_owner G fq⟩),?_⟩
    rcases eo with eq|eq
    · exact Or.inl (Fin.ext (congrArg Prod.fst eq).symm)
    · exact Or.inr (Fin.ext (congrArg Prod.snd eq).symm)

/-- Two distinct primal vertices are adjacent precisely when their
dual facial triangles share two vertices. -/
theorem adj_iff_shared_edge {M} (G : IsDiskFullerene M h) (hh : 3≤h) (u v : Fin M.ord) :
    M.adj u.val v.val ↔ u≠v ∧ ∃ f g : Face M, f≠g ∧
      f∈triangle u ∧ f∈triangle v ∧ g∈triangle u ∧ g∈triangle v := by
  constructor
  · intro edge
    have dart := dart_iff.mpr edge
    have left := owner_incident G dart
    have right := reverse_owner G left
    have ne := (dart_info G dart).2.2
    have A := sideEnds left; have B := sideEnds right
    exact ⟨fun eq => ne (congrArg Fin.val eq),_,_,opposite_faces_distinct G hh left right,
      (mem_triangle _ _).mpr A.1,(mem_triangle _ _).mpr A.2,(mem_triangle _ _).mpr B.2,(mem_triangle _ _).mpr B.1⟩
  · rintro ⟨ne,f,g,fg,uf,vf,ug,vg⟩
    obtain ⟨e,eu,uu⟩ := common_edge_at G hh fg uf ug
    obtain ⟨k,ev,vv⟩ := common_edge_at G hh fg vf vg
    have eq := uniqueAcross G hh eu ev
    subst k
    have forward := dart_iff.mp (endpoints_mem e)
    have back := dart_iff.mp (dart_reverse G (endpoints_mem e))
    rcases uu with U|U <;> rcases vv with V|V <;> rw [U,V] at ne ⊢
    · exact False.elim (ne rfl)
    · exact forward
    · exact back
    · exact False.elim (ne rfl)

/-- Isomorphism of the dual triangulations, given by its action on
vertices and on the unordered triples that actually bound faces. -/
structure TriangulationIso (M N : MapData) where
  f : Face M → Face N
  g : Face N → Face M
  left : ∀ i, g (f i)=i
  right : ∀ j, f (g j)=j
  maps : ∀ u : Fin M.ord, ∃ v : Fin N.ord, ∀ i, i∈triangle u ↔ f i∈triangle v
  covers : ∀ v : Fin N.ord, ∃ u : Fin M.ord, ∀ i, i∈triangle u ↔ f i∈triangle v

/-- The target in the manuscript is isomorphism of the original cubic
graphs. Matching the unordered dual facial triples suffices even if
the isomorphism reverses every local rotation. -/
theorem TriangulationIso.primal_iso {M N} {h k} (A : IsDiskFullerene M h) (B : IsDiskFullerene N k)
    (hh : 3≤h) (hk : 3≤k) (F : TriangulationIso M N) : GraphIso M N := by
  classical
  let f := fun u => (F.maps u).choose
  let g := fun v => (F.covers v).choose
  have agrees (u i) : i∈triangle u ↔ F.f i∈triangle (f u) := (F.maps u).choose_spec i
  have pre (v i) : i∈triangle (g v) ↔ F.f i∈triangle v := (F.covers v).choose_spec i
  have l (u) : g (f u)=u := same_triangle A hh (fun i => (pre (f u) i).trans (agrees u i).symm)
  have r (v) : f (g v)=v := by
    apply same_triangle B hk; intro j
    have := ((agrees (g v) (F.g j)).symm.trans (pre v (F.g j)))
    simpa only [F.right] using this
  refine ⟨f,g,l,r,fun u v => ?_⟩
  rw [adj_iff_shared_edge A hh,adj_iff_shared_edge B hk]
  constructor
  · rintro ⟨ne,i,j,ij,iu,iv,ju,jv⟩
    exact ⟨fun eq => ne (by simpa only [l] using congrArg g eq),F.f i,F.f j,
      fun eq => ij (by simpa only [F.left] using congrArg F.g eq),
      (agrees u i).mp iu,(agrees v i).mp iv,(agrees u j).mp ju,(agrees v j).mp jv⟩
  · rintro ⟨ne,i,j,ij,iu,iv,ju,jv⟩
    have lift {v t} (H : t∈triangle (f v)) : F.g t∈triangle v :=
      (agrees v (F.g t)).mpr (by simpa only [F.right] using H)
    exact ⟨fun eq => ne (congrArg f eq),F.g i,F.g j,
      fun eq => ij (by simpa only [F.right] using congrArg F.f eq),lift iu,lift iv,lift ju,lift jv⟩

end DiskFullerene.Dual
