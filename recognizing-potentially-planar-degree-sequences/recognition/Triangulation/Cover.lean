import Triangulation.Layers
import Triangulation.Stacking

namespace Recognition.Forward
open Recognition.Rigidity Recognition.Reduction Recognition.Layers Recognition.Stacking
variable {T : Table}
/-- Data for choosing the unfilled faces in one actual map. -/
structure Omission (R : Model T.degrees) (q : Test) where
  fill : Choice R.V
  hits : ∀ a, R.label a ∈ selectedLabels T q ↔ ∃ b c, vacant R.map fill a b c
  disjoint : ∀ a b c d e, vacant R.map fill a b c → vacant R.map fill a d e →
      (b=d ∧ c=e) ∨ (b=e ∧ c=d)

def allFaces (R : Model T.degrees) : Omission R full where
  fill _ := True
  hits _ := by simp [selectedLabels,full,vacant]
  disjoint _ _ _ _ _ f := False.elim (f.2 trivial)

structure Cover (R : Model T.degrees) (q : Test) where
  x : Fin q.group.length → R.V
  y : Fin q.group.length → R.V
  z : Fin q.group.length → R.V
  labX : ∀ i, R.label (x i) = q.group[i.val].marker
  labY : ∀ i, R.label (y i) = endpoint q.side q.group[i.val]
  labZ : ∀ i, R.label (z i) = T.fresh+i.val
  face : ∀ i, R.map.face (x i) (y i) (z i)

variable {R : Model T.degrees} {q : Test}

private def key (C : Cover R q) (i : Fin q.group.length) : R.V → Prop :=
  corners (C.x i) (C.y i) (C.z i)

private theorem cover_lookup (C : Cover R q) (i : Fin q.group.length) :
    let ls := selectedLabels T q
    let t := q.group.length
    ls[i.val]? = some (R.label (C.x i)) ∧ ls[t+i.val]? = some (R.label (C.y i)) ∧
      ls[2*t+i.val]? = some (R.label (C.z i)) := by
  dsimp only
  rw [C.labX,C.labY,C.labZ]
  have hi := i.isLt
  have eq₁ : q.group.length+i.val-q.group.length = i.val := by omega
  have eq₂ : 2*q.group.length+i.val-(q.group.length+q.group.length) = i.val := by omega
  simp only [selectedLabels,List.getElem?_append,List.length_append,List.length_map]
  simp [hi,show i.val<q.group.length+q.group.length by omega,
    show q.group.length+i.val < q.group.length+q.group.length by omega,
    show ¬q.group.length+i.val < q.group.length by omega,
    show ¬2*q.group.length+i.val < q.group.length+q.group.length by omega,
    eq₁,eq₂]

private theorem corner_index (C : Cover R q) (i : Fin q.group.length) (v : R.V) (hv : key C i v) :
    ∃ j, j % q.group.length = i.val ∧ (selectedLabels T q)[j]? = some (R.label v) := by
  have ⟨x,y,z⟩ := cover_lookup C i
  have hi := i.isLt
  rcases hv with rfl|rfl|rfl
  · exact ⟨_,Nat.mod_eq_of_lt hi,x⟩
  · exact ⟨_,by simp [Nat.mod_eq_of_lt hi],y⟩
  · exact ⟨_,by simp [Nat.add_mod,Nat.mod_eq_of_lt hi],z⟩

private theorem unique_corner (C : Cover R q) (nd : (selectedLabels T q).Nodup)
    (i j : Fin q.group.length) (v : R.V) (hi : key C i v) (hj : key C j v) : i=j := by
  obtain ⟨s,hs,es⟩ := corner_index C i v hi
  obtain ⟨t,ht,et⟩ := corner_index C j v hj
  have ⟨sb,sv⟩ := List.getElem?_eq_some_iff.mp es
  have ⟨tb,tv⟩ := List.getElem?_eq_some_iff.mp et
  have eq := nd.eq_of_getElem_eq sb tb (sv.trans tv.symm)
  exact Fin.ext (hs.symm.trans ((congrArg (· % q.group.length) eq).trans ht))

private theorem label_hit (C : Cover R q) (v : R.V) :
    R.label v ∈ selectedLabels T q ↔ ∃ i, key C i v := by
  constructor
  · intro h
    rcases List.mem_append.mp h with old|fresh
    · rcases List.mem_append.mp old with hx|hy
      · obtain ⟨m,hm,eq⟩ := List.mem_map.mp hx
        obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hm
        let i : Fin q.group.length := ⟨j,hj⟩
        exact ⟨i,Or.inl (R.inj _ _ (eq.symm.trans (C.labX i).symm))⟩
      · obtain ⟨m,hm,eq⟩ := List.mem_map.mp hy
        obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hm
        let i : Fin q.group.length := ⟨j,hj⟩
        exact ⟨i,Or.inr (.inl (R.inj _ _ (eq.symm.trans (C.labY i).symm)))⟩
    · obtain ⟨j,hj,eq⟩ := List.mem_range'.mp fresh
      let i : Fin q.group.length := ⟨j,hj⟩
      simp only [Nat.one_mul] at eq
      exact ⟨i,Or.inr (.inr (R.inj _ _ (eq.trans (C.labZ i).symm)))⟩
  · rintro ⟨i,h⟩
    obtain ⟨j,_,ej⟩ := corner_index C i v h
    exact List.mem_iff_getElem.mpr (by obtain ⟨b,eq⟩ := List.getElem?_eq_some_iff.mp ej; exact ⟨j,b,eq⟩)

/-- Leave precisely the unordered faces specified by the cover unstellated.
The concrete no-duplicate label list proves that two different face choices
cannot share a vertex. -/
noncomputable def Cover.omission (C : Cover R q) (nd : (selectedLabels T q).Nodup) : Omission R q := by
  classical
  let fill : Choice R.V := fun K => ¬∃ i, K=key C i
  have vacant_iff (a b c : R.V) :
      vacant R.map fill a b c ↔ R.map.face a b c ∧ ∃ i, corners a b c = key C i := by
    simp [vacant,fill]
  refine ⟨fill,?_,?_⟩
  · intro a
    rw [label_hit C]
    constructor
    · rintro ⟨i,h⟩
      have f := C.face i
      rcases h with rfl|rfl|rfl
      · exact ⟨_,_,(vacant_iff ..).mpr ⟨f,i,rfl⟩⟩
      · refine ⟨_,_,(vacant_iff ..).mpr ⟨R.map.rot f,i,?_⟩⟩
        funext v; apply propext; unfold key corners; grind
      · refine ⟨_,_,(vacant_iff ..).mpr ⟨R.map.rot (R.map.rot f),i,?_⟩⟩
        funext v; apply propext; unfold key corners; grind
    · rintro ⟨b,c,h⟩
      obtain ⟨_,i,k⟩ := (vacant_iff ..).mp h
      exact ⟨i,by rw [←k]; exact Or.inl rfl⟩
  · intro a b c d e f g
    obtain ⟨F,i,eq⟩ := (vacant_iff ..).mp f
    obtain ⟨G,j,eq'⟩ := (vacant_iff ..).mp g
    have h := unique_corner C nd i j a (by rw [←eq]; exact Or.inl rfl)
      (by rw [←eq']; exact Or.inl rfl)
    subst j
    have H := eq.trans eq'.symm
    have mem (z : R.V) : corners a b c z ↔ corners a d e z := by rw [H]
    have := mem b; have := mem c
    have := R.map.distinct F; have := R.map.distinct (R.map.rot F); have := R.map.distinct (R.map.rot (R.map.rot F))
    unfold corners at *
    grind only

end Recognition.Forward
