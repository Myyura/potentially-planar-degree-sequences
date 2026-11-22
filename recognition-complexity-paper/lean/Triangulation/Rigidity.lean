import Std

/-!
# Peeling cubic vertices

A triangular map is given by its oriented listings of triangular faces. The
two sides of an edge have distinct opposite corners, and the dual is connected.
These local arguments apply to closed simplicial triangulations of any genus.
-/
namespace Recognition.Rigidity

structure Triangle (V : Type) where
  a : V
  b : V
  c : V

/-- Moves within an unordered face, or across one of its edges. -/
inductive Walk {V : Type} (F : V → V → V → Prop) (s : Triangle V) : Triangle V → Prop
  | nil : Walk F s s
  | rot : Walk F s ⟨a,b,c⟩ → Walk F s ⟨b,c,a⟩
  | flip : Walk F s ⟨a,b,c⟩ → Walk F s ⟨b,a,c⟩
  | cross : Walk F s ⟨a,b,c⟩ → F a b d → Walk F s ⟨a,b,d⟩

structure Map (V : Type) where
  face : V → V → V → Prop
  rot : face a b c → face b c a
  flip : face a b c → face b a c
  distinct : face a b c → a ≠ b
  twoSides : face a b c → ∃ d, d ≠ c ∧ face a b d ∧ ∀ e, face a b e → e = c ∨ e = d
  incident : ∀ a, ∃ b c, face a b c
  connected : ∀ {a b c u v w}, face a b c → face u v w → Walk face ⟨a,b,c⟩ ⟨u,v,w⟩

variable {V : Type} (M : Map V)

def Map.adj (x y : V) : Prop := ∃ z, M.face x y z

def Map.Three (x a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ ∀ z, M.adj x z ↔ z = a ∨ z = b ∨ z = c

def Map.Cubic (x : V) : Prop := ∃ a b c, M.Three x a b c

private theorem exhaust {a b c d e : V} (f : M.face a b c) (g : M.face a b d)
    (ne : c ≠ d) (h : M.face a b e) : e = c ∨ e = d := by
  obtain ⟨w, _, _, hw⟩ := M.twoSides f
  have := hw d g
  have := hw e h
  grind

private theorem other {x a b c : V} (H : M.Three x a b c) :
    M.face x a b ∧ M.face x b c ∧ M.face x c a := by
  obtain ⟨hab,hbc,hac,hn⟩ := H
  have mk : ∀ u v w, (u = a ∨ u = b ∨ u = c) →
      (v = a ∨ v = b ∨ v = c) → (w = a ∨ w = b ∨ w = c) →
      u ≠ v → v ≠ w → u ≠ w → M.face x u v := by
    intro u v w hu hv hw huv hvw huw
    obtain ⟨e,he⟩ := (hn u).mpr hu
    obtain ⟨f,hfe,hf,_⟩ := M.twoSides he
    have he' := M.rot he
    have hf' := M.rot hf
    have h1 := M.distinct he'
    have h2 := M.distinct hf'
    have rev : ∀ {i j k}, M.face i j k → M.face i k j := fun g => M.flip (M.rot (M.rot g))
    have h3 := (hn e).mp ⟨u,rev he⟩
    have h4 := (hn f).mp ⟨u,rev hf⟩
    grind
  exact ⟨mk a b c (by simp) (by simp) (by simp) hab hbc hac,
    mk b c a (by simp) (by simp) (by simp) hbc (Ne.symm hac) (Ne.symm hab),
    mk c a b (by simp) (by simp) (by simp) (Ne.symm hac) hab (Ne.symm hbc)⟩

theorem cubic_faces {x a b c : V} (H : M.Three x a b c) :
    M.face x a b ∧ M.face x b c ∧ M.face x c a := other M H

private theorem cover (S : V → Prop) {i j k : V} (f : M.face i j k)
    (seed : S i ∧ S j ∧ S k)
    (closed : ∀ a b c, M.face a b c → S a → S b → S c)
    (v : V) : S v := by
  obtain ⟨p,q,g⟩ := M.incident v
  have reach := M.connected f g
  have aux : ∀ {t : Triangle V}, Walk M.face ⟨i,j,k⟩ t → S t.a ∧ S t.b ∧ S t.c := by
    intro t walk
    induction walk with
    | nil => exact seed
    | rot _ ih => exact ⟨ih.2.1, ih.2.2, ih.1⟩
    | flip _ ih => exact ⟨ih.2.1, ih.1, ih.2.2⟩
    | cross _ h ih => exact ⟨ih.1, ih.2.1, closed _ _ _ h ih.1 ih.2.1⟩
  exact (aux reach).1

private theorem sq {a b c : V} (h : M.face a b c) :
    M.face a c b ∧ M.face b c a ∧ M.face b a c ∧ M.face c a b ∧ M.face c b a :=
  ⟨M.flip (M.rot (M.rot h)), M.rot h, M.flip h, M.rot (M.rot h), M.flip (M.rot h)⟩

private theorem tetra {x a b c : V} (H : M.Three x a b c) (g : M.face a b c) (v : V) :
    v = x ∨ v = a ∨ v = b ∨ v = c := by
  obtain ⟨f₁,f₂,f₃⟩ := other M H
  have p₁ := sq M f₁
  have p₂ := sq M f₂
  have p₃ := sq M f₃
  have p₄ := sq M g
  have ⟨hab,hbc,hac,_⟩ := H
  have hxa := M.distinct f₁
  have hxb := M.distinct f₂
  have hxc := M.distinct f₃
  let S := fun w => w = x ∨ w = a ∨ w = b ∨ w = c
  apply cover M S f₁ (by simp [S]) _ v
  intro u w t ht hu hw
  have huw := M.distinct ht
  have sep : ∀ i j, i ≠ j → M.face u w i → M.face u w j → t = i ∨ t = j :=
    fun _ _ h hi hj => exhaust M hi hj h ht
  simp only [S] at *
  rcases hu with h | h | h | h <;> subst u <;>
    rcases hw with h | h | h | h <;> subst w <;>
    grind


private theorem three_of_named {x a b c : V} (H : M.Cubic x)
    (ab : a ≠ b) (bc : b ≠ c) (ac : a ≠ c)
    (e₁ : M.adj x a) (e₂ : M.adj x b) (e₃ : M.adj x c) : M.Three x a b c := by
  obtain ⟨i,j,k,_,_,_,N⟩ := H
  refine ⟨ab,bc,ac,?_⟩
  have := (N a).mp e₁
  have := (N b).mp e₂
  have := (N c).mp e₃
  intro z
  specialize N z
  grind

/-- Adjacent cubic vertices force the entire map to be the tetrahedron. -/
theorem cubic_independent (large : ∀ x a b c : V, ∃ z, z ≠ x ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c)
    {x y : V} (X : M.Cubic x) (Y : M.Cubic y) : ¬ M.adj x y := by
  rintro ⟨a,f⟩
  obtain ⟨b,hba,g,_⟩ := M.twoSides f
  have pf := sq M f
  have pg := sq M g
  have A : M.Three x y a b :=
    three_of_named M X (M.distinct (M.rot f)) (Ne.symm hba) (M.distinct (M.rot g))
      ⟨a,f⟩ ⟨y,pf.1⟩ ⟨y,pg.1⟩
  have B : M.Three y x a b :=
    three_of_named M Y (M.distinct pf.1) (Ne.symm hba) (M.distinct pg.1)
      ⟨a,M.flip f⟩ ⟨x,M.rot f⟩ ⟨x,M.rot g⟩
  have cap := (other M B).2.1
  obtain ⟨z,hz⟩ := large x y a b
  have := tetra M A cap z
  grind

theorem restored_triangle_was_absent
    (large : ∀ x a b c : V, ∃ z, z ≠ x ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c)
    {x a b c : V} (H : M.Three x a b c) : ¬ M.face a b c := by
  intro cap
  obtain ⟨z,hz⟩ := large x a b c
  have := tetra M H cap z
  grind

/-- Two distinct cubic stars with identical corners close up a triangular
bipyramid. A fourth surviving vertex rules this out in the reduction. -/
theorem common_corners {x y a b c : V} (H : M.Three x a b c) (K : M.Three y a b c)
    (xy : x ≠ y) (v : V) : v = x ∨ v = y ∨ v = a ∨ v = b ∨ v = c := by
  obtain ⟨f₁,f₂,f₃⟩ := other M H
  obtain ⟨g₁,g₂,g₃⟩ := other M K
  have p₁ := sq M f₁
  have p₂ := sq M f₂
  have p₃ := sq M f₃
  have q₁ := sq M g₁
  have q₂ := sq M g₂
  have q₃ := sq M g₃
  have ⟨hab,hbc,hac,N⟩ := H
  have hxa := M.distinct f₁
  have hxb := M.distinct f₂
  have hxc := M.distinct f₃
  have hya := M.distinct g₁
  have hyb := M.distinct g₂
  have hyc := M.distinct g₃
  let S := fun w => w = x ∨ w = y ∨ w = a ∨ w = b ∨ w = c
  apply cover M S f₁ (by simp [S]) _ v
  intro u w t ht hu hw
  have huw := M.distinct ht
  have sep : ∀ i j, i ≠ j → M.face u w i → M.face u w j → t = i ∨ t = j :=
    fun _ _ ne hi hj => exhaust M hi hj ne ht
  have hxy : ¬ M.adj x y := by
    have := N y
    grind
  have ed : M.adj u w := ⟨t,ht⟩
  have de : M.adj w u := ⟨t,M.flip ht⟩
  simp only [S] at *
  rcases hu with h | h | h | h | h <;> subst u <;>
    rcases hw with h | h | h | h | h <;> subst w <;> grind

/-- A row records the base degree, intended degree, number of unoccupied
incident faces, and the single selection bit. Using addition in the interface
also admits base degree zero without truncated-subtraction ambiguities. -/
structure Row where
  base : Nat
  target : Nat
  missed : Nat
  bit : Nat
  small : bit ≤ 1
  equation : 2 * base + bit = 2 * target + missed

private theorem row_ge (r : Row) : r.target ≤ r.base := by
  have := r.small
  have := r.equation
  omega

private theorem sum_ge (rows : List Row) :
    (rows.map Row.target).sum ≤ (rows.map Row.base).sum := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (row_ge r) ih

theorem omitted_incidence_rigidity (rows : List Row)
    (euler : (rows.map Row.base).sum = (rows.map Row.target).sum) :
    ∀ r ∈ rows, r.base = r.target ∧ r.missed = r.bit := by
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons] at euler
    have := row_ge r
    have := sum_ge rs
    have tail : (rs.map Row.base).sum = (rs.map Row.target).sum := by omega
    intro s hs
    rcases List.mem_cons.mp hs with h | h
    · subst s
      have := r.equation
      omega
    · exact ih tail s h


/-- An independent family of cubic stars is deleted at once. Four old vertices
remain, so two restored faces cannot have the same boundary. -/
structure Peeling (M : Map V) where
  fresh : V → Prop
  cubic : ∀ x, fresh x → M.Cubic x
  fourOld : ∀ a b c, ∃ v, ¬ fresh v ∧ v ≠ a ∧ v ≠ b ∧ v ≠ c

variable {M} (P : Peeling M)

private theorem five {x : V} (hx : P.fresh x) (a b c d : V) :
    ∃ v, v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ d := by
  classical
  by_cases ha : x = a
  · obtain ⟨v,h⟩ := P.fourOld b c d
    exact ⟨v,by grind⟩
  by_cases hb : x = b
  · obtain ⟨v,h⟩ := P.fourOld a c d
    exact ⟨v,by grind⟩
  by_cases hc : x = c
  · obtain ⟨v,h⟩ := P.fourOld a b d
    exact ⟨v,by grind⟩
  by_cases hd : x = d
  · obtain ⟨v,h⟩ := P.fourOld a b c
    exact ⟨v,by grind⟩
  exact ⟨x,ha,hb,hc,hd⟩

private theorem old_neighbor {x y : V} (hx : P.fresh x) (h : M.adj x y) : ¬ P.fresh y :=
  fun hy => cubic_independent M (five P hx) (P.cubic x hx) (P.cubic y hy) h

abbrev Peeling.Old (P : Peeling M) := {x : V // ¬ P.fresh x}

/-- Faces surviving deletion and triangles exposed by a deleted star. -/
def Peeling.face (a b c : P.Old) : Prop :=
  M.face a.val b.val c.val ∨ ∃ x, P.fresh x ∧ M.Three x a.val b.val c.val

private theorem three_rot {x a b c : V} (h : M.Three x a b c) : M.Three x b c a := by
  obtain ⟨hab,hbc,hac,n⟩ := h
  exact ⟨hbc,Ne.symm hac,Ne.symm hab,fun z => by specialize n z; grind⟩

private theorem three_flip {x a b c : V} (h : M.Three x a b c) : M.Three x b a c := by
  obtain ⟨hab,hbc,hac,n⟩ := h
  exact ⟨Ne.symm hab,hac,hbc,fun z => by specialize n z; grind⟩

theorem peeled_rot {a b c : P.Old} : P.face a b c → P.face b c a := by
  rintro (h | ⟨x,hx,h⟩)
  · exact Or.inl (M.rot h)
  · exact Or.inr ⟨x,hx,three_rot h⟩

theorem peeled_flip {a b c : P.Old} : P.face a b c → P.face b a c := by
  rintro (h | ⟨x,hx,h⟩)
  · exact Or.inl (M.flip h)
  · exact Or.inr ⟨x,hx,three_flip h⟩

theorem peeled_distinct {a b c : P.Old} : P.face a b c → a ≠ b := by
  rintro (h | ⟨_,_,h⟩)
  · exact fun e => M.distinct h (congrArg Subtype.val e)
  · exact fun e => h.1 (congrArg Subtype.val e)

/-- Transfer the two opposite corners of a surviving edge through deletion. -/
private def Opposite (a b : P.Old) (z : V) (c : P.Old) : Prop :=
  c.val = z ∨ (P.fresh z ∧ M.Three z a.val b.val c.val)

private theorem opposite_exists {a b : P.Old} {z : V} (g : M.face a.val b.val z) :
    ∃ c, Opposite P a b z c := by
  classical
  by_cases fresh : P.fresh z
  · have A : M.adj z a.val := ⟨b.val, M.rot (M.rot g)⟩
    have B : M.adj z b.val := ⟨a.val, M.flip (M.rot g)⟩
    obtain ⟨i,j,k,hij,hjk,hik,N⟩ := P.cubic z fresh
    have ab := M.distinct g
    have := (N _).mp A
    have := (N _).mp B
    have third : ∃ w, (w = i ∨ w = j ∨ w = k) ∧ a.val ≠ w ∧ b.val ≠ w := by
      by_cases hi : a.val ≠ i ∧ b.val ≠ i
      · exact ⟨i,by grind⟩
      by_cases hj : a.val ≠ j ∧ b.val ≠ j
      · exact ⟨j,by grind⟩
      exact ⟨k,by grind⟩
    obtain ⟨w,hw,haw,hbw⟩ := third
    have W := (N w).mpr hw
    exact ⟨⟨w,old_neighbor P fresh W⟩, Or.inr ⟨fresh,
      three_of_named M (P.cubic z fresh) ab hbw haw A B W⟩⟩
  · exact ⟨⟨z,fresh⟩,Or.inl rfl⟩

private theorem opposite_functional {a b c d : P.Old} {z : V}
    (h : Opposite P a b z c) (k : Opposite P a b z d) : c = d := by
  apply Subtype.ext
  have hc := c.property
  have hd := d.property
  rcases h with h | ⟨hz,h⟩ <;> rcases k with k | ⟨fz,k⟩ <;> try grind
  have := (h.2.2.2 d.val).mp ((k.2.2.2 d.val).mpr (by simp))
  have := k.2.1
  have := k.2.2.1
  grind

private theorem opposite_injective {a b c : P.Old} {z w : V}
    (f : M.face a.val b.val z) (g : M.face a.val b.val w)
    (h : Opposite P a b z c) (k : Opposite P a b w c) : z = w := by
  classical
  rcases h with h | ⟨hz,h⟩ <;> rcases k with k | ⟨hw,k⟩
  · exact h.symm.trans k
  · exact False.elim (restored_triangle_was_absent M (five P hw) k (h.symm ▸ f))
  · exact False.elim (restored_triangle_was_absent M (five P hz) h (k.symm ▸ g))
  · apply Classical.byContradiction
    intro ne
    obtain ⟨v,hv⟩ := P.fourOld a.val b.val c.val
    have := common_corners M h k ne v
    grind

private theorem face_iff_opposite {a b c : P.Old} :
    P.face a b c ↔ ∃ z, M.face a.val b.val z ∧ Opposite P a b z c := by
  constructor
  · rintro (h | ⟨x,hx,h⟩)
    · exact ⟨_,h,Or.inl rfl⟩
    · exact ⟨x,M.rot (other M h).1,Or.inr ⟨hx,h⟩⟩
  · rintro ⟨z,f,h | h⟩
    · exact Or.inl (h.symm ▸ f)
    · exact Or.inr ⟨z,h⟩

theorem peeled_edges {a b : P.Old} : (∃ c, P.face a b c) ↔ M.adj a.val b.val := by
  constructor
  · rintro ⟨c,g⟩
    obtain ⟨z,f,_⟩ := (face_iff_opposite P).mp g
    exact ⟨z,f⟩
  · rintro ⟨z,f⟩
    obtain ⟨c,h⟩ := opposite_exists P f
    exact ⟨c,(face_iff_opposite P).mpr ⟨z,f,h⟩⟩

theorem peeled_two_sides {a b c : P.Old} (h : P.face a b c) :
    ∃ d, d ≠ c ∧ P.face a b d ∧ ∀ e, P.face a b e → e = c ∨ e = d := by
  obtain ⟨z,f,zc⟩ := (face_iff_opposite P).mp h
  obtain ⟨w,wz,g,sides⟩ := M.twoSides f
  obtain ⟨d,wd⟩ := opposite_exists P g
  refine ⟨d,fun e => wz (opposite_injective P g f wd (e ▸ zc)),
    (face_iff_opposite P).mpr ⟨w,g,wd⟩,?_⟩
  intro e he
  obtain ⟨u,k,ue⟩ := (face_iff_opposite P).mp he
  rcases sides u k with rfl | rfl
  · exact Or.inl (opposite_functional P ue zc)
  · exact Or.inr (opposite_functional P ue wd)


def Triangle.contains {V : Type} (s : Triangle V) (v : V) : Prop :=
  v = s.a ∨ v = s.b ∨ v = s.c

private theorem walk_trans {U : Type} {F : U → U → U → Prop} {p q r}
    (h : Walk F p q) (k : Walk F q r) : Walk F p r := by
  induction k with
  | nil => exact h
  | rot _ ih => exact .rot ih
  | flip _ ih => exact .flip ih
  | cross _ f ih => exact .cross ih f

private theorem walk_pull {p q : Triangle P.Old} (h : Walk P.face p q)
    (f : P.face p.a p.b p.c) : P.face q.a q.b q.c ∧ Walk P.face q p := by
  induction h with
  | nil => exact ⟨f,.nil⟩
  | rot _ ih => exact ⟨peeled_rot P ih.1,walk_trans (.rot (.rot .nil)) ih.2⟩
  | flip _ ih => exact ⟨peeled_flip P ih.1,walk_trans (.flip .nil) ih.2⟩
  | cross _ g ih => exact ⟨g,walk_trans (.cross .nil ih.1) ih.2⟩

private theorem orient (s : Triangle P.Old) {u v : P.Old} (uv : u ≠ v)
    (hu : s.contains u) (hv : s.contains v) :
    ∃ w, Walk P.face s ⟨u,v,w⟩ := by
  obtain ⟨a,b,c⟩ := s
  change u = a ∨ u = b ∨ u = c at hu
  change v = a ∨ v = b ∨ v = c at hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first | contradiction | exact ⟨_,.nil⟩ | exact ⟨_,.rot .nil⟩ | exact ⟨_,.rot (.rot .nil)⟩
          | exact ⟨_,.flip .nil⟩ | exact ⟨_,.flip (.rot .nil)⟩ | exact ⟨_,.rot (.flip .nil)⟩

private theorem across {s t : Triangle P.Old} (f : P.face t.a t.b t.c)
    {u v : P.Old} (uv : u ≠ v) (u₁ : s.contains u) (v₁ : s.contains v)
    (u₂ : t.contains u) (v₂ : t.contains v) : Walk P.face s t := by
  obtain ⟨c,h⟩ := orient P s uv u₁ v₁
  obtain ⟨d,k⟩ := orient P t uv u₂ v₂
  obtain ⟨g,l⟩ := walk_pull P k f
  exact walk_trans (.cross h g) l

/-- The image of an original triangle across simultaneous removal of its
cubic corners. All old corners survive. A fresh corner records its whole link. -/
private structure Image (s : Triangle V) (t : Triangle P.Old) : Prop where
  valid : P.face t.a t.b t.c
  keep : ∀ z : P.Old, s.contains z.val → t.contains z
  link : ∀ x, s.contains x → P.fresh x → ∀ z : P.Old, M.adj x z.val ↔ t.contains z

private theorem old_image {a b c : P.Old} (h : M.face a.val b.val c.val) :
    Image P ⟨a.val,b.val,c.val⟩ ⟨a,b,c⟩ := by
  refine ⟨Or.inl h,?_,?_⟩
  · intro v hv
    rcases hv with e | e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Or.inl (Subtype.ext e))
    · exact Or.inr (Or.inr (Subtype.ext e))
  · intro x hx fresh
    rcases hx with rfl | rfl | rfl
    · exact False.elim (a.property fresh)
    · exact False.elim (b.property fresh)
    · exact False.elim (c.property fresh)

private theorem cubic_image {a b c : P.Old} {x : V} (hx : P.fresh x)
    (h : M.Three x a.val b.val c.val) :
    Image P ⟨a.val,b.val,x⟩ ⟨a,b,c⟩ := by
  refine ⟨Or.inr ⟨x,hx,h⟩,?_,?_⟩
  · intro v hv
    rcases hv with e | e | e
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Or.inl (Subtype.ext e))
    · exact False.elim (v.property (e ▸ hx))
  · intro z hz fresh v
    rcases hz with rfl | rfl | rfl
    · exact False.elim (a.property fresh)
    · exact False.elim (b.property fresh)
    · simpa [Triangle.contains,Subtype.ext_iff] using h.2.2.2 v.val

private theorem transport_image {s t : Triangle V} {q : Triangle P.Old}
    (i : Image P s q) (incl : ∀ z, t.contains z → s.contains z) : Image P t q :=
  ⟨i.valid,fun z hz => i.keep z (incl _ hz), fun x hx => i.link x (incl _ hx)⟩

private theorem image_of_old_edge (a b : P.Old) {z : V} (h : M.face a.val b.val z) :
    ∃ t, Image P ⟨a.val,b.val,z⟩ t := by
  obtain ⟨c,hc | ⟨hz,hc⟩⟩ := opposite_exists P h
  · subst z
    exact ⟨_,old_image P h⟩
  · exact ⟨_,cubic_image P hz hc⟩

private theorem image_exists {a b c : V} (h : M.face a b c) : ∃ t, Image P ⟨a,b,c⟩ t := by
  classical
  by_cases ha : P.fresh a
  · have hb := old_neighbor P ha (show M.adj a b from ⟨c,h⟩)
    have hc := old_neighbor P ha (show M.adj a c from ⟨b,(sq M h).1⟩)
    obtain ⟨t,i⟩ := image_of_old_edge P ⟨b,hb⟩ ⟨c,hc⟩ (M.rot h)
    exact ⟨t,transport_image P i (by simp only [Triangle.contains]; grind)⟩
  by_cases hb : P.fresh b
  · have hc := old_neighbor P hb (show M.adj b c from ⟨a,M.rot h⟩)
    obtain ⟨t,i⟩ := image_of_old_edge P ⟨c,hc⟩ ⟨a,ha⟩ (M.rot (M.rot h))
    exact ⟨t,transport_image P i (by simp only [Triangle.contains]; grind)⟩
  exact image_of_old_edge P ⟨a,ha⟩ ⟨b,hb⟩ h

private theorem along {s t : Triangle V} {p q : Triangle P.Old}
    (i : Image P s p) (j : Image P t q) {u v : V} (uv : u ≠ v)
    (us : s.contains u) (vs : s.contains v) (ut : t.contains u) (vt : t.contains v) :
    Walk P.face p q := by
  classical
  have tagged : ∀ x, s.contains x → t.contains x → P.fresh x → Walk P.face p q := by
    intro x sx tx fx
    have eqv : ∀ z, p.contains z → q.contains z :=
      fun z hz => (j.link x tx fx z).mp ((i.link x sx fx z).mpr hz)
    have a : p.contains p.a := Or.inl rfl
    have b : p.contains p.b := Or.inr (Or.inl rfl)
    exact across P j.valid (peeled_distinct P i.valid) a b (eqv _ a) (eqv _ b)
  by_cases hu : P.fresh u
  · exact tagged u us ut hu
  by_cases hv : P.fresh v
  · exact tagged v vs vt hv
  exact across P j.valid (fun e => uv (congrArg Subtype.val e))
    (i.keep ⟨u,hu⟩ us) (i.keep ⟨v,hv⟩ vs) (j.keep ⟨u,hu⟩ ut) (j.keep ⟨v,hv⟩ vt)

private theorem preimage {a b c : P.Old} (f : P.face a b c) :
    ∃ s : Triangle V, M.face s.a s.b s.c ∧ Image P s ⟨a,b,c⟩ := by
  rcases f with f | ⟨x,hx,h⟩
  · exact ⟨_,f,old_image P f⟩
  · exact ⟨_,M.rot (other M h).1,cubic_image P hx h⟩

theorem peeled_connected {a b c u v w : P.Old}
    (f : P.face a b c) (g : P.face u v w) : Walk P.face ⟨a,b,c⟩ ⟨u,v,w⟩ := by
  obtain ⟨s,hs,i⟩ := preimage P f
  obtain ⟨t,ht,j⟩ := preimage P g
  have lift : ∀ {r : Triangle V}, Walk M.face s r →
      M.face r.a r.b r.c ∧ ∀ q, Image P r q → Walk P.face ⟨a,b,c⟩ q := by
    intro r h
    induction h with
    | nil =>
      refine ⟨hs,fun q k => ?_⟩
      exact along P i k (M.distinct hs) (Or.inl rfl) (Or.inr (Or.inl rfl))
        (Or.inl rfl) (Or.inr (Or.inl rfl))
    | rot _ ih =>
      exact ⟨M.rot ih.1, fun q k => ih.2 q (transport_image P k (by simp only [Triangle.contains]; grind))⟩
    | flip _ ih =>
      exact ⟨M.flip ih.1, fun q k => ih.2 q (transport_image P k (by simp only [Triangle.contains]; grind))⟩
    | cross _ f' ih =>
      obtain ⟨p,jp⟩ := image_exists P ih.1
      refine ⟨f', fun q k => walk_trans (ih.2 p jp) ?_⟩
      exact along P jp k (M.distinct f') (Or.inl rfl) (Or.inr (Or.inl rfl))
        (Or.inl rfl) (Or.inr (Or.inl rfl))
  exact (lift (M.connected hs ht)).2 _ j

theorem peeled_incident (v : P.Old) : ∃ a b, P.face v a b := by
  classical
  obtain ⟨u,w,f⟩ := M.incident v.val
  by_cases hu : P.fresh u
  · have hw := old_neighbor P hu (show M.adj u w from ⟨_,M.rot f⟩)
    obtain ⟨b,g⟩ := (peeled_edges P (a := v) (b := ⟨w,hw⟩)).mpr ⟨u,(sq M f).1⟩
    exact ⟨_,b,g⟩
  obtain ⟨b,g⟩ := (peeled_edges P (a := v) (b := ⟨u,hu⟩)).mpr ⟨w,f⟩
  exact ⟨_,b,g⟩

/-- Simultaneous deletion yields another connected two-sided triangular map. -/
def Peeling.map : Map P.Old where
  face := P.face
  rot := peeled_rot P
  flip := peeled_flip P
  distinct := peeled_distinct P
  twoSides := peeled_two_sides P
  incident := peeled_incident P
  connected := peeled_connected P


/-- A finite vertex enumeration. No order on vertices is needed to count
an unoccupied face, since its two orientations at the vertex are counted. -/
structure Enumeration (V : Type) where
  vertices : List V
  unique : vertices.Nodup
  complete : ∀ v, v ∈ vertices

def mass {U : Type} (xs : List U) (f : U → Nat) : Nat := (xs.map f).sum

noncomputable def mark (p : Prop) : Nat := by
  classical
  exact if p then 1 else 0

private theorem mark_yes {q : Prop} (h : q) : mark q = 1 := by simp [mark,h]
private theorem mark_no {q : Prop} (h : ¬ q) : mark q = 0 := by simp [mark,h]
private theorem mark_congr {p q : Prop} (h : p ↔ q) : mark p = mark q := by rw [propext h]

private theorem mass_congr {U : Type} (xs : List U) {f g : U → Nat} (h : ∀ x, f x = g x) :
    mass xs f = mass xs g := by rw [funext h]

private theorem mass_plus {U : Type} (xs : List U) (f g : U → Nat) :
    mass xs (fun x => f x + g x) = mass xs f + mass xs g := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp only [mass,List.map_cons,List.sum_cons] at *; omega

private theorem mass_zero {U : Type} (xs : List U) : mass xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons a as ih => simpa [mass] using ih

private theorem mass_double {U : Type} (xs : List U) (f : U → Nat) :
    mass xs (fun v => 2 * f v) = 2 * mass xs f := by
  simpa only [Nat.two_mul] using mass_plus xs f f

private theorem mass_single_aux {U : Type} (xs : List U) (un : xs.Nodup) (a : U) :
    mass xs (fun z => mark (z = a)) = mark (a ∈ xs) := by
  induction xs with
  | nil => simp [mass,mark]
  | cons x xs ih =>
    have ⟨hx,ht⟩ := List.nodup_cons.mp un
    simp only [mass,List.map_cons,List.sum_cons] at *
    rw [ih ht]
    by_cases e : x = a
    · subst x
      simp [mark,hx]
    · rw [mark_no e,Nat.zero_add]
      apply mark_congr
      exact ⟨fun h => List.mem_cons_of_mem _ h,fun h => (List.mem_cons.mp h).resolve_left (Ne.symm e)⟩

private theorem mass_pair (E : Enumeration V) {u v : V} (uv : u ≠ v) :
    mass E.vertices (fun w => mark (w = u ∨ w = v)) = 2 := by
  have h : ∀ w : V, mark (w = u ∨ w = v) = mark (w = u) + mark (w = v) := by
    intro w
    by_cases a : w = u <;> by_cases b : w = v <;> simp [mark,a,b,uv,Ne.symm uv] <;> grind
  rw [mass_congr _ h, mass_plus, mass_single_aux _ E.unique, mass_single_aux _ E.unique]
  simp [mark,E.complete]

private theorem swap_mass {U W : Type} (as : List U) (bs : List W) (f : U → W → Nat) :
    mass as (fun a => mass bs (f a)) = mass bs (fun b => mass as (fun a => f a b)) := by
  induction as with
  | nil => simpa only [mass,List.map_nil,List.sum_nil] using (mass_zero bs).symm
  | cons a as ih =>
    simp only [mass,List.map_cons,List.sum_cons] at *
    rw [ih]
    exact (mass_plus bs (f a) (fun b => mass as (fun a => f a b))).symm

private theorem side_count (E : Enumeration V) {a b : V} :
    mass E.vertices (fun z => mark (M.face a b z)) = 2 * mark (M.adj a b) := by
  classical
  by_cases h : M.adj a b
  · obtain ⟨u,f⟩ := h
    obtain ⟨v,vu,g,allSides⟩ := M.twoSides f
    have eqs : ∀ z, M.face a b z ↔ z = u ∨ z = v := by
      intro z
      exact ⟨allSides z, fun e => by rcases e with rfl | rfl <;> assumption⟩
    rw [mass_congr _ (fun z => mark_congr (eqs z)), mass_pair E (Ne.symm vu),
      mark_yes (show M.adj a b from ⟨u,f⟩)]
  · have noFaces : ∀ z, ¬ M.face a b z := fun z hz => h ⟨z,hz⟩
    simp only [mark_no h,Nat.mul_zero]
    exact (mass_congr _ (fun z => mark_no (noFaces z))).trans (mass_zero _)

variable (E : Enumeration V)

noncomputable def degree (a : V) := mass E.vertices (fun z => mark (M.adj a z))
noncomputable def baseDegree (a : V) :=
  mass E.vertices (fun z => mark (¬ P.fresh z ∧ M.adj a z))
noncomputable def starNeighbors (a : V) :=
  mass E.vertices (fun z => mark (P.fresh z ∧ M.adj a z))
noncomputable def omittedFlags (a : V) :=
  mass E.vertices (fun b => mass E.vertices (fun c =>
    mark (¬ P.fresh b ∧ ¬ P.fresh c ∧ M.face a b c)))

theorem split_degree (a : V) :
    degree (M := M) E a = baseDegree P E a + starNeighbors P E a := by
  unfold degree baseDegree starNeighbors
  rw [← mass_plus]
  apply mass_congr
  intro z
  by_cases hz : P.fresh z <;> by_cases h : M.adj a z <;> simp [mark,hz,h]

theorem count_omitted_flags (a : P.Old) :
    2 * baseDegree P E a.val = 2 * starNeighbors P E a.val + omittedFlags P E a.val := by
  let F := fun b c => mark (¬ P.fresh b ∧ M.face a.val b c)
  let used := fun b c => mark (¬ P.fresh b ∧ P.fresh c ∧ M.face a.val b c)
  let empty := fun b c => mark (¬ P.fresh b ∧ ¬ P.fresh c ∧ M.face a.val b c)
  let xs := E.vertices
  have row (b : V) : mass xs (F b) = 2 * mark (¬ P.fresh b ∧ M.adj a.val b) := by
    by_cases h : P.fresh b
    · simpa [F,mark,h] using (mass_zero xs)
    · simpa only [F,h,not_false_eq_true,true_and,xs] using (side_count (M := M) E (a := a.val) (b := b))
  have col (c : V) :
      mass xs (fun b => used b c) = 2 * mark (P.fresh c ∧ M.adj a.val c) := by
    by_cases h : P.fresh c
    · have tr : ∀ b, used b c = mark (M.face a.val c b) := by
        intro b
        apply mark_congr
        constructor
        · rintro ⟨_,_,g⟩
          exact (sq M g).1
        · intro g
          exact ⟨old_neighbor P h ⟨_,M.rot g⟩, h,(sq M g).1⟩
      rw [mass_congr _ tr]
      simpa [h] using (side_count (M := M) E (a := a.val) (b := c))
    · simpa [used,mark,h] using (mass_zero xs)
  have split (b c : V) : F b c = used b c + empty b c := by
    by_cases h : P.fresh c <;> by_cases hb : P.fresh b <;> by_cases hf : M.face a.val b c <;> simp [F,used,empty,mark,h,hb,hf]
  change 2 * mass xs _ = 2 * mass xs _ + mass xs (fun b => mass xs (empty b))
  rw [← mass_double, ← mass_congr xs row, ← mass_double, ← mass_congr xs col,
    ← swap_mass xs xs used, ← mass_plus]
  exact mass_congr xs (fun b => (mass_congr xs (split b)).trans (mass_plus xs _ _))

/-- The row supplied to the global rigidity lemma is derived from the actual
degrees and facial incidences of the input map. -/
noncomputable def incidenceRow (a : P.Old) (target bit : Nat) (small : bit ≤ 1)
    (givenDegree : degree (M := M) E a.val + bit = 2 * target) : Row where
  base := baseDegree P E a.val
  target := target
  missed := omittedFlags P E a.val / 2
  bit := bit
  small := small
  equation := by
    have := count_omitted_flags P E a
    have := split_degree P E a.val
    omega


private theorem mass_le {U : Type} (xs : List U) {f g : U → Nat} (h : ∀ x, f x ≤ g x) :
    mass xs f ≤ mass xs g := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons a as ih => exact Nat.add_le_add (h a) ih

private theorem singleton {u : V} : mass E.vertices (fun v => mark (v = u)) = 1 :=
  (mass_single_aux _ E.unique u).trans (mark_yes (E.complete u))

private theorem spike (s : V × V) :
    mass E.vertices (fun b => mass E.vertices (fun c => mark ((b,c) = s))) = 1 := by
  rcases s with ⟨u,v⟩
  have row (b : V) : mass E.vertices (fun c => mark ((b,c) = (u,v))) = mark (b = u) := by
    by_cases h : b = u
    · subst b
      simpa [Prod.mk.injEq,mark_yes (q := True) trivial] using (singleton E (u := v))
    · simpa [Prod.mk.injEq,mark,h] using (mass_zero E.vertices)
  exact (mass_congr _ row).trans (singleton E)

private theorem mass_four {U : Type} (xs : List U) (f g h k : U → Nat) :
    mass xs (fun x => f x + g x + h x + k x) = mass xs f + mass xs g + mass xs h + mass xs k := by
  rw [mass_plus, mass_plus, mass_plus]

private theorem four_flags {a : P.Old} (b c d e : P.Old)
    (f : M.face a.val b.val c.val) (g : M.face a.val d.val e.val)
    (diff : ¬ ((b = d ∧ c = e) ∨ (b = e ∧ c = d))) :
    4 ≤ omittedFlags P E a.val := by
  let δ := fun (s : V × V) (i j : V) => mark ((i,j) = s)
  let u := (b.val,c.val)
  let v := (c.val,b.val)
  let w := (d.val,e.val)
  let x := (e.val,d.val)
  let actual := fun i j => mark (¬ P.fresh i ∧ ¬ P.fresh j ∧ M.face a.val i j)
  have bound : ∀ i j, δ u i j + δ v i j + δ w i j + δ x i j ≤ actual i j := by
    intro i j
    have hbc := M.distinct (M.rot f)
    have hde := M.distinct (M.rot g)
    have hb := b.property
    have hc := c.property
    have hd := d.property
    have he := e.property
    have p := (sq M f).1
    have q := (sq M g).1
    simp only [Subtype.ext_iff] at diff
    simp only [δ,u,v,w,x,actual,mark,Prod.mk.injEq]
    grind
  let xs := E.vertices
  have row (i : V) := mass_le xs (bound i)
  have both := mass_le xs row
  simp only [mass_four] at both
  have D (y : V × V) : mass xs (fun i => mass xs (δ y i)) = 1 := spike E y
  rw [D,D,D,D] at both
  exact both

theorem unique_unoccupied {a b c d e : P.Old} (bound : omittedFlags P E a.val ≤ 2)
    (f : M.face a.val b.val c.val) (g : M.face a.val d.val e.val) :
    (b = d ∧ c = e) ∨ (b = e ∧ c = d) := by
  apply Classical.byContradiction
  intro ne
  have := four_flags P E b c d e f g ne
  omega

private theorem unoccupied_exists {a : P.Old} (bound : 0 < omittedFlags P E a.val) :
    ∃ b c : P.Old, M.face a.val b.val c.val := by
  apply Classical.byContradiction
  intro h
  have noFace (b c : V) : ¬ (¬ P.fresh b ∧ ¬ P.fresh c ∧ M.face a.val b c) := by
    rintro ⟨hb,hc,f⟩
    exact h ⟨⟨b,hb⟩,⟨c,hc⟩,f⟩
  simp only [omittedFlags,mark_no (noFace _ _),mass_zero] at bound
  omega

private theorem flags_positive {a b c : P.Old} (f : M.face a.val b.val c.val) :
    0 < omittedFlags P E a.val := by
  have bound (i j : V) : mark ((i,j) = (b.val,c.val)) ≤
      mark (¬ P.fresh i ∧ ¬ P.fresh j ∧ M.face a.val i j) := by
    by_cases h : (i,j) = (b.val,c.val)
    · have hi := congrArg Prod.fst h
      have hj := congrArg Prod.snd h
      simp only at hi hj
      subst i
      subst j
      rw [mark_yes rfl,mark_yes ⟨b.property,c.property,f⟩]
      decide
    · rw [mark_no h]
      exact Nat.zero_le _
  have := mass_le E.vertices (fun i => mass_le E.vertices (bound i))
  rw [spike E (b.val,c.val)] at this
  exact this

theorem no_flags {a : P.Old} (none : ¬ ∃ b c : P.Old, M.face a.val b.val c.val) :
    omittedFlags P E a.val = 0 := by
  have h : ¬ 0 < omittedFlags P E a.val := fun pos => none (unoccupied_exists P E pos)
  omega

theorem two_flags {a b c : P.Old} (f : M.face a.val b.val c.val)
    (unique : ∀ d e : P.Old, M.face a.val d.val e.val →
      (b = d ∧ c = e) ∨ (b = e ∧ c = d)) :
    omittedFlags P E a.val = 2 := by
  let δ := fun (s : V × V) (i j : V) => mark ((i,j) = s)
  have eq (i j : V) : mark (¬ P.fresh i ∧ ¬ P.fresh j ∧ M.face a.val i j) =
      δ (b.val,c.val) i j + δ (c.val,b.val) i j := by
    have u (hi : ¬ P.fresh i) (hj : ¬ P.fresh j) (g : M.face a.val i j) :=
      unique ⟨i,hi⟩ ⟨j,hj⟩ g
    simp only [Subtype.ext_iff] at u
    have fb := b.property
    have fc := c.property
    have bc := M.distinct (M.rot f)
    have f' := (sq M f).1
    simp only [δ,mark,Prod.mk.injEq]
    grind
  unfold omittedFlags
  rw [mass_congr _ (fun i => (mass_congr _ (eq i)).trans (mass_plus _ _ _)), mass_plus]
  have D (s : V × V) : mass E.vertices (fun i => mass E.vertices (δ s i)) = 1 := spike E s
  rw [D,D]

private theorem fresh_total (x : V) (hx : P.fresh x) :
    mass E.vertices (fun v => mark (M.adj v x)) = 3 := by
  obtain ⟨a,b,c,hab,hbc,hac,N⟩ := P.cubic x hx
  have eq (v : V) : mark (M.adj v x) = mark (v = a) + mark (v = b) + mark (v = c) := by
    have symm : M.adj v x ↔ M.adj x v :=
      ⟨fun ⟨t,h⟩ => ⟨t,M.flip h⟩,fun ⟨t,h⟩ => ⟨t,M.flip h⟩⟩
    have := (symm.trans (N v))
    simp only [mark]
    grind
  rw [mass_congr _ eq,mass_plus,mass_plus,singleton,singleton,singleton]

noncomputable def Peeling.newCount := mass E.vertices (fun x => mark (P.fresh x))

theorem total_new_neighbors :
    mass E.vertices (starNeighbors P E) = 3 * P.newCount E := by
  unfold starNeighbors Peeling.newCount
  rw [swap_mass]
  have col (x : V) : mass E.vertices (fun v => mark (P.fresh x ∧ M.adj v x)) = 3 * mark (P.fresh x) := by
    by_cases hx : P.fresh x
    · simpa only [hx,true_and,mark_yes (q := True) trivial,Nat.mul_one] using fresh_total P E x hx
    · simpa [hx,mark] using mass_zero E.vertices
  rw [mass_congr _ col]
  induction E.vertices with
  | nil => rfl
  | cons a as ih => simp only [mass,List.map_cons,List.sum_cons] at *; omega

/-- Extend the row array by zero on the deleted vertices so every sum uses
the same vertex enumeration. -/
private noncomputable def rowAt (target bit : V → Nat)
    (small : ∀ v, bit v ≤ 1)
    (given : ∀ v, ¬ P.fresh v → degree (M := M) E v + bit v = 2 * target v) (v : V) : Row := by
  classical
  exact if h : P.fresh v then ⟨0,0,0,0,by decide,by decide⟩
    else incidenceRow P E ⟨v,h⟩ (target v) (bit v) (small v) (given v h)

theorem zero_stars {x : V} (h : P.fresh x) : starNeighbors P E x = 0 := by
  unfold starNeighbors
  have no (v : V) : ¬ (P.fresh v ∧ M.adj x v) := fun ⟨hv,ha⟩ => old_neighbor P h ha hv
  exact (mass_congr _ (fun v => mark_no (no v))).trans (mass_zero _)

/-- One inverse layer, including identification of its omitted faces. The
scalar budget is Σ p = 3k + Σ bit for k new vertices. It follows from
Σ p = 6N−12, k = 2N−4−t, and exactly 3t selected vertices. -/
theorem inverse_layer (target bit : V → Nat) (small : ∀ v, bit v ≤ 1)
    (zero : ∀ v, P.fresh v → target v = 0 ∧ bit v = 0)
    (given : ∀ v, ¬ P.fresh v → degree (M := M) E v + bit v = 2 * target v)
    (budget : mass E.vertices target = 3 * P.newCount E + mass E.vertices bit)
    (a : P.Old) :
    baseDegree P E a.val = target a.val ∧
    omittedFlags P E a.val = 2 * bit a.val ∧
    (bit a.val = 1 ↔ ∃ b c : P.Old, M.face a.val b.val c.val) ∧
    (∀ b c d e : P.Old, M.face a.val b.val c.val → M.face a.val d.val e.val →
       (b = d ∧ c = e) ∨ (b = e ∧ c = d)) := by
  classical
  let row := rowAt P E target bit small given
  have add (x : V) :
      (row x).base + starNeighbors P E x + bit x = target x + target x := by
    by_cases h : P.fresh x
    · obtain ⟨ht,hb⟩ := zero _ h
      simp [row,rowAt,h,ht,hb,zero_stars P E h]
    · simpa [row,rowAt,h,incidenceRow,← split_degree P E x,Nat.two_mul] using given x h
  have totals := mass_congr E.vertices add
  simp only [mass_plus,total_new_neighbors] at totals
  have eqt (v : V) : (row v).target = target v := by
    by_cases h : P.fresh v
    · simp [row,rowAt,h,(zero _ h).1]
    · simp [row,rowAt,h,incidenceRow]
  let rows := E.vertices.map row
  have eq : (rows.map Row.base).sum = (rows.map Row.target).sum := by
    change (List.map Row.base (List.map row E.vertices)).sum = _
    simp only [rows,List.map_map,Function.comp_def]
    change mass E.vertices _ = mass E.vertices _
    rw [mass_congr _ eqt]
    omega
  have member : row a.val ∈ rows := List.mem_map.mpr ⟨a.val,E.complete _,rfl⟩
  have ha := omitted_incidence_rigidity rows eq _ member
  simp only [row,rowAt,a.property,↓reduceDIte,incidenceRow] at ha
  have counts := count_omitted_flags P E a
  have twice : omittedFlags P E a.val = 2 * bit a.val := by omega
  refine ⟨ha.1,twice,⟨fun h => unoccupied_exists P E (a := a) (by omega),?_⟩,?_⟩
  · rintro ⟨b,c,f⟩
    have := flags_positive P E (a := a) (b := b) (c := c) f
    have := small a.val
    omega
  · intro b c d e f g
    have := small a.val
    exact unique_unoccupied P E (a := a) (by omega) f g


private theorem filter_count {U : Type} (xs : List U) (p : U → Prop) [DecidablePred p] :
    (xs.filter fun x => decide (p x)).length = mass xs (fun x => mark (p x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : p x <;> simpa [h,mass,mark,Nat.add_comm] using ih

private theorem length_three {U : Type} (xs : List U) (len : xs.length = 3) :
    ∃ a b c, xs = [a,b,c] := by
  cases xs with
  | nil => simp at len
  | cons a xs =>
    cases xs with
    | nil => simp at len
    | cons b xs =>
      cases xs with
      | nil => simp at len
      | cons c xs =>
        obtain rfl : xs = [] := List.length_eq_zero_iff.mp (by simpa using len)
        exact ⟨a,b,c,rfl⟩

/-- Numerical degree three is equivalent to the combinatorial three-neighbor
description used in the deletion construction. -/
theorem cubic_iff_degree (x : V) : M.Cubic x ↔ degree (M := M) E x = 3 := by
  classical
  let nbr := E.vertices.filter (fun z => decide (M.adj x z))
  have len : nbr.length = degree (M := M) E x := filter_count _ _
  have nodup : nbr.Nodup := List.filter_sublist.nodup E.unique
  have mem (v : V) : v ∈ nbr ↔ M.adj x v := by simp [nbr,E.complete]
  constructor
  · rintro ⟨a,b,c,hab,hbc,hac,N⟩
    have eq (v : V) : mark (M.adj x v) = mark (v = a) + mark (v = b) + mark (v = c) := by
      have := N v
      simp only [mark]
      grind
    unfold degree
    rw [mass_congr _ eq,mass_plus,mass_plus,singleton,singleton,singleton]
  · intro h
    obtain ⟨a,b,c,f⟩ := length_three nbr (len.trans h)
    rw [f] at nodup
    simp only [List.nodup_cons,List.mem_cons,List.mem_nil_iff,or_false] at nodup
    refine ⟨a,b,c,by grind,by grind,by grind,fun z => ?_⟩
    simpa [f] using (mem z).symm

/-- Canonical choice of the deleted vertices in the reverse reduction. -/
noncomputable def fromDegrees
    (fourOld : ∀ a b c : V, ∃ z, degree (M := M) E z ≠ 3 ∧ z ≠ a ∧ z ≠ b ∧ z ≠ c) :
    Peeling M where
  fresh x := degree (M := M) E x = 3
  cubic x := (cubic_iff_degree E x).mpr
  fourOld := fourOld

private noncomputable def keepOld (x : V) : Option P.Old := by
  classical
  exact if h : P.fresh x then none else some ⟨x,h⟩

private theorem old_mem (xs : List V) (z : P.Old) :
    z ∈ xs.filterMap (keepOld P) ↔ z.val ∈ xs := by
  constructor
  · intro h
    obtain ⟨x,hx,k⟩ := List.mem_filterMap.mp h
    by_cases f : P.fresh x
    · simp [keepOld,f] at k
    · have eq : x = z.val := congrArg Subtype.val (Option.some.inj (by simpa only [keepOld,f,↓reduceDIte] using k))
      exact eq ▸ hx
  · intro h
    exact List.mem_filterMap.mpr ⟨z.val,h,by simp [keepOld,z.property]⟩

noncomputable def Peeling.enumeration : Enumeration P.Old where
  vertices := E.vertices.filterMap (keepOld P)
  unique := by
    have aux : ∀ (l : List V), l.Nodup → (l.filterMap (keepOld P)).Nodup := by
      intro l
      induction l with
      | nil => simp
      | cons a l ih =>
        intro h
        obtain ⟨hm,hn⟩ := List.nodup_cons.mp h
        by_cases fresh : P.fresh a
        · simpa [List.filterMap_cons,keepOld,fresh] using ih hn
        · simp only [List.filterMap_cons,keepOld,fresh,↓reduceDIte]
          exact List.nodup_cons.mpr ⟨fun mem => hm ((old_mem P l ⟨a,fresh⟩).mp mem),ih hn⟩
    exact aux E.vertices E.unique
  complete z := (old_mem P E.vertices z).mpr (E.complete _)

theorem degree_of_peeled_map (v : P.Old) :
    degree (M := P.map) (P.enumeration E) v = baseDegree P E v.val := by
  let g := fun z : P.Old => mark (P.map.adj v z)
  have eq (z : P.Old) : g z = mark (M.adj v.val z.val) := mark_congr (peeled_edges P)
  have scan : ∀ xs : List V, mass (xs.filterMap (keepOld P)) g =
      mass xs (fun z => mark (¬ P.fresh z ∧ M.adj v.val z)) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      by_cases h : P.fresh a
      · simpa [List.filterMap_cons,keepOld,h,mass,mark] using ih
      · simp only [List.filterMap_cons,keepOld,h,↓reduceDIte,List.map_cons,
          mass,List.sum_cons,not_false_eq_true,true_and]
        simp only [mass] at ih
        rw [eq ⟨a,h⟩,ih]
  exact scan E.vertices

#print axioms cubic_independent
#print axioms Peeling.map
#print axioms inverse_layer
#print axioms cubic_iff_degree
#print axioms degree_of_peeled_map

end Recognition.Rigidity
