import Triangulation.Rigidity

namespace Recognition.Stacking
open Recognition.Rigidity

variable {V : Type} (M : Map V)

/-- A triangle is named by its unordered set of three vertices. -/
def corners (a b c : V) : V → Prop := fun x => x = a ∨ x = b ∨ x = c

abbrev Choice (V : Type) := (V → Prop) → Prop

variable (fill : Choice V)

def Star := {k : V → Prop // (∃ a b c, M.face a b c ∧ k = corners a b c) ∧ fill k}
abbrev Vertex := Sum V (Star M fill)

private theorem rot_key (a b c : V) : corners a b c = corners b c a := by
  funext x
  apply propext
  simp only [corners]
  grind

private theorem flip_key (a b c : V) : corners a b c = corners b a c := by
  funext x
  apply propext
  simp only [corners]
  grind

private theorem three_distinct {a b c : V} (f : M.face a b c) : a ≠ b ∧ b ≠ c ∧ a ≠ c :=
  ⟨M.distinct f, M.distinct (M.rot f),Ne.symm (M.distinct (M.rot (M.rot f)))⟩

private theorem named {a b : V} {s : Star M fill} (ab : a ≠ b) (ha : s.val a) (hb : s.val b) :
    ∃ c, M.face a b c ∧ s.val = corners a b c := by
  obtain ⟨u,v,w,f,h⟩ := s.property.1
  rw [h] at ha hb ⊢
  have r := M.rot f
  have rr := M.rot r
  rcases ha with ha | ha | ha <;> subst a <;> rcases hb with hb | hb | hb <;> subst b <;>
    first | contradiction
          | exact ⟨_,f,rfl⟩ | exact ⟨_,r,rot_key ..⟩
          | exact ⟨_,rr,(rot_key ..).trans (rot_key ..)⟩
          | exact ⟨_,M.flip f,flip_key ..⟩
          | exact ⟨_,M.flip r,(rot_key ..).trans (flip_key ..)⟩
          | exact ⟨_,M.flip rr,((rot_key ..).trans (rot_key ..)).trans (flip_key ..)⟩

def face : Vertex M fill → Vertex M fill → Vertex M fill → Prop
  | .inl a, .inl b, .inl c => M.face a b c ∧ ¬ fill (corners a b c)
  | .inl a, .inl b, .inr s => a ≠ b ∧ s.val a ∧ s.val b
  | .inl b, .inr s, .inl a => a ≠ b ∧ s.val a ∧ s.val b
  | .inr s, .inl a, .inl b => a ≠ b ∧ s.val a ∧ s.val b
  | _, _, _ => False

private theorem rot {a b c : Vertex M fill} : face M fill a b c → face M fill b c a := by
  cases a <;> cases b <;> cases c <;> simp only [face] <;> try exact id
  intro ⟨h,k⟩
  exact ⟨M.rot h,rot_key .. ▸ k⟩

private theorem flip {a b c : Vertex M fill} : face M fill a b c → face M fill b a c := by
  cases a <;> cases b <;> cases c <;> simp only [face] <;> try grind
  intro ⟨h,k⟩
  exact ⟨M.flip h,flip_key .. ▸ k⟩

private theorem distinct {a b c : Vertex M fill} : face M fill a b c → a ≠ b := by
  cases a <;> cases b <;> cases c <;> simp only [face,ne_eq,Sum.inl.injEq,reduceCtorEq,not_false_eq_true] <;> grind [Map.distinct]

noncomputable def opposite {a b c : V} (f : M.face a b c) : Vertex M fill := by
  classical
  exact if occupied : fill (corners a b c)
    then .inr ⟨corners a b c, ⟨a,b,c,f,rfl⟩,occupied⟩ else .inl c

private theorem sector {a b c : V} (f : M.face a b c) :
    face M fill (.inl a) (.inl b) (opposite M fill f) := by
  classical
  unfold opposite
  split
  · exact ⟨M.distinct f,Or.inl rfl,Or.inr (Or.inl rfl)⟩
  · exact ⟨f,by assumption⟩

private theorem sectors_exact (a b : V) (z : Vertex M fill)
    (h : face M fill (.inl a) (.inl b) z) :
    ∃ c, ∃ f : M.face a b c, z = opposite M fill f := by
  classical
  cases z with
  | inl c => exact ⟨c,h.1,by simp [opposite,h.2]⟩
  | inr s =>
    obtain ⟨c,f,k⟩ := named (M := M) (fill := fill) h.1 h.2.1 h.2.2
    have hc : fill (corners a b c) := k ▸ s.property.2
    exact ⟨c,f,by simp only [opposite,hc,↓reduceDIte]; exact congrArg Sum.inr (Subtype.ext k)⟩

private theorem opposite_inj {a b c d : V} (f : M.face a b c) (g : M.face a b d)
    (eq : opposite M fill f = opposite M fill g) : c = d := by
  classical
  unfold opposite at eq
  split at eq <;> split at eq <;> try contradiction <;> try solve | injection eq
  case isFalse.isFalse => exact Sum.inl.inj eq
  have h := congrArg Subtype.val (Sum.inr.inj eq)
  change corners a b c = corners a b d at h
  have k : corners a b d c := h ▸ (show corners a b c c from Or.inr (Or.inr rfl))
  have := three_distinct M f
  rcases k with e | e | e <;> grind

private def Two {W : Type} (F : W → W → W → Prop) (a b c : W) : Prop :=
  ∃ d, d ≠ c ∧ F a b d ∧ ∀ e, F a b e → e = c ∨ e = d

private theorem old_sides {a b : V} {z : Vertex M fill} (h : face M fill (.inl a) (.inl b) z) :
    Two (face M fill) (.inl a) (.inl b) z := by
  obtain ⟨c,f,rfl⟩ := sectors_exact M fill _ _ _ h
  obtain ⟨d,ne,g,sides⟩ := M.twoSides f
  refine ⟨opposite M fill g,fun e => ne (opposite_inj M fill g f e),sector M fill g,?_⟩
  intro e he
  obtain ⟨t,k,rfl⟩ := sectors_exact M fill _ _ _ he
  rcases sides t k with rfl | rfl <;> simp

private theorem spoke_sides {a : V} {s : Star M fill} {z : Vertex M fill}
    (h : face M fill (.inl a) (.inr s) z) : Two (face M fill) (.inl a) (.inr s) z := by
  cases z with
  | inr _ => exact False.elim h
  | inl b =>
    obtain ⟨c,f,k⟩ := named (M := M) (fill := fill) h.1 h.2.1 h.2.2
    have ⟨hba,hac,hbc⟩ := three_distinct M f
    refine ⟨.inl c,fun e => hbc (Sum.inl.inj e).symm,
      ⟨Ne.symm hac,k ▸ Or.inr (Or.inr rfl),h.2.2⟩,?_⟩
    intro e he
    cases e with
    | inr _ => exact False.elim he
    | inl x =>
      have hx := he.2.1
      rw [k] at hx
      have xa := he.1
      rcases hx with rfl | rfl | rfl <;> grind

private theorem sides {a b c : Vertex M fill} (f : face M fill a b c) :
    Two (face M fill) a b c := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact old_sides M fill f
    | inr s => exact spoke_sides M fill f
  | inr s =>
    cases b with
    | inr _ => cases c <;> exact False.elim f
    | inl b =>
      obtain ⟨d,ne,g,h⟩ := spoke_sides M fill (flip M fill f)
      exact ⟨d,ne,flip M fill g,fun e k => h e (flip M fill k)⟩


private noncomputable def anchor {a b c : V} (f : M.face a b c) : Triangle (Vertex M fill) :=
  ⟨.inl a,.inl b,opposite M fill f⟩

private theorem join {W : Type} {F : W → W → W → Prop} {s t u}
    (h : Walk F s t) (k : Walk F t u) : Walk F s u := by
  induction k with
  | nil => exact h
  | rot _ ih => exact .rot ih
  | flip _ ih => exact .flip ih
  | cross _ f ih => exact .cross ih f

private theorem pull {s t : Triangle (Vertex M fill)} (h : Walk (face M fill) s t)
    (f : face M fill s.a s.b s.c) : face M fill t.a t.b t.c ∧ Walk (face M fill) t s := by
  induction h with
  | nil => exact ⟨f,.nil⟩
  | rot _ ih => exact ⟨rot M fill ih.1,join (.rot (.rot .nil)) ih.2⟩
  | flip _ ih => exact ⟨flip M fill ih.1,join (.flip .nil) ih.2⟩
  | cross _ g ih => exact ⟨g,join (.cross .nil ih.1) ih.2⟩

private theorem turn_sector {a b c : V} (f : M.face a b c) :
    Walk (face M fill) (anchor M fill f) (anchor M fill (M.rot f)) := by
  classical
  have eq := rot_key a b c
  by_cases h : fill (corners a b c)
  · have h' : fill (corners b c a) := eq ▸ h
    let s : Star M fill := ⟨corners a b c,⟨a,b,c,f,rfl⟩,h⟩
    have same : (⟨corners b c a,⟨b,c,a,M.rot f,rfl⟩,h'⟩ : Star M fill) = s := Subtype.ext eq.symm
    simp only [anchor,opposite,h,h',↓reduceDIte,same]
    change Walk (face M fill) ⟨.inl a,.inl b,.inr s⟩ ⟨.inl b,.inl c,.inr s⟩
    have crossFace : face M fill (.inl b) (.inr s) (.inl c) :=
      ⟨Ne.symm (M.distinct (M.rot f)),Or.inr (Or.inr rfl),Or.inr (Or.inl rfl)⟩
    exact .flip (.rot (.rot (.cross (.rot .nil) crossFace)))
  · have h' : ¬ fill (corners b c a) := eq ▸ h
    simp only [anchor,opposite,h,h',↓reduceDIte]
    exact .rot .nil

private theorem flip_sector {a b c : V} (f : M.face a b c) :
    Walk (face M fill) (anchor M fill f) (anchor M fill (M.flip f)) := by
  classical
  have eq := flip_key a b c
  by_cases h : fill (corners a b c)
  · have h' : fill (corners b a c) := eq ▸ h
    have same : (⟨corners b a c,⟨b,a,c,M.flip f,rfl⟩,h'⟩ : Star M fill) =
      ⟨corners a b c,⟨a,b,c,f,rfl⟩,h⟩ := Subtype.ext eq.symm
    simp only [anchor,opposite,h,h',↓reduceDIte,same]
    exact .flip .nil
  · have h' : ¬ fill (corners b a c) := eq ▸ h
    simp only [anchor,opposite,h,h',↓reduceDIte]
    exact .flip .nil

private theorem sector_walk {a b c d e f : V} (h : M.face a b c) (g : M.face d e f) :
    Walk (face M fill) (anchor M fill h) (anchor M fill g) := by
  have lift : ∀ {t : Triangle V}, Walk M.face ⟨a,b,c⟩ t →
      ∃ k : M.face t.a t.b t.c, Walk (face M fill) (anchor M fill h) (anchor M fill k) := by
    intro t w
    induction w with
    | nil => exact ⟨h,.nil⟩
    | rot _ ih =>
      obtain ⟨k,p⟩ := ih
      exact ⟨M.rot k,join p (turn_sector M fill k)⟩
    | flip _ ih =>
      obtain ⟨k,p⟩ := ih
      exact ⟨M.flip k,join p (flip_sector M fill k)⟩
    | cross _ k ih =>
      obtain ⟨_,p⟩ := ih
      exact ⟨k,.cross p (sector M fill k)⟩
  exact (lift (M.connected h g)).elim (fun _ w => w)

private theorem sector_parent {a b c : Vertex M fill} (g : face M fill a b c) :
    ∃ i j k, ∃ h : M.face i j k, Walk (face M fill) (anchor M fill h) ⟨a,b,c⟩ := by
  have old (i j : V) (w : Vertex M fill) (h : face M fill (.inl i) (.inl j) w) :
      ∃ k, ∃ f : M.face i j k, Walk (face M fill) (anchor M fill f) ⟨.inl i,.inl j,w⟩ := by
    obtain ⟨k,f,rfl⟩ := sectors_exact M fill i j w h
    exact ⟨k,f,.nil⟩
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      obtain ⟨k,f,w⟩ := old i j _ g
      exact ⟨i,j,k,f,w⟩
    | inr s =>
      cases c with
      | inr _ => exact False.elim g
      | inl j =>
        obtain ⟨k,f,w⟩ := old j i _ (rot M fill (rot M fill g))
        exact ⟨j,i,k,f,.rot w⟩
  | inr s =>
    cases b with
    | inr _ => cases c <;> exact False.elim g
    | inl i =>
      cases c with
      | inr _ => exact False.elim g
      | inl j =>
        obtain ⟨k,f,w⟩ := old i j _ (rot M fill g)
        exact ⟨i,j,k,f,.rot (.rot w)⟩

private theorem connected {a b c u v w : Vertex M fill} (f : face M fill a b c) (g : face M fill u v w) :
    Walk (face M fill) ⟨a,b,c⟩ ⟨u,v,w⟩ := by
  obtain ⟨_,_,_,p,h⟩ := sector_parent M fill f
  obtain ⟨_,_,_,q,k⟩ := sector_parent M fill g
  exact join (pull M fill h (sector M fill p)).2 (join (sector_walk M fill p q) k)

private theorem incident (z : Vertex M fill) : ∃ a b, face M fill z a b := by
  cases z with
  | inl x =>
    obtain ⟨a,b,f⟩ := M.incident x
    exact ⟨_,_,sector M fill f⟩
  | inr s =>
    obtain ⟨a,b,c,f,k⟩ := s.property.1
    exact ⟨.inl a,.inl b,M.distinct f,k ▸ Or.inl rfl,k ▸ Or.inr (Or.inl rfl)⟩

/-- Subdivide each chosen face simultaneously, introducing exactly one vertex
indexed by its unordered boundary. -/
def stack : Map (Vertex M fill) where
  face := face M fill
  rot := rot M fill
  flip := flip M fill
  distinct := distinct M fill
  twoSides := sides M fill
  incident := incident M fill
  connected := connected M fill

theorem old_edges (a b : V) :
    (stack M fill).adj (.inl a) (.inl b) ↔ M.adj a b := by
  constructor
  · rintro ⟨z,h⟩
    obtain ⟨c,f,_⟩ := sectors_exact M fill _ _ _ h
    exact ⟨c,f⟩
  · rintro ⟨c,f⟩
    exact ⟨_,sector M fill f⟩

theorem star_link (s : Star M fill) {a b c : V} (f : M.face a b c)
    (h : s.val = corners a b c) : (stack M fill).Three (.inr s) (.inl a) (.inl b) (.inl c) := by
  have ⟨ab,bc,ac⟩ := three_distinct M f
  refine ⟨(fun e => ab (Sum.inl.inj e)),(fun e => bc (Sum.inl.inj e)),
    (fun e => ac (Sum.inl.inj e)),?_⟩
  intro v
  constructor
  · rintro ⟨w,hw⟩
    cases v with
    | inr _ => cases w <;> exact False.elim hw
    | inl x =>
      cases w with
      | inr _ => exact False.elim hw
      | inl y =>
        have hx := hw.2.1
        rw [h] at hx
        rcases hx with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨.inl b,ab,h ▸ Or.inl rfl,h ▸ Or.inr (Or.inl rfl)⟩
    · exact ⟨.inl c,bc,h ▸ Or.inr (Or.inl rfl),h ▸ Or.inr (Or.inr rfl)⟩
    · exact ⟨.inl a,Ne.symm ac,h ▸ Or.inr (Or.inr rfl),h ▸ Or.inl rfl⟩


theorem star_neighbors (s : Star M fill) (v : V) : (stack M fill).adj (.inr s) (.inl v) ↔ s.val v := by
  obtain ⟨a,b,c,f,h⟩ := s.property.1
  have N := (star_link M fill s f h).2.2.2 (.inl v)
  simpa [h,corners] using N

def newVertex : Vertex M fill → Prop
  | .inl _ => False
  | .inr _ => True

private noncomputable def ground : Vertex M fill → V
  | .inl v => v
  | .inr s => Classical.choose s.property.1

variable (four : ∀ a b c : V, ∃ z, z ≠ a ∧ z ≠ b ∧ z ≠ c)

def deletion : Peeling (stack M fill) where
  fresh := newVertex M fill
  cubic x h := by
    cases x with
    | inl _ => exact False.elim h
    | inr s =>
      obtain ⟨a,b,c,f,k⟩ := s.property.1
      exact ⟨_,_,_,star_link M fill s f k⟩
  fourOld a b c := by
    obtain ⟨v,ha,hb,hc⟩ := four (ground M fill a) (ground M fill b) (ground M fill c)
    have ne (t : Vertex M fill) (h : v ≠ ground M fill t) : Sum.inl v ≠ t :=
      fun e => h (congrArg (ground M fill) e)
    exact ⟨.inl v, id,ne a ha,ne b hb,ne c hc⟩

abbrev old (v : V) : (deletion M fill four).Old := ⟨.inl v,id⟩

private theorem old_surjective (w : (deletion M fill four).Old) : ∃ a, w = old M fill four a := by
  obtain ⟨x,h⟩ := w
  cases x with
  | inl a => exact ⟨a,rfl⟩
  | inr s => exact False.elim (h trivial)

/-- Deleting the introduced star vertices recovers exactly the initial faces. -/
theorem peel_stack_face (a b c : V) :
    (deletion M fill four).map.face (old M fill four a) (old M fill four b)
      (old M fill four c) ↔ M.face a b c := by
  constructor
  · rintro (f | ⟨x,hx,k⟩)
    · exact f.1
    · cases x with
      | inl _ => exact False.elim hx
      | inr s =>
        have N (v : V) := (star_neighbors M fill s v).symm.trans (k.2.2.2 (.inl v))
        simp only [Sum.inl.injEq] at N
        have ab : a ≠ b := fun e => k.1 (congrArg Sum.inl e)
        obtain ⟨w,g,h⟩ := named (M := M) (fill := fill) ab ((N a).mpr (by simp)) ((N b).mpr (by simp))
        have := (N w).mp (h ▸ Or.inr (Or.inr rfl))
        have := three_distinct M g
        obtain rfl : w = c := by grind
        exact g
  · intro f
    classical
    by_cases h : fill (corners a b c)
    · let s : Star M fill := ⟨corners a b c,⟨a,b,c,f,rfl⟩,h⟩
      exact Or.inr ⟨.inr s,trivial,star_link M fill s f rfl⟩
    · exact Or.inl ⟨f,h⟩

private def uniqueList {U : Type} [DecidableEq U] : List U → List U
  | [] => []
  | x :: xs => if x ∈ xs then uniqueList xs else x :: uniqueList xs

private theorem mem_unique {U : Type} [DecidableEq U] (xs : List U) (v : U) :
    v ∈ uniqueList xs ↔ v ∈ xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [uniqueList,List.mem_cons]
    split <;> simp_all [List.mem_cons] <;> grind

private theorem nodup_unique {U : Type} [DecidableEq U] (xs : List U) : (uniqueList xs).Nodup := by
  induction xs with
  | nil => simp [uniqueList]
  | cons x xs ih => simp only [uniqueList]; split <;> simp_all [List.nodup_cons,mem_unique]

private noncomputable def starAt (a b c : V) : List (Star M fill) := by
  classical
  exact if yes : M.face a b c ∧ fill (corners a b c) then
    [⟨corners a b c, ⟨a,b,c,yes.1,rfl⟩, yes.2⟩] else []

variable (E : Enumeration V)

noncomputable def starEnumeration : Enumeration (Star M fill) := by
  classical
  let xs := E.vertices
  let stars := xs.flatMap (fun a => xs.flatMap (fun b => xs.flatMap (fun c => starAt M fill a b c)))
  refine ⟨uniqueList stars,nodup_unique _,?_⟩
  intro s
  apply (mem_unique _ _).mpr
  obtain ⟨a,b,c,f,k⟩ := s.property.1
  have h : fill (corners a b c) := k ▸ s.property.2
  exact List.mem_flatMap.mpr ⟨a,E.complete _,List.mem_flatMap.mpr ⟨b,E.complete _,
    List.mem_flatMap.mpr ⟨c,E.complete _,by
      simp [starAt,f,h]
      exact List.mem_singleton.mpr (Subtype.ext k)⟩⟩⟩

noncomputable def enumeration : Enumeration (Vertex M fill) where
  vertices := E.vertices.map Sum.inl ++ (starEnumeration M fill E).vertices.map Sum.inr
  unique := by
    apply List.nodup_append.mpr
    refine ⟨List.pairwise_map.mpr (E.unique.imp (fun h e => h (Sum.inl.inj e))),
      List.pairwise_map.mpr ((starEnumeration M fill E).unique.imp (fun h e => h (Sum.inr.inj e))),?_⟩
    intro x hx y hy
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hx
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hy
    simp
  complete z := by
    cases z with
    | inl v => exact List.mem_append_left _ (List.mem_map.mpr ⟨v,E.complete _,rfl⟩)
    | inr s => exact List.mem_append_right _ (List.mem_map.mpr ⟨s,(starEnumeration M fill E).complete _,rfl⟩)

theorem new_degree (s : Star M fill) : degree (M := stack M fill) (enumeration M fill E) (.inr s) = 3 := by
  apply (cubic_iff_degree _ _).mp
  obtain ⟨a,b,c,f,k⟩ := s.property.1
  exact ⟨_,_,_,star_link M fill s f k⟩

private theorem base_eq (a : V) :
    baseDegree (deletion M fill four) (enumeration M fill E) (.inl a) = degree (M := M) E a := by
  unfold baseDegree degree mass
  simp only [enumeration,List.map_append,List.map_map,List.sum_append,Function.comp_def]
  have old_eq (v : V) :
      mark (¬ (deletion M fill four).fresh (.inl v) ∧ (stack M fill).adj (.inl a) (.inl v)) = mark (M.adj a v) := by
    change mark (¬ False ∧ _) = _
    rw [show (¬ False ∧ (stack M fill).adj (.inl a) (.inl v)) ↔ M.adj a v by simp [old_edges]]
  have new_zero (s : Star M fill) :
      mark (¬ (deletion M fill four).fresh (.inr s) ∧ (stack M fill).adj (.inl a) (.inr s)) = 0 := by
    simp [deletion,newVertex,mark]
  simp only [old_eq,new_zero]
  have z {U : Type} (xs : List U) : (xs.map (fun _ => (0:Nat))).sum = 0 := by
    induction xs with
    | nil => rfl
    | cons _ xs ih => simpa using ih
  rw [z,Nat.add_zero]


def vacant (a b c : V) : Prop := M.face a b c ∧ ¬ fill (corners a b c)

include four in
/-- If the unfilled faces are vertex-disjoint, and their corners are the
marked vertices, the old degrees in the constructed map are exactly doubled,
with a deficit of one at each marked vertex. -/
theorem forward_layer (marked : V → Bool)
    (hits : ∀ a, marked a = true ↔ ∃ b c, vacant M fill a b c)
    (disjoint : ∀ a b c d e, vacant M fill a b c → vacant M fill a d e →
      (b = d ∧ c = e) ∨ (b = e ∧ c = d)) (a : V) :
    degree (M := stack M fill) (enumeration M fill E) (.inl a) + (if marked a then 1 else 0) =
      2 * degree (M := M) E a := by
  let P := deletion M fill four
  let E' := enumeration M fill E
  let o := old M fill four
  have inc := count_omitted_flags P E' (o a)
  have deg := split_degree P E' (.inl a)
  have base : baseDegree P E' (.inl a) = degree (M := M) E a := base_eq M fill four E a
  change 2 * baseDegree P E' (.inl a) = 2 * starNeighbors P E' (.inl a) +
    omittedFlags P E' (.inl a) at inc
  change degree (M := stack M fill) E' (.inl a) + _ = _
  cases m : marked a with
  | false =>
    have empty : ¬ ∃ b c : P.Old, (stack M fill).face (o a).val b.val c.val := by
      rintro ⟨b,c,f⟩
      obtain ⟨i,rfl⟩ := old_surjective M fill four b
      obtain ⟨j,rfl⟩ := old_surjective M fill four c
      have := (hits a).mpr ⟨i,j,f⟩
      simp [m] at this
    have z : omittedFlags P E' (.inl a) = 0 := no_flags P E' (a := o a) empty
    simp only [Bool.false_eq_true,↓reduceIte,Nat.add_zero]
    omega
  | true =>
    obtain ⟨b,c,f⟩ := (hits a).mp m
    have uniq : ∀ d e : P.Old, (stack M fill).face (o a).val d.val e.val →
        (o b = d ∧ o c = e) ∨ (o b = e ∧ o c = d) := by
      intro d e g
      obtain ⟨i,rfl⟩ := old_surjective M fill four d
      obtain ⟨j,rfl⟩ := old_surjective M fill four e
      rcases disjoint a b c i j f g with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [o]
    have z : omittedFlags P E' (.inl a) = 2 := two_flags P E' (a := o a) (b := o b) (c := o c) f uniq
    simp only [↓reduceIte]
    omega


private theorem mass_const {U : Type} (xs : List U) (k : Nat) :
    mass xs (fun _ => k) = xs.length * k := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih => simpa [mass,Nat.succ_mul,Nat.add_comm] using congrArg (fun n => k + n) ih

private theorem sum_by_type (f : Vertex M fill → Nat) :
    mass (enumeration M fill E).vertices f =
      mass E.vertices (fun v => f (.inl v)) + mass (starEnumeration M fill E).vertices (fun s => f (.inr s)) := by
  simp [mass,enumeration,List.map_map,Function.comp_def]

private theorem stars_count :
    (deletion M fill four).newCount (enumeration M fill E) = (starEnumeration M fill E).vertices.length := by
  unfold Peeling.newCount
  rw [sum_by_type]
  change mass E.vertices (fun _ => mark False) +
    mass (starEnumeration M fill E).vertices (fun _ => mark True) = _
  simp [mark,mass_const]

include four in
/-- In the Euler-tight input case the forward construction appends precisely
the stated number of degree-three entries. The equality is expressed without
truncated subtraction. -/
theorem forward_length (marked : V → Bool)
    (hits : ∀ a, marked a = true ↔ ∃ b c, vacant M fill a b c)
    (disjoint : ∀ a b c d e, vacant M fill a b c → vacant M fill a d e →
      (b = d ∧ c = e) ∨ (b = e ∧ c = d))
    (t : Nat)
    (bits : mass E.vertices (fun v => if marked v then 1 else 0) = 3 * t)
    (euler : mass E.vertices (degree (M := M) E) + 12 = 6 * E.vertices.length) :
    (starEnumeration M fill E).vertices.length + t + 4 = 2 * E.vertices.length := by
  let P := deletion M fill four
  let all := enumeration M fill E
  let K := (starEnumeration M fill E).vertices.length
  let bit := fun v => if marked v then 1 else 0
  have step (a : V) : starNeighbors P all (.inl a) + bit a = degree (M := M) E a := by
    have d := forward_layer M fill four E marked hits disjoint a
    have b := base_eq M fill four E a
    have c := split_degree P all (.inl a)
    change degree (M := stack M fill) all (.inl a) + bit a = 2 * degree (M := M) E a at d
    change baseDegree P all (.inl a) = degree (M := M) E a at b
    omega
  have sums (xs : List V) : mass xs (fun a => starNeighbors P all (.inl a)) + mass xs bit =
      mass xs (degree (M := M) E) := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      have := step a
      simp only [mass,List.map_cons,List.sum_cons] at *
      omega
  have total := total_new_neighbors P all
  change mass (enumeration M fill E).vertices (starNeighbors P all) = _ at total
  rw [sum_by_type] at total
  have zs : ∀ s, starNeighbors P all (.inr s) = 0 := fun _ => zero_stars P all trivial
  have z : mass (starEnumeration M fill E).vertices (fun s => starNeighbors P all (.inr s)) = 0 := by
    simp only [zs,mass_const,Nat.mul_zero]
  have k : P.newCount all = K := stars_count M fill four E
  rw [z,Nat.add_zero,k] at total
  have sum := sums E.vertices
  change mass E.vertices bit = 3 * t at bits
  change K + _ + _ = _
  omega

#print axioms stack
#print axioms new_degree
#print axioms peel_stack_face
#print axioms forward_layer
#print axioms forward_length

end Recognition.Stacking
