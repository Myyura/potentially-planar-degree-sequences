import SparseBoundary.GraphEncoding

namespace SparseBoundary.Fan

open Graph

def between (a b c : Nat) : Bool :=
  decide (min a b < c ∧ c < max a b)

def noncross (a b c d : Nat) : Prop := between a b c = between a b d

theorem noncross_swap {a b c d : Nat}
    (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) :
    noncross a b c d ↔ noncross c d a b := by
  simp only [noncross,between,decide_eq_decide]
  by_cases h : a≤b <;> by_cases g : c≤d <;>
    simp only [Nat.min_def,Nat.max_def,h,g,ite_true,ite_false] <;> omega

/-- An ordering of the vertices in which all disjoint edges avoiding one
fixed apex can be drawn as non-crossing chords of a circle. -/
structure OuterOrder (G : Graph n) (apex : Fin n) where
  rank : Fin n → Nat
  inj : ∀ u v, rank u=rank v → u=v
  chords : ∀ u v x y, u≠apex → v≠apex → x≠apex → y≠apex →
    u≠x → u≠y → v≠x → v≠y →
    G.adj u v=true → G.adj x y=true →
    (decide (min (rank u) (rank v)<rank x ∧ rank x<max (rank u) (rank v))) =
    (decide (min (rank u) (rank v)<rank y ∧ rank y<max (rank u) (rank v)))

private def Uniform (G : Graph n) (S : Fin n → Prop) : Prop :=
  ∀ f : Fin n → Bool, (∀ u v, S u → S v → G.adj u v=true → f u=f v) →
    ∀ u v, S u → S v → f u=f v

private theorem bag_uniform (G : Graph n) (s : List (Fin n)) (hc : G.connected s=true) :
    Uniform G (·∈s) := by
  match s with
  | [] => simp [connected] at hc
  | [v] => intro f h u w hu hw; simp_all
  | x::y::s =>
    obtain ⟨he,ht⟩ := Bool.and_eq_true_iff.mp hc
    obtain ⟨z,hz,hed⟩ := List.any_eq_true.mp he
    have ih := bag_uniform G (y::s) ht
    intro f h u v hu hv
    have old := ih f (fun a b ha hb e => h a b (.tail _ ha) (.tail _ hb) e)
    have hx : f x=f z := h x z (by simp) (.tail _ hz) hed
    have urel : f u=f z := by
      rcases List.mem_cons.mp hu with eq|mem
      · simpa [eq] using hx
      · exact old _ _ mem hz
    have vrel : f v=f z := by
      rcases List.mem_cons.mp hv with eq|mem
      · simpa [eq] using hx
      · exact old _ _ mem hz
    exact urel.trans vrel.symm

private theorem union_uniform {G : Graph n} {s t : List (Fin n)}
    (hs : G.connected s=true) (ht : G.connected t=true) (he : G.links s t=true) :
    Uniform G (fun u => u∈s ∨ u∈t) := by
  obtain ⟨x,hx,ex⟩ := List.any_eq_true.mp he
  obtain ⟨y,hy,ey⟩ := List.any_eq_true.mp ex
  intro f h u v hu hv
  have sconst := bag_uniform _ _ hs f (fun a b ha hb e => h _ _ (.inl ha) (.inl hb) e)
  have tconst := bag_uniform _ _ ht f (fun a b ha hb e => h _ _ (.inr ha) (.inr hb) e)
  have xy := h _ _ (.inl hx) (.inr hy) ey
  rcases hu with hu|hu <;> rcases hv with hv|hv
  · exact sconst _ _ hu hv
  · exact (sconst _ _ hu hx).trans (xy.trans (tconst _ _ hy hv))
  · exact (tconst _ _ hu hy).trans (xy.symm.trans (sconst _ _ hx hv))
  · exact tconst _ _ hu hv

/-- The chords joining endpoints in two disjoint connected vertex sets
cannot cross. -/
private theorem no_alternation {G : Graph n} {apex : Fin n} (O : OuterOrder G apex)
    {A B : Fin n → Prop} (hA : Uniform G A) (hB : Uniform G B)
    (cleanA : ∀u, A u → u≠apex) (cleanB : ∀u, B u → u≠apex)
    (disj : ∀u v, A u → B v → u≠v) (u v x y : Fin n)
    (hu : A u) (hv : A v) (hx : B x) (hy : B y) :
    noncross (O.rank u) (O.rank v) (O.rank x) (O.rank y) := by
  have dr {a b} (ha : A a) (hb : B b) : O.rank a ≠ O.rank b :=
    fun e => disj a b ha hb (O.inj a b e)
  apply hB (fun z => between (O.rank u) (O.rank v) (O.rank z)) _ _ _ hx hy
  intro p q hP hQ pq
  change noncross _ _ _ _
  rw [noncross_swap (dr hu hP) (dr hu hQ) (dr hv hP) (dr hv hQ)]
  apply hA (fun z => between (O.rank p) (O.rank q) (O.rank z)) _ _ _ hu hv
  intro a b ha hb ab
  change noncross _ _ _ _
  rw [← noncross_swap (dr ha hP) (dr ha hQ) (dr hb hP) (dr hb hQ)]
  exact O.chords a b p q (cleanA _ ha) (cleanA _ hb) (cleanB _ hP) (cleanB _ hQ)
    (disj _ _ ha hP) (disj _ _ ha hQ) (disj _ _ hb hP) (disj _ _ hb hQ) ab pq


private def Drawing {k : Nat} (R : Fin k → Fin k → Bool) (z : Fin k)
    (r : Fin k → Nat) : Prop :=
  ∀ i j x y, i≠z → j≠z → x≠z → y≠z → i≠x → i≠y → j≠x → j≠y →
    R i j=true → R x y=true → noncross (r i) (r j) (r x) (r y)

private theorem drawing_of_minor {G : Graph n} {v : Fin n} (O : OuterOrder G v)
    {R : Fin k → Fin k → Bool} (anyIdx : Fin k)
    {bags : Fin k → List (Fin n)} (h : minorTest G R bags=true) :
    ∃ z r, (∀ i j, i≠j → r i≠r j) ∧ Drawing R z r := by
  classical
  have row (i) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h i (List.mem_finRange i))
  have pair (i j) := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (row i).2 j (List.mem_finRange j))
  have disj {i j : Fin k} (ij : i≠j) {u w} (hu : u∈bags i) (hw : w∈bags j) : u≠w := by
    intro eq; subst w
    have hd : disjoint (bags i) (bags j)=true := by simpa [ij] using (pair i j).1
    have := List.all_eq_true.mp hd u hu
    simp [hw] at this
  have link {i j} (e : R i j=true) : G.links (bags i) (bags j)=true := by
    simpa [e] using (pair i j).2
  have hz : ∃ z : Fin k, ∀i, i≠z → ∀u∈bags i, u≠v := by
    by_cases e : ∃j, v∈bags j
    · obtain ⟨j,m⟩ := e
      exact ⟨j,fun i ij u hu => disj ij hu m⟩
    · exact ⟨anyIdx,fun i _ u hu eq => e ⟨i,eq ▸ hu⟩⟩
  obtain ⟨z,hz⟩ := hz
  have ex (i : Fin k) : ∃ w, w∈bags i := by
    cases eq : bags i with
    | nil => have := (row i).1; simp [eq,connected] at this
    | cons w s => exact ⟨w,by simp⟩
  let rep (i : Fin k) := Classical.choose (ex i)
  have mem (i : Fin k) : rep i∈bags i := Classical.choose_spec (ex i)
  refine ⟨z,fun i => O.rank (rep i),fun i j ij eq =>
    disj ij (mem i) (mem j) (O.inj _ _ eq),?_⟩
  intro i j x y iz jz xz yz ix iy jx jy ij xy
  have L := union_uniform (row i).1 (row j).1 (link ij)
  have R' := union_uniform (row x).1 (row y).1 (link xy)
  apply no_alternation O L R' _ _ _ (rep i) (rep j) (rep x) (rep y)
    (.inl (mem _)) (.inr (mem _)) (.inl (mem _)) (.inr (mem _))
  · intro u hu; exact hu.elim (hz i iz u) (hz j jz u)
  · intro u hu; exact hu.elim (hz x xz u) (hz y yz u)
  · intro u w hu hw
    rcases hu with hu|hu <;> rcases hw with hw|hw
    · exact disj ix hu hw
    · exact disj iy hu hw
    · exact disj jx hu hw
    · exact disj jy hu hw

theorem noncross_iff (a b c d : Nat) : noncross a b c d ↔
    ((a<c ∧ c<b ∨ b<c ∧ c<a) ↔ (a<d ∧ d<b ∨ b<d ∧ d<a)) := by
  simp only [noncross,between,decide_eq_decide]
  by_cases h : a≤b <;> simp only [Nat.min_def,Nat.max_def,h,ite_true,ite_false] <;> omega

private theorem four_chords {a b c d : Nat} (ab : a≠b) (ac : a≠c) (ad : a≠d)
    (bc : b≠c) (bd : b≠d) (cd : c≠d) (u : noncross a c b d) (v : noncross a d b c) :
    ¬noncross a b c d := by
  intro h
  rw [noncross_iff] at h u v
  by_cases h1 : a<b <;> by_cases h2 : c<d <;>
    by_cases h3 : a<c <;> by_cases h4 : a<d <;>
    by_cases h5 : b<c <;> by_cases h6 : b<d <;> omega

private theorem clique_selection (z : Fin 5) :
    ∃ a b c d : Fin 5,
      a≠z ∧ b≠z ∧ c≠z ∧ d≠z ∧
      a≠b ∧ a≠c ∧ a≠d ∧ b≠c ∧ b≠d ∧ c≠d ∧
      clique5 a b=true ∧ clique5 a c=true ∧ clique5 a d=true ∧ clique5 b c=true ∧ clique5 b d=true ∧ clique5 c d=true := by
  have hz : z=0 ∨ z=1 ∨ z=2 ∨ z=3 ∨ z=4 := by
    simp only [Fin.ext_iff]; omega
  rcases hz with rfl|rfl|rfl|rfl|rfl
  · exact ⟨1,2,3,4,by decide⟩
  · exact ⟨0,2,3,4,by decide⟩
  · exact ⟨0,1,3,4,by decide⟩
  · exact ⟨0,1,2,4,by decide⟩
  · exact ⟨0,1,2,3,by decide⟩

set_option maxHeartbeats 6000000 in
private theorem clique_obstruction (z : Fin 5) (r : Fin 5 → Nat)
    (inj : ∀ i j, i≠j → r i≠r j) (h : Drawing clique5 z r) : False := by
  obtain ⟨a,b,c,d,az,bz,cz,dz,
    ab,ac,ad,bc,bd,cd,hab,hac,had,hbc,hbd,hcd⟩ := clique_selection z
  have dab := inj a b ab
  have dac := inj a c ac
  have dad := inj a d ad
  have dbc := inj b c bc
  have dbd := inj b d bd
  have dcd := inj c d cd
  have nabcd := (h a b c d az bz cz dz
    ac ad bc bd hab hcd)
  have nacbd := (h a c b d az cz bz dz
    ab ad (Ne.symm bc) cd hac hbd)
  have nadbc := (h a d b c az dz bz cz
    ab ac (Ne.symm bd) (Ne.symm cd) had hbc)
  exact four_chords dab dac dad dbc dbd dcd nacbd nadbc nabcd

private theorem bipartite_selection (z : Fin 6) :
    ∃ a b c d e : Fin 6,
      a≠z ∧ b≠z ∧ c≠z ∧ d≠z ∧ e≠z ∧
      a≠b ∧ a≠c ∧ a≠d ∧ a≠e ∧ b≠c ∧ b≠d ∧ b≠e ∧ c≠d ∧ c≠e ∧ d≠e ∧
      biclique33 a c=true ∧ biclique33 a d=true ∧ biclique33 a e=true ∧ biclique33 b c=true ∧ biclique33 b d=true ∧ biclique33 b e=true := by
  have hz : z=0 ∨ z=1 ∨ z=2 ∨ z=3 ∨ z=4 ∨ z=5 := by
    simp only [Fin.ext_iff]; omega
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨1,2,3,4,5,by decide⟩
  · exact ⟨0,2,3,4,5,by decide⟩
  · exact ⟨0,1,3,4,5,by decide⟩
  · exact ⟨4,5,0,1,2,by decide⟩
  · exact ⟨3,5,0,1,2,by decide⟩
  · exact ⟨3,4,0,1,2,by decide⟩

set_option maxHeartbeats 6000000 in
private theorem bipartite_obstruction (z : Fin 6) (r : Fin 6 → Nat)
    (inj : ∀ i j, i≠j → r i≠r j) (h : Drawing biclique33 z r) : False := by
  obtain ⟨a,b,c,d,e,az,bz,cz,dz,ez,
    ab,ac,ad,ae,bc,bd,be,cd,ce,de,hac,had,hae,hbc,hbd,hbe⟩ := bipartite_selection z
  have dab := inj a b ab
  have dac := inj a c ac
  have dad := inj a d ad
  have dae := inj a e ae
  have dbc := inj b c bc
  have dbd := inj b d bd
  have dbe := inj b e be
  have dcd := inj c d cd
  have dce := inj c e ce
  have dde := inj d e de
  have nacbd := (h a c b d az cz bz dz
    ab ad (Ne.symm bc) cd hac hbd)
  have nacbe := (h a c b e az cz bz ez
    ab ae (Ne.symm bc) ce hac hbe)
  have nadbc := (h a d b c az dz bz cz
    ab ac (Ne.symm bd) (Ne.symm cd) had hbc)
  have nadbe := (h a d b e az dz bz ez
    ab ae (Ne.symm bd) de had hbe)
  have naebc := (h a e b c az ez bz cz
    ab ac (Ne.symm be) (Ne.symm ce) hae hbc)
  have naebd := (h a e b d az ez bz dz
    ab ad (Ne.symm be) (Ne.symm de) hae hbd)
  have ncd := four_chords dab dac dad dbc dbd dcd nacbd nadbc
  have nce := four_chords dab dac dae dbc dbe dce nacbe naebc
  have nde := four_chords dab dad dae dbd dbe dde nadbe naebd
  unfold noncross at ncd nce nde
  have pigeon (i j k : Bool) : i≠j → i≠k → j≠k → False := by
    cases i <;> cases j <;> cases k <;> decide
  exact pigeon _ _ _ ncd nce nde

/-- Coning an abstract graph with a non-crossing chord order produces a
planar graph, also allowing arbitrary edges incident to the cone vertex. -/
theorem outer_order_planar {G : Graph n} {v : Fin n} (O : OuterOrder G v) : G.Planar := by
  constructor
  · rintro ⟨s,h⟩
    obtain ⟨z,r,inj,draw⟩ := drawing_of_minor O 0 h
    exact clique_obstruction z r inj draw
  · rintro ⟨s,h⟩
    obtain ⟨z,r,inj,draw⟩ := drawing_of_minor O 0 h
    exact bipartite_obstruction z r inj draw

end SparseBoundary.Fan
