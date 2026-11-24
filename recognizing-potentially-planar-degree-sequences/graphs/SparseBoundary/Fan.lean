import Std

/-! Integer augmentations on the path and the spokes of a double fan.
All counts in this file are *additional* edge multiplicities. -/

namespace SparseBoundary.Fan

/-- `Packing i cs x ds` assigns weights to consecutive path edges.
The initial incoming weight is `i`, the outgoing weights sum to `x`, and
`ds` lists the capacities left at the individual vertices. The last vertex
has outgoing weight zero. -/
inductive Packing : Nat → List Nat → Nat → List Nat → Prop where
  | nil : Packing 0 [] 0 []
  | cons {i o d c m : Nat} {cs ds : List Nat} (hc : i + o + d = c)
      (tail : Packing o cs m ds) : Packing i (c :: cs) (o + m) (d :: ds)

theorem Packing.total (h : Packing i cs x ds) : cs.sum = i + 2*x + ds.sum := by
  induction h with
  | nil => simp
  | cons hc _ ih => simp only [List.sum_cons]; omega

theorem Packing.append (h : Packing i cs x ds) (k : Packing 0 es y fs) :
    Packing i (cs ++ es) (x+y) (ds ++ fs) := by
  induction h with
  | nil => simpa using k
  | @cons i o d c m cs ds hc tail ih =>
    simpa [Nat.add_assoc] using Packing.cons hc ih

theorem Packing.trim (h : Packing i cs x ds) (hj : j ≤ i) (hy : y ≤ x) :
    ∃ fs, Packing j cs y fs := by
  induction h generalizing j y with
  | nil =>
    have : j = 0 := by omega
    have : y = 0 := by omega
    subst j; subst y; exact ⟨[], Packing.nil⟩
  | @cons i o d c m cs ds hc tail ih =>
    let u := min o y
    have hu : u ≤ o := Nat.min_le_left .. 
    have huv : u ≤ y := Nat.min_le_right ..
    have hm : y-u ≤ m := by dsimp [u]; omega
    obtain ⟨fs, hf⟩ := ih hu hm
    have hh : j + u + (c-(j+u)) = c := by omega
    exact ⟨_, by simpa [show u + (y-u) = y by omega] using Packing.cons hh hf⟩

/-- Split each residual into two spoke weights. -/
inductive Spokes : List Nat → Nat → Nat → Prop where
  | nil : Spokes [] 0 0
  | cons (l r : Nat) (tail : Spokes ds a b) :
      Spokes ((l+r) :: ds) (l+a) (r+b)

theorem spokes_of_sum (ds : List Nat) (a b : Nat) (h : ds.sum = a+b) :
    Spokes ds a b := by
  induction ds generalizing a b with
  | nil =>
    have : a = 0 := by simp at h; omega
    have : b = 0 := by simp at h; omega
    simp_all [Spokes.nil]
  | cons d ds ih =>
    let l := min a d
    let r := d-l
    have hrs : r ≤ b := by simp only [List.sum_cons] at h; dsimp [r,l]; omega
    have hls : l ≤ a := Nat.min_le_left ..
    have hlr : l+r = d := by dsimp [r,l]; omega
    have rest : ds.sum = (a-l)+(b-r) := by simp only [List.sum_cons] at h; omega
    simpa [hlr, show l+(a-l)=a by omega, show r+(b-r)=b by omega] using
      Spokes.cons l r (ih (a-l) (b-r) rest)

/-- A single witness assigns path edges, the centre edge, and all spokes. -/
def Filled (cs : List Nat) (a b : Nat) : Prop :=
  ∃ z x ds l r, Packing 0 cs x ds ∧ Spokes ds l r ∧ z+l=a ∧ z+r=b

theorem fill_of_packing (h : Packing 0 cs x ds) (hba : b ≤ a)
    (hbal : a ≤ cs.sum+b) (hpar : (cs.sum+a+b)%2 = 0)
    (hleft : ds.sum ≤ a+b) : Filled cs a b := by
  have ht := h.total
  by_cases hab : a+b ≤ cs.sum
  · let y := (cs.sum-a-b)/2
    have hy : y ≤ x := by dsimp [y]; omega
    obtain ⟨fs,hf⟩ := h.trim (j:=0) (by decide) hy
    have ht' := hf.total
    have hs : fs.sum=a+b := by dsimp [y] at *; omega
    exact ⟨0,y,fs,a,b,hf,spokes_of_sum fs a b hs,by omega,by omega⟩
  · let z := (a+b-cs.sum)/2
    obtain ⟨fs,hf⟩ := h.trim (j:=0) (y:=0) (by decide) (Nat.zero_le _)
    have ht' := hf.total
    have hzb : z ≤ b := by dsimp [z]; omega
    have hs : fs.sum=(a-z)+(b-z) := by dsimp [z] at *; omega
    exact ⟨z,0,fs,a-z,b-z,hf,spokes_of_sum fs _ _ hs,by omega,by omega⟩

private theorem one (a : Nat) : Packing 0 [a] 0 [a] := by
  exact Packing.cons (o:=0) (by omega) Packing.nil

private theorem two {a b : Nat} (hab : a ≤ b) :
    Packing 0 [a,b] a [0,b-a] := by
  exact Packing.cons (o:=a) (by omega)
    (Packing.cons (o:=0) (by omega) Packing.nil)

private theorem three {a b c : Nat} (hab : a < b) (hbc : b < c) (ha : 0 < a) :
    ∃ x ds, Packing 0 [a,c,b] x ds ∧ ds.sum + 3 ≤ c+1 := by
  let v := min (c-a) b
  have hv : a+v ≤ c := by dsimp [v]; omega
  have hv' : v ≤ b := Nat.min_le_right ..
  refine ⟨_,_,Packing.cons (o:=a) (d:=0) (by omega)
    (Packing.cons (o:=v) (d:=c-a-v) (by omega)
    (Packing.cons (o:=0) (d:=b-v) (by omega) Packing.nil)),?_⟩
  simp only [List.sum_cons,List.sum_nil]; dsimp [v]; omega

private theorem four {a b c d : Nat} (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∃ x ds, Packing 0 [a,c,d,b] x ds ∧ ds.sum + a + 3 ≤ d := by
  let v := c-a
  let w := min b (d-v)
  have hw : w ≤ b := Nat.min_le_left ..
  have hw' : v+w ≤ d := by dsimp [v,w]; omega
  refine ⟨_,_,Packing.cons (o:=a) (d:=0) (by omega)
    (Packing.cons (o:=v) (d:=0) (by dsimp [v]; omega)
    (Packing.cons (o:=w) (d:=d-v-w) (by omega)
    (Packing.cons (o:=0) (d:=b-w) (by omega) Packing.nil))),?_⟩
  simp only [List.sum_cons,List.sum_nil]; dsimp [w,v]; omega


/-- Non-strict capacities may be matched in pairs. -/
theorem paired_layout (ws : List Nat) (M : Nat)
    (hs : ws.Pairwise (· ≥ ·)) (hm : ∀ z ∈ ws, z ≤ M) :
    ∃ ord x ds, ws.Perm ord ∧ Packing 0 ord x ds ∧ ds.sum ≤ M := by
  match ws with
  | [] => exact ⟨[],0,[],.nil,.nil,by simp⟩
  | [c] => exact ⟨[c],0,[c],.refl _,one c,by simpa using hm c (by simp)⟩
  | c :: b :: xs =>
    have hbc : b ≤ c := List.rel_of_pairwise_cons hs (by simp)
    have hc := hm c (by simp)
    obtain ⟨ord,x,ds,perm,hp,hh⟩ := paired_layout xs b hs.of_cons.of_cons
      (List.pairwise_cons.mp hs.of_cons).1
    refine ⟨[b,c]++ord, _, _, (List.Perm.swap b c []).append perm,
      (two hbc).append hp,?_⟩
    simp only [List.sum_append,List.sum_cons,List.sum_nil]; omega

/-- With distinct positive capacities the leftover decreases by the path
length, up to the endpoint constant. The construction rearranges each block
of four and handles all three possible terminal nonempty blocks. -/
theorem strict_layout (ws : List Nat) (M : Nat)
    (hs : ws.Pairwise (· > ·)) (hm : ∀ z ∈ ws, z ≤ M)
    (hz : ∀ z ∈ ws, 0 < z) :
    ∃ ord x ds, ws.Perm ord ∧ Packing 0 ord x ds ∧
      ds.sum + ws.length ≤ M+1 := by
  match ws with
  | [] => exact ⟨[],0,[],.nil,.nil,by simp⟩
  | [a] =>
    have := hm a (by simp)
    exact ⟨[a],0,[a],.refl _,one a,by simpa⟩
  | [b,a] =>
    have hab : a < b := List.rel_of_pairwise_cons hs (by simp)
    have hb := hm b (by simp)
    have ha := hz a (by simp)
    refine ⟨[a,b],a,[0,b-a], .swap a b [], two (by omega),?_⟩
    simp; omega
  | [c,b,a] =>
    have hab : a < b := List.rel_of_pairwise_cons hs.of_cons (by simp)
    have hbc : b < c := List.rel_of_pairwise_cons hs (by simp)
    obtain ⟨x,ds,hp,hh⟩ := three hab hbc (hz a (by simp))
    have hm' := hm c (by simp)
    refine ⟨[a,c,b],x,ds,?_,hp,?_⟩
    · exact ((List.Perm.swap a b []).cons c).trans (.swap a c [b])
    · simp; omega
  | d :: c :: b :: a :: xs =>
    have hab : a < b := List.rel_of_pairwise_cons hs.of_cons.of_cons (by simp)
    have hbc : b < c := List.rel_of_pairwise_cons hs.of_cons (by simp)
    have hcd : c < d := List.rel_of_pairwise_cons hs (by simp)
    have hd := hm d (by simp)
    have ha := hz a (by simp)
    obtain ⟨y,us,hu,hi⟩ := four hab hbc hcd
    have hbnd : ∀ z ∈ xs, z ≤ a-1 := by
      intro z h
      have : z<a := List.rel_of_pairwise_cons hs.of_cons.of_cons.of_cons h
      omega
    obtain ⟨ord,x,ds,perm,hp,hh⟩ :=
      strict_layout xs (a-1) hs.of_cons.of_cons.of_cons.of_cons hbnd
        (by intro z h; exact hz z (by simp [h]))
    have localPerm : [d,c,b,a].Perm [a,c,d,b] := by
      apply List.perm_iff_count.mpr
      intro z
      simp only [List.count_cons,List.count_nil]
      omega
    refine ⟨[a,c,d,b]++ord,_,_,localPerm.append perm,hu.append hp,?_⟩
    simp only [List.sum_append,List.length_cons]; omega

/-- Put one extra capacity at the last path vertex. -/
def bumpLast : List Nat → List Nat
  | [] => []
  | [a] => [a+1]
  | a :: b :: cs => a :: bumpLast (b :: cs)

private theorem bumpLast_sum (h : cs ≠ []) : (bumpLast cs).sum = cs.sum+1 := by
  match cs with
  | [a] => simp [bumpLast]
  | a :: b :: cs =>
    simp only [bumpLast,List.sum_cons]
    have := bumpLast_sum (cs:=b::cs) (by simp)
    simp only [List.sum_cons] at this
    omega

private theorem Packing.bumpLast (h : Packing i cs x ds) (hn : cs ≠ []) :
    ∃ fs, Packing i (Fan.bumpLast cs) x fs ∧ fs.sum=ds.sum+1 := by
  induction h with
  | nil => contradiction
  | @cons i o d c m cs ds hc tail ih =>
    cases cs with
    | nil =>
      cases tail
      refine ⟨[d+1],Packing.cons (o:=0) (by omega) Packing.nil,?_⟩
      simp
    | cons b cs =>
      obtain ⟨fs,hf,hh⟩ := ih (by simp)
      exact ⟨_, Packing.cons hc hf,by simp [hh,Nat.add_assoc]⟩

/-- The true capacities give each end one unit over its base capacity.
On a single-vertex list this adds both units at that vertex. -/
def ends : List Nat → List Nat
  | [] => []
  | a::cs => bumpLast ((a+1)::cs)

theorem ends_sum (h : cs ≠ []) : (ends cs).sum=cs.sum+2 := by
  obtain ⟨a,rs,rfl⟩ := List.exists_cons_of_ne_nil h
  change (bumpLast ((a+1)::rs)).sum = (a::rs).sum+2
  rw [bumpLast_sum (by simp)]
  simp only [List.sum_cons]; omega

theorem Packing.ends (h : Packing 0 cs x ds) (hn : cs ≠ []) :
    ∃ fs, Packing 0 (Fan.ends cs) x fs ∧ fs.sum=ds.sum+2 := by
  cases h with
  | nil => contradiction
  | @cons i o d c m cs ds hc ht =>
    have h' : Packing 0 ((c+1)::cs) (o+m) ((d+1)::ds) :=
      Packing.cons (by omega) ht
    obtain ⟨fs,hf,hh⟩ := h'.bumpLast (by simp)
    refine ⟨fs,hf,?_⟩
    simp only [List.sum_cons] at *; omega

private theorem perm_sum {u v : List Nat} (h : u.Perm v) : u.sum=v.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp [Nat.add_left_comm]
  | trans _ _ i j => exact i.trans j

/-- Sufficient criterion for an actual integral weight assignment on a double
fan, for arbitrary positive length and weakly ordered capacities. -/
theorem fill_paired (ws : List Nat) (a b M : Nat) (hn : ws ≠ [])
    (hord : ws.Pairwise (· ≥ ·)) (hub : ∀ v ∈ ws, v ≤ M)
    (hba : b ≤ a) (hbal : a ≤ ws.sum+2+b)
    (hpar : (ws.sum+2+a+b)%2=0) (hsize : M+2 ≤ a+b) :
    ∃ ord, ws.Perm ord ∧ Filled (ends ord) a b := by
  obtain ⟨ord,x,ds,perm,hp,hh⟩ := paired_layout ws M hord hub
  have hn' : ord ≠ [] := by intro he; apply hn; simpa [he] using perm
  obtain ⟨fs,hf,hfs⟩ := hp.ends hn'
  have hsum := (perm_sum perm)
  have he := ends_sum hn'
  exact ⟨ord,perm,fill_of_packing hf hba (by omega) (by omega) (by omega)⟩

/-- Stronger sufficient criterion for all strict positive capacity lists. -/
theorem fill_strict (ws : List Nat) (a b M : Nat) (hn : ws ≠ [])
    (hord : ws.Pairwise (· > ·)) (hub : ∀ v ∈ ws, v ≤ M) (hpos : ∀ v ∈ ws, 0<v)
    (hba : b ≤ a) (hbal : a ≤ ws.sum+2+b)
    (hpar : (ws.sum+2+a+b)%2=0) (hsize : M+3 ≤ a+b+ws.length) :
    ∃ ord, ws.Perm ord ∧ Filled (ends ord) a b := by
  obtain ⟨ord,x,ds,perm,hp,hh⟩ := strict_layout ws M hord hub hpos
  have hn' : ord ≠ [] := by intro he; apply hn; simpa [he] using perm
  obtain ⟨fs,hf,hfs⟩ := hp.ends hn'
  have hsum := perm_sum perm
  have he := ends_sum hn'
  exact ⟨ord,perm,fill_of_packing hf hba (by omega) (by omega) (by omega)⟩

private theorem five_penalty (xs : List Nat) (hm : ∀ d ∈ xs, 5 ≤ d) :
    6*xs.length ≤ xs.sum + xs.count 5 := by
  induction xs with
  | nil => simp
  | cons d xs ih =>
    have hd := hm d (by simp)
    have hi := ih (by intro i hi; exact hm i (by simp [hi]))
    by_cases h : d=5
    · subst d; simp; omega
    · simp [h]; omega

/-- The counting step for both boundaries. Remove a largest entry `a` and
one occurrence of the smallest repeated value `g`; the remaining entries
form `xs`. The condition on `xs.count 5` follows as soon as `g>5`.
The proof avoids the quadratic estimates from counting all small values. -/
theorem terminal_dominance {p t a g : Nat} (xs : List Nat)
    (hn : p = xs.length + 2) (hp : 8 ≤ p)
    (hm : ∀ d ∈ xs, 5 ≤ d) (h5 : 5 < g → xs.count 5 ≤ 1)
    (ha : a ≤ t + 4) (hg : g ≤ a)
    (hvol : a + g + xs.sum ≤ 4*p + 2*t)
    (hfail : p+t+1 < a+g) : 2*p ≤ a+4 ∧ p ≤ g+2 := by
  have hgap : p ≤ g+2 := by omega
  have hlarge : 5 < g := by omega
  have hcount := h5 hlarge
  have := five_penalty xs hm
  constructor <;> omega

private theorem subtract_four_sum (xs : List Nat) (hm : ∀ i ∈ xs, 4 ≤ i) :
    (xs.map (·-4)).sum + 4*xs.length = xs.sum := by
  induction xs with
  | nil => simp
  | cons v xs ih =>
    have hv := hm v (by simp)
    have := ih (by intro i hi; exact hm i (by simp [hi]))
    simp; omega

private theorem subtract_four_sorted (xs : List Nat) (ho : xs.Pairwise (· ≥ ·)) :
    (xs.map (·-4)).Pairwise (· ≥ ·) := by
  induction xs with
  | nil => simp
  | cons v xs ih =>
    simp only [List.map_cons,List.pairwise_cons]
    refine ⟨?_,ih ho.of_cons⟩
    intro y hy
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hy
    have := List.rel_of_pairwise_cons ho hi
    omega

private theorem subtract_four_strict (xs : List Nat) (ho : xs.Pairwise (· > ·))
    (hm : ∀ i ∈ xs, 4 ≤ i) : (xs.map (·-4)).Pairwise (· > ·) := by
  induction xs with
  | nil => simp
  | cons v xs ih =>
    simp only [List.map_cons,List.pairwise_cons]
    refine ⟨?_,ih ho.of_cons (by intro d hd; exact hm d (by simp [hd]))⟩
    intro y hy
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hy
    have := List.rel_of_pairwise_cons ho hi
    have := hm i (by simp [hi])
    omega

/-- Completed weight assignment in the degree variables of the paper.
`us` are all target degrees except the two hubs. -/
def DegreeWeights (a b : Nat) (us : List Nat) : Prop :=
  ∃ ord, (us.map (·-4)).Perm ord ∧
    Filled (ends ord) (a-(us.length+1)) (b-(us.length+1))

/-- The general double-fan bound. Here `H=a+b+us.sum`, `p=us.length+2`;
the hub balance inequality is `2a+4p ≤ H+10`. -/
theorem degree_weights_paired {a b c p : Nat} (us : List Nat)
    (hp : p=us.length+2) (hn : us ≠ []) (ho : us.Pairwise (· ≥ ·))
    (hb : p ≤ b+1) (hba : b ≤ a)
    (hmin : ∀ d ∈ us, 5 ≤ d) (hmax : ∀ d ∈ us, d ≤ c) (hc : 4 ≤ c)
    (hbal : 2*a+4*p ≤ a+b+us.sum+10)
    (hpar : (a+b+us.sum)%2=0)
    (hh : 2*p+c ≤ a+b+4) : DegreeWeights a b us := by
  have hs := subtract_four_sum us (by intro i hi; have := hmin i hi; omega)
  apply fill_paired _ _ _ (c-4) (by simpa using hn) (subtract_four_sorted us ho)
  · intro v hv
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hv
    have := hmax d hd
    omega
  · omega
  · omega
  · omega
  · omega

/-- If the tail has distinct entries its largest capacity is allowed to
exceed the combined hub budget by its length minus three. -/
theorem degree_weights_strict {a b c p : Nat} (us : List Nat)
    (hp : p=us.length+2) (hn : us ≠ []) (ho : us.Pairwise (· > ·))
    (hb : p ≤ b+1) (hba : b ≤ a)
    (hmin : ∀ d ∈ us, 5 ≤ d) (hmax : ∀ d ∈ us, d ≤ c) (hc : 4 ≤ c)
    (hbal : 2*a+4*p ≤ a+b+us.sum+10)
    (hpar : (a+b+us.sum)%2=0)
    (hh : c+p ≤ a+b+1) : DegreeWeights a b us := by
  have hm : ∀ d ∈ us, 4 ≤ d := by intro d hd; have := hmin d hd; omega
  have hs := subtract_four_sum us hm
  apply fill_strict _ _ _ (c-4) (by simpa using hn) (subtract_four_strict us ho hm)
  · intro v hv
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hv
    have := hmax d hd
    omega
  · intro v hv
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hv
    have := hmin d hd
    omega
  · omega
  · omega
  · omega
  · simp only [List.length_map]; omega


private theorem strict_of_counts (xs : List Nat) (ho : xs.Pairwise (· ≥ ·))
    (hc : ∀ g, xs.count g ≤ 1) : xs.Pairwise (· > ·) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    refine List.pairwise_cons.mpr ⟨?_,ih ho.of_cons (fun g =>
      Nat.le_trans List.count_le_count_cons (hc g))⟩
    intro b hb
    have hab : a ≥ b := List.rel_of_pairwise_cons ho hb
    have hne : b ≠ a := by
      rintro rfl
      have hn := List.count_pos_iff.mpr hb
      have := hc b
      simp at this; omega
    omega

private theorem strict_length (xs : List Nat) (hi : Nat)
    (ho : xs.Pairwise (· > ·)) (hmax : ∀ i ∈ xs, i < hi)
    (hmin : ∀ i ∈ xs, 5 ≤ i) (hhi : 5 ≤ hi) : xs.length+5 ≤ hi := by
  induction xs generalizing hi with
  | nil => simp [hhi]
  | cons a xs ih =>
    have ha := hmax a (by simp)
    have hl := hmin a (by simp)
    have hn := ih a ho.of_cons (List.pairwise_cons.mp ho).1
      (fun v hv => hmin v (by simp [hv])) hl
    simp; omega

/-- The precise maximum-degree condition after deleting equal entries. -/
def Deletable (xs : List Nat) (p t : Nat) : Prop :=
  ∃ g rs, xs.Perm (g::g::rs) ∧ ∀ d ∈ rs, d+g ≤ p+t+1

private theorem repeated_witness {g : Nat} {xs : List Nat} (h : 2 ≤ xs.count g) :
    ∃ rs, xs.Perm (g :: g :: rs) := by
  have h1 : g ∈ xs := List.count_pos_iff.mp (by omega)
  have h2 : g ∈ xs.erase g := List.count_pos_iff.mp (by rw [List.count_erase_self]; omega)
  exact ⟨_, (List.perm_cons_erase h1).trans ((List.perm_cons_erase h2).cons g)⟩

private theorem repeat_or_strict {a b c : Nat} (us : List Nat)
    (hs : (a::b::c::us).Pairwise (· ≥ ·)) :
    (a::b::c::us).Pairwise (· > ·) ∨
    ∃ g, 2 ≤ (a::b::c::us).count g ∧ (5<g → (a::b::c::us).count 5 ≤ 1) := by
  by_cases h5 : 2 ≤ (a::b::c::us).count 5
  · exact .inr ⟨5,h5,by omega⟩
  by_cases hd : ∃ g, 2 ≤ (a::b::c::us).count g
  · obtain ⟨g,hg⟩ := hd; exact .inr ⟨g,hg,by omega⟩
  · exact .inl (strict_of_counts _ hs (by intro g; have : ¬ 2 ≤ (a::b::c::us).count g :=
                                            fun h => hd ⟨g,h⟩; omega))

/-- Exhaustive reduction for cores of minimum degree five on the two layers.
`k=1` selects volume `4n-2`; `k=0` selects volume `4n`.
The conclusions are the cone range, a deletable pair, actual double-fan
weights, or the upper-layer four-spoke wheel range, respectively. -/
theorem min_five_cases_with_hub_bound {a b c p t k : Nat} (us : List Nat)
    (hp : p=us.length+3) (hp8 : 8≤p) (hk : k≤1)
    (hs : (a::b::c::us).Pairwise (· ≥ ·))
    (hmin : ∀ d ∈ a::b::c::us, 5 ≤ d)
    (hvol : (a::b::c::us).sum+2*k=4*p+2*t) :
    t+5 ≤ a+k ∨ Deletable (a::b::c::us) p t ∨ (p≤b+1 ∧ DegreeWeights a b (c::us)) ∨
      (k=0 ∧ a=t+4 ∧ b=p-2) := by
  have hab : b≤a := List.rel_of_pairwise_cons hs (by simp)
  have hbc : c≤b := List.rel_of_pairwise_cons hs.of_cons (by simp)
  have hc := hmin c (by simp)
  have hm : ∀ d ∈ c::us, 5 ≤ d := fun d hd => hmin d (by simp [hd])
  have hu : ∀ d ∈ c::us, d ≤ c := by
    intro d hd
    rcases List.mem_cons.mp hd with he|he
    · omega
    · exact List.rel_of_pairwise_cons hs.of_cons.of_cons he
  by_cases cone : t+5 ≤ a+k
  · exact .inl cone
  by_cases del : Deletable (a::b::c::us) p t
  · exact .inr (.inl del)
  apply Or.inr; apply Or.inr
  have hb0 : 2*a+4*p ≤ a+b+(c::us).sum+10 := by simp only [List.sum_cons] at *; omega
  have he : (a+b+(c::us).sum)%2=0 := by simp only [List.sum_cons] at *; omega
  have plen : p=(c::us).length+2 := by simp; omega
  rcases repeat_or_strict us hs with strict|⟨g,hg,h5⟩
  · have hab' : b < a := List.rel_of_pairwise_cons strict (by simp)
    have hbc' : c < b := List.rel_of_pairwise_cons strict.of_cons (by simp)
    have hc' := strict_length us c strict.of_cons.of_cons.of_cons
      (List.pairwise_cons.mp strict.of_cons.of_cons).1
      (fun v hv => hm v (by simp [hv])) hc
    exact .inl ⟨by omega,degree_weights_strict _ plen (by simp) strict.of_cons.of_cons
      (by omega) hab hm hu (by omega) hb0 he (by omega)⟩
  · obtain ⟨rs,perm⟩ := repeated_witness hg
    have fail : ¬ (∀ d ∈ rs, d+g ≤ p+t+1) := fun h => del ⟨g,rs,perm,h⟩
    have xub : ∀ d ∈ a::b::c::us, d≤a := by
      intro d hd
      rcases List.mem_cons.mp hd with he'|hr
      · omega
      · exact List.rel_of_pairwise_cons hs hr
    have hag : p+t+1 < a+g := by
      apply Nat.lt_of_not_ge
      intro bad
      apply fail
      intro d hd
      have := xub d (perm.mem_iff.mpr (by simp [hd]))
      omega
    have hgt : g ∈ b::c::us := by
      apply List.count_pos_iff.mp
      have hh : (a::b::c::us).count g ≤ (b::c::us).count g+1 := by
        rw [List.count_cons]; split <;> omega
      omega
    have hgb : g ≤ b := by
      rcases List.mem_cons.mp hgt with he'|hr
      · omega
      · exact List.rel_of_pairwise_cons hs.of_cons hr
    let xs := (b::c::us).erase g
    have p' := List.perm_cons_erase hgt
    have plen' := p'.length_eq
    have sum' := perm_sum p'
    have hx5 : 5 < g → xs.count 5 ≤ 1 := by
      intro hbig
      exact Nat.le_trans ((List.erase_sublist (a:=g)).count_le 5)
        (Nat.le_trans List.count_le_count_cons (h5 hbig))
    have hl : ∀ v ∈ xs, 5≤v := by
      intro v hv
      have hm' : v ∈ b::c::us := List.mem_of_mem_erase hv
      exact hmin v (by simp [hm'])
    have len' : p = xs.length + 2 := by
      change _ = ((b::c::us).erase g).length + 2
      simp only [List.length_cons] at plen'; omega
    have vol' : a+g+xs.sum ≤ 4*p+2*t := by
      dsimp [xs]; simp only [List.sum_cons] at sum' hvol; omega
    have dom := terminal_dominance xs len' hp8 hl hx5 (by omega) (by omega) vol' hag
    by_cases wide : p≤b+1
    · exact .inl ⟨wide,degree_weights_paired _ plen (by simp) hs.of_cons.of_cons
        wide hab hm hu (by omega) hb0 he (by omega)⟩
    · exact .inr (by omega)

theorem min_five_cases {a b c p t k : Nat} (us : List Nat)
    (hp : p=us.length+3) (hp8 : 8≤p) (hk : k≤1)
    (hs : (a::b::c::us).Pairwise (· ≥ ·))
    (hmin : ∀ d ∈ a::b::c::us, 5 ≤ d)
    (hvol : (a::b::c::us).sum+2*k=4*p+2*t) :
    t+5 ≤ a+k ∨ Deletable (a::b::c::us) p t ∨ DegreeWeights a b (c::us) ∨
      (k=0 ∧ a=t+4 ∧ b=p-2) := by
  rcases min_five_cases_with_hub_bound us hp hp8 hk hs hmin hvol with h|h|⟨_,w⟩|h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl w))
  · exact .inr (.inr (.inr h))

end SparseBoundary.Fan
