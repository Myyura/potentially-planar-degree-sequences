import DiskFullerene.CheckMap
import DiskFullerene.ConstructionSphere

namespace DiskFullerene.PrimalSplice

/-- Graphs live on disjoint finite sets of names in a common ambient type.
Only the designated vertex is required to be trivalent in this lemma. -/
structure Arm where
  vertex : Nat → Prop
  edge : Nat → Nat → Prop
  endpoints : ∀ {x y}, edge x y → vertex x ∧ vertex y
  symm : ∀ {x y}, edge x y → edge y x
  cut : Nat
  cutValid : vertex cut
  port : Fin 3 → Nat
  portsValid : ∀ i, vertex (port i) ∧ port i ≠ cut
  portsDifferent : Function.Injective port
  neighbors : ∀ x, edge x cut ↔ ∃ i, port i=x
  conn : ∀ gone : List Nat, gone.length ≤ 2 → ∀ x y, vertex x → vertex y →
    x ∉ gone → y ∉ gone → PathAvoiding edge gone x y

def Arm.stays (A : Arm) (v : Nat) := A.vertex v ∧ v ≠ A.cut

def keepVertex (A B : Arm) (v : Nat) := A.stays v ∨ B.stays v

inductive Edge (A B : Arm) : Nat → Nat → Prop where
  | left {u v} : A.stays u → A.stays v → A.edge u v → Edge A B u v
  | right {u v} : B.stays u → B.stays v → B.edge u v → Edge A B u v
  | bridge (i : Fin 3) : Edge A B (A.port i) (B.port i)
  | back (i : Fin 3) : Edge A B (B.port i) (A.port i)

private theorem symm {A B : Arm} (u v : Nat) (e : Edge A B u v) : Edge A B v u := by
  cases e with
  | left u v e => exact .left v u (A.symm e)
  | right u v e => exact .right v u (B.symm e)
  | bridge i => exact .back i
  | back i => exact .bridge i

private noncomputable def bad (A : Arm) (erased : List Nat) := by
  classical
  exact erased.filter (fun x => decide (A.stays x))

private theorem bad_mem (A : Arm) (erased : List Nat) (v : Nat) :
    v ∈ bad A erased ↔ v ∈ erased ∧ A.stays v := by
  classical simp [bad]

private theorem badLength (A B : Arm) (disjoint : ∀ x, A.vertex x → ¬B.vertex x) (erased : List Nat) :
    (bad A erased).length + (bad B erased).length ≤ erased.length := by
  classical
  induction erased with
  | nil => simp [bad]
  | cons x xs ih =>
    have ne : ¬(A.stays x ∧ B.stays x) := fun h => disjoint x h.1.1 h.2.1
    simp only [bad,List.filter_cons,List.length_cons] at *
    split <;> split <;> simp_all <;> omega

private theorem pathDomain (A : Arm) {d a b} (start : A.vertex a)
    (p : PathAvoiding A.edge d a b) : A.vertex b := by
  cases p with
  | here => exact start
  | step _ e _ => exact (A.endpoints e).2

private theorem liftRoute (A : Arm) {E : Nat → Nat → Prop} (erased : List Nat)
    (lift : ∀ {x y}, A.stays x → A.stays y → A.edge x y → E x y)
    (ha : A.vertex a) (p : PathAvoiding A.edge (A.cut :: bad A erased) a b) :
    PathAvoiding E erased a b := by
  have good (v : Nat) (hv : A.vertex v) (ok : v ∉ A.cut::bad A erased) :
      A.stays v ∧ v ∉ erased := by
    have hc : v ≠ A.cut := fun eq => ok (by simp [eq])
    exact ⟨⟨hv,hc⟩,fun e => ok (List.mem_cons_of_mem _ ((bad_mem ..).mpr ⟨e,hv,hc⟩))⟩
  induction p with
  | here ok => exact .here (good _ ha ok).2
  | step p e ok ih =>
    have tail := good _ (A.endpoints e).2 ok
    exact ih.step (lift (good _ (pathDomain A ha p) p.lastOK).1 tail.1 e) tail.2

/-- Given any surviving route to the cut vertex, stop one step before its
first visit. It ends at a surviving port. -/
private theorem reachPort (A : Arm) {bad : List Nat} {x : Nat} (hx : x ≠ A.cut)
    (r : PathAvoiding A.edge bad x A.cut) :
    ∃ i, PathAvoiding A.edge (A.cut :: bad) x (A.port i) := by
  have aux {y} (p : PathAvoiding A.edge bad x y) :
      PathAvoiding A.edge (A.cut::bad) x y ∨ ∃ i, PathAvoiding A.edge (A.cut::bad) x (A.port i) := by
    induction p with
    | here ok => exact Or.inl (.here (by simp [hx,ok]))
    | @step b c p e ok ih =>
      obtain h|h := ih
      · by_cases eq : c=A.cut
        · obtain ⟨i,pi⟩ := (A.neighbors b).mp (eq ▸ e)
          exact Or.inr ⟨i,pi ▸ h⟩
        · exact Or.inl (h.step e (by simp [eq,ok]))
      · exact Or.inr h
  obtain atCut|h := aux r
  · exact (atCut.lastOK (by simp)).elim
  · exact h

private theorem toPort (A : Arm) (erased : List Nat) (small : (bad A erased).length ≤ 2)
    (x : Nat) (hx : A.stays x) (survives : x ∉ erased)
    (lift : ∀ {x y}, A.stays x → A.stays y → A.edge x y → E x y) :
    ∃ i, PathAvoiding E erased x (A.port i) := by
  have hcut : A.cut ∉ bad A erased := by simp [bad_mem,Arm.stays]
  have start : x ∉ bad A erased := by simp [bad_mem,survives]
  obtain ⟨i,p⟩ := reachPort A hx.2 (A.conn _ small _ _ hx.1 A.cutValid start hcut)
  exact ⟨i,liftRoute A erased lift hx.1 p⟩

private theorem within (A : Arm) (erased : List Nat) (small : (bad A erased).length ≤ 1)
    (x y : Nat) (hx : A.stays x) (hy : A.stays y) (sx : x ∉ erased) (sy : y ∉ erased)
    (lift : ∀ {x y}, A.stays x → A.stays y → A.edge x y → E x y) :
    PathAvoiding E erased x y := by
  apply liftRoute A erased lift hx.1
  apply A.conn _ (by simp; omega) _ _ hx.1 hy.1
  · simp [hx.2,bad_mem,sx]
  · simp [hy.2,bad_mem,sy]

private theorem freePair (A B : Arm) (disjoint : ∀ x, A.vertex x → ¬ B.vertex x)
    (erased : List Nat) (len : erased.length ≤ 2) :
    ∃ i : Fin 3, A.port i ∉ erased ∧ B.port i ∉ erased := by
  classical
  let blocked (x : Nat) (i : Fin 3) := A.port i=x ∨ B.port i=x
  have unique (x : Nat) {i j : Fin 3} (u : blocked x i) (v : blocked x j) : i=j := by
    rcases u with a|a <;> rcases v with b|b
    · exact A.portsDifferent (a.trans b.symm)
    · exact (disjoint x (a ▸ (A.portsValid i).1) (b ▸ (B.portsValid j).1)).elim
    · exact (disjoint x (b ▸ (A.portsValid j).1) (a ▸ (B.portsValid i).1)).elim
    · exact B.portsDifferent (a.trans b.symm)
  have avoidTwo (x y : Nat) : ∃ i : Fin 3, ¬blocked x i ∧ ¬blocked y i := by
    by_cases h0 : ¬blocked x 0 ∧ ¬blocked y 0
    · exact ⟨0,h0⟩
    by_cases h1 : ¬blocked x 1 ∧ ¬blocked y 1
    · exact ⟨1,h1⟩
    refine ⟨2,?_⟩
    have d01 : (0 : Fin 3) ≠ 1 := by decide
    have d02 : (0 : Fin 3) ≠ 2 := by decide
    have d12 : (1 : Fin 3) ≠ 2 := by decide
    have excl (z : Nat) : (blocked z 0 → ¬blocked z 1) ∧
        (blocked z 0 → ¬blocked z 2) ∧ (blocked z 1 → ¬blocked z 2) :=
      ⟨fun a b => d01 (unique z a b),fun a b => d02 (unique z a b),fun a b => d12 (unique z a b)⟩
    have ex := excl x
    have ey := excl y
    grind only
  cases erased with
  | nil => exact ⟨0,by simp⟩
  | cons x xs => cases xs with
    | nil =>
      obtain ⟨i,h,_⟩ := avoidTwo x x
      exact ⟨i,by simpa [blocked] using h⟩
    | cons y ys =>
      have empty : ys=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
      subst ys
      obtain ⟨i,h,k⟩ := avoidTwo x y
      simp [blocked] at h k; exact ⟨i,by simp_all⟩

private theorem span (A B : Arm) {E : Nat → Nat → Prop} {erased : List Nat}
    (total : (bad A erased).length + (bad B erased).length ≤ 2)
    (smallB : (bad B erased).length ≤ 1)
    (li : ∀ {x y}, A.stays x → A.stays y → A.edge x y → E x y)
    (ri : ∀ {x y}, B.stays x → B.stays y → B.edge x y → E x y)
    (bridge : ∀ i, E (A.port i) (B.port i))
    (free : Fin 3) (aok : A.port free ∉ erased) (bok : B.port free ∉ erased)
    (x : Nat) (hx : A.stays x ∨ B.stays x) (sx : x ∉ erased) :
    PathAvoiding E erased x (B.port free) := by
  obtain h|h := hx
  · by_cases smallA : (bad A erased).length ≤ 1
    · exact (within A erased smallA x _ h (A.portsValid free) sx aok li).step (bridge free) bok
    · have empty : bad B erased=[] := List.length_eq_zero_iff.mp (by omega)
      obtain ⟨i,p⟩ := toPort A erased (by omega) x h sx li
      have bi : B.port i ∉ erased := fun e => by
        have contra := (bad_mem B erased _).mpr ⟨e,B.portsValid i⟩
        simp [empty] at contra
      exact (p.step (bridge i) bi).trans (within B erased smallB _ _ (B.portsValid i)
        (B.portsValid free) bi bok ri)
  · exact within B erased smallB x _ h (B.portsValid free) sx bok ri

/-- Delete the two distinguished trivalent vertices and match the corresponding
three neighbour pairs. Any two surviving vertices in the resulting graph can
still be joined after deleting at most two vertices, for any matching. -/
theorem vertexSumConnected (A B : Arm) (disjoint : ∀ x, A.vertex x → ¬ B.vertex x)
    (erased : List Nat) (len : erased.length ≤ 2) {x y : Nat}
    (hx : keepVertex A B x) (hy : keepVertex A B y) (sx : x ∉ erased) (sy : y ∉ erased) :
    PathAvoiding (Edge A B) erased x y := by
  have total := Nat.le_trans (badLength A B disjoint erased) len
  obtain ⟨i,ai,bi⟩ := freePair A B disjoint erased len
  by_cases sm : (bad B erased).length ≤ 1
  · have route := span A B total sm Edge.left Edge.right Edge.bridge i ai bi
    exact (route x hx sx).trans ((route y hy sy).reverse symm)
  · have rev : (bad B erased).length + (bad A erased).length ≤ 2 := by omega
    have route := span B A rev (by omega) Edge.right Edge.left Edge.back i bi ai
    exact (route x hx.symm sx).trans ((route y hy.symm sy).reverse symm)

open Construction Certificates

/-- Adjacency of the 22 triangles of the *closed* cap, read directly from its
face list. Vertex 16 represents the facet (w,b₀,b₁) to be removed. -/
def capRows : MapData where
  rows := (List.range closedCap.length).map fun i =>
    (List.range closedCap.length).filter fun j =>
      i != j && (triangleLabels closedCap[i]!).countP (fun a => contains closedCap[j]! a) == 2
  outer := []
  inner := []
where triangleLabels (t : Triangle) := [t.1,t.2.1,t.2.2]

private def capRings : List (List Nat) :=
  [[1, 2, 3, 4, 9, 15, 10, 5, 11, 6],
   [0, 4, 3, 2, 7, 12, 6, 11, 5],
   [0, 1, 6, 12, 7, 13, 8, 3, 4],
   [0, 1, 2, 7, 13, 8, 14, 9, 4],
   [0, 1, 2, 3, 8, 14, 9, 15, 10, 5],
   [0, 1, 6, 11, 17, 16, 10, 15, 9, 4],
   [0, 1, 2, 7, 12, 18, 17, 11, 5],
   [1, 2, 3, 8, 13, 19, 18, 12, 6],
   [2, 3, 4, 9, 14, 20, 19, 13, 7],
   [0, 4, 3, 8, 14, 20, 21, 15, 10, 5],
   [0, 4, 9, 15, 21, 16, 17, 11, 5],
   [0, 1, 6, 12, 18, 17, 16, 10, 5],
   [1, 2, 7, 13, 19, 18, 17, 11, 6],
   [2, 3, 8, 14, 20, 19, 18, 12, 7],
   [3, 8, 13, 19, 20, 21, 15, 9, 4],
   [0, 4, 9, 14, 20, 21, 16, 10, 5],
   [5, 10, 15, 21, 20, 19, 18, 17, 11],
   [5, 10, 16, 21, 20, 19, 18, 12, 6, 11],
   [6, 11, 17, 16, 21, 20, 19, 13, 7, 12],
   [7, 12, 18, 17, 16, 21, 20, 14, 8, 13],
   [8, 13, 19, 18, 17, 16, 21, 15, 9, 14],
   [9, 14, 20, 19, 18, 17, 16, 10, 15]]

private theorem capRowsValid : capRows.rotationOK := by decide
private theorem capOrder : capRows.ord = 22 := rfl

theorem capBounds (h : capRows.adj x y) : x < 22 ∧ y < 22 := by
  have rowBound {x y} (m : capRows.adj x y) : x < capRows.ord := by
    by_cases b : x < capRows.rows.length
    · exact b
    · simp [MapData.adj,List.getElem?_eq_none (l:=capRows.rows) (i:=x) (by omega)] at m
  exact ⟨rowBound h,rowBound (adj_symmetric capRowsValid _ _ h)⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem capGraphConnected : capRows.ThreeConnected := by
  have det : detoursOK capRows (detours capRows capRings) := by decide
  have sym := adj_symmetric capRowsValid
  apply robust_of_detours _ _ det (by decide) sym
  have base (x : Nat) (hx : x < capRows.ord) : PathAvoiding capRows.adj [] 0 x := by
    induction x using Nat.strongRecOn with
    | ind x ih =>
      have d : descending capRows := by decide
      rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp d x (List.mem_range.mpr hx)) with e|h
      · have := beq_iff_eq.mp e; subst x; exact .here (by simp)
      · obtain ⟨y,hy,hlt⟩ := List.any_eq_true.mp h
        have lt := of_decide_eq_true hlt
        exact (ih y lt (by omega)).step (sym _ _ hy) (by simp)
  exact fun x y hx hy => ((base x hx).reverse sym).trans (base y hy)

private def capPort (flip : Bool) (i : Fin 3) : Nat :=
  if i.val = 0 then (if flip then 17 else 21)
  else if i.val = 1 then (if flip then 21 else 17) else 10

/-- The two seam orientations exchange the two pole edges. -/
def capArm (flip : Bool) : Arm where
  vertex x := x < 22
  edge := capRows.adj
  endpoints := fun e => capBounds e
  symm := fun {x y} => adj_symmetric capRowsValid x y
  cut := 16
  cutValid := by decide
  port := capPort flip
  portsValid := by cases flip <;> decide
  portsDifferent := by change ∀ i j, capPort flip i = capPort flip j → i=j; cases flip <;> decide
  neighbors := by
    intro x
    change capRows.adj x 16 ↔ ∃ i, capPort flip i=x
    rw [show capRows.adj x 16 ↔ capRows.adj 16 x from
      ⟨adj_symmetric capRowsValid _ _,adj_symmetric capRowsValid _ _⟩]
    change x ∈ [10,17,21] ↔ _
    have facts (f : Bool) : capPort f 0 = (if f then 17 else 21) ∧
        capPort f 1 = (if f then 21 else 17) ∧ capPort f 2 = 10 := by cases f <;> decide
    have mem (f : Bool) : ∀ i : Fin 3, capPort f i ∈ [10,17,21] := by cases f <;> decide
    constructor
    · intro h
      have ⟨a,b,c⟩ := facts flip
      cases flip <;> simp at a b h <;> rcases h with rfl|rfl|rfl <;> first | exact ⟨0,a⟩ | exact ⟨1,b⟩ | exact ⟨2,c⟩
    · rintro ⟨i,rfl⟩; exact mem _ _
  conn := capGraphConnected.2

private def tetra (m : Nat) : Arm where
  vertex x := m ≤ x ∧ x < m+4
  edge x y := (m ≤ x ∧ x < m+4) ∧ (m ≤ y ∧ y < m+4) ∧ x ≠ y
  endpoints := fun e => ⟨e.1,e.2.1⟩
  symm := fun e => ⟨e.2.1,e.1,e.2.2.symm⟩
  cut := m
  cutValid := by omega
  port i := m+1+i.val
  portsValid := by intro i; have := i.isLt; omega
  portsDifferent := by intro i j eq; change m+1+i.val=m+1+j.val at eq; apply Fin.ext; omega
  neighbors := by
    intro x; constructor
    · rintro ⟨⟨lo,hi⟩,_,ne⟩; exact ⟨⟨x-(m+1),by omega⟩,by simp; omega⟩
    · rintro ⟨i,rfl⟩; have := i.isLt; omega
  conn := by
    intro gone _ x y hx hy sx sy
    by_cases e : x=y
    · subst y; exact .here sx
    · exact (PathAvoiding.here sx).step ⟨hx,hy,e⟩ sy

private def newPort (A : Arm) (m : Nat) (i : Fin 3) :=
  if i.val=0 then m+2 else if i.val=1 then A.port 0 else m+3

/-- In the next tetrahedron local vertices m, m+1, m+2, m+3 correspond
respectively to the incoming facet, outgoing facet, outer cone facet and
strip facet. Ports are ordered by the two pole edges and the opposite edge. -/
private def extend (A : Arm) (m : Nat) (bound : ∀ v, A.vertex v → v<m) : Arm where
  vertex := keepVertex A (tetra m)
  edge := Edge A (tetra m)
  endpoints := by
    intro x y e
    cases e with
    | left hx hy _ => exact ⟨.inl hx,.inl hy⟩
    | right hx hy _ => exact ⟨.inr hx,.inr hy⟩
    | bridge i => exact ⟨.inl (A.portsValid _),.inr ((tetra m).portsValid _)⟩
    | back i => exact ⟨.inr ((tetra m).portsValid _),.inl (A.portsValid _)⟩
  symm := fun {x y} => symm x y
  cut := m+1
  cutValid := Or.inr (show (m ≤ m+1 ∧ m+1<m+4) ∧ m+1 ≠ m by omega)
  port := newPort A m
  portsValid := by
    intro i
    have a := bound _ (A.portsValid 0).1
    simp only [newPort]
    split
    · exact ⟨Or.inr (show (m≤m+2 ∧ m+2<m+4) ∧ m+2 ≠ m by omega),by omega⟩
    split
    · exact ⟨Or.inl (A.portsValid 0),by omega⟩
    · exact ⟨Or.inr (show (m≤m+3 ∧ m+3<m+4) ∧ m+3 ≠ m by omega),by omega⟩
  portsDifferent := by
    intro i j eq
    have := bound _ (A.portsValid 0).1
    apply Fin.ext
    unfold newPort at eq
    repeat' first | omega | split at eq
  neighbors := by
    intro x
    constructor
    · intro edge
      generalize save : m+1=y at edge
      cases edge with
      | left _ hy _ => have := bound _ hy.1; omega
      | right hx _ e =>
        change (m≤x ∧ x<m+4) ∧ _ ∧ x≠_ at e
        change _ ∧ x≠m at hx
        by_cases is2 : x=m+2
        · exact ⟨0,show m+2=x by omega⟩
        · exact ⟨2,show m+3=x by omega⟩
      | bridge i =>
        change m+1 = m+1+i.val at save
        have iz : i=0 := Fin.ext (show i.val=0 by omega)
        subst i; exact ⟨1,rfl⟩
      | back i =>
        have := bound _ (A.portsValid i).1
        omega
    · rintro ⟨i,rfl⟩
      by_cases zero : i.val=0
      · rw [show newPort A m i=m+2 by simp [newPort,zero]]
        apply Edge.right <;> simp [Arm.stays,tetra] <;> omega
      by_cases one : i.val=1
      · rw [show newPort A m i=A.port 0 by simp [newPort,one]]
        exact Edge.bridge 0
      · rw [show newPort A m i=m+3 by simp [newPort,zero,one]]
        apply Edge.right <;> simp [Arm.stays,tetra] <;> omega
  conn := by
    intro erased len x y hx hy sx sy
    apply vertexSumConnected A (tetra m) _ erased len hx hy sx sy
    intro z hz other
    have := bound _ hz
    exact (Nat.not_le_of_lt this) other.1

private def lowerNames (offset : Nat) (erased : List Nat) :=
  (erased.filter (fun x => decide (offset≤x))).map (fun x => x-offset)

private theorem lower_mem (m x : Nat) (erased : List Nat) :
    x ∈ lowerNames m erased ↔ m+x ∈ erased := by
  simp only [lowerNames,List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨y,⟨mem,ge⟩,eq⟩; exact (show y=m+x by omega) ▸ mem
  · intro mem; exact ⟨m+x,⟨mem,by omega⟩,by omega⟩

private def translate (A : Arm) (m : Nat) : Arm where
  vertex x := m≤x ∧ A.vertex (x-m)
  edge x y := m≤x ∧ m≤y ∧ A.edge (x-m) (y-m)
  endpoints := fun e => ⟨⟨e.1,(A.endpoints e.2.2).1⟩,⟨e.2.1,(A.endpoints e.2.2).2⟩⟩
  symm := fun e => ⟨e.2.1,e.1,A.symm e.2.2⟩
  cut := m+A.cut
  cutValid := by simp [A.cutValid]
  port i := m+A.port i
  portsValid := by intro i; simp [(A.portsValid i).1,(A.portsValid i).2]
  portsDifferent := by intro i j h; exact A.portsDifferent (Nat.add_left_cancel h)
  neighbors := by
    intro x
    simp only [Nat.le_add_right,true_and,Nat.add_sub_cancel_left,A.neighbors]
    constructor
    · rintro ⟨hx,i,hi⟩; exact ⟨i,by omega⟩
    · rintro ⟨i,rfl⟩; exact ⟨by omega,i,by omega⟩
  conn := by
    intro erased len x y hx hy sx sy
    have ll : (lowerNames m erased).length ≤ 2 :=
      Nat.le_trans (by simpa [lowerNames] using List.length_filter_le (fun x => decide (m≤x)) erased) len
    have xeq : m+(x-m)=x := by omega
    have yeq : m+(y-m)=y := by omega
    have orig := A.conn _ ll _ _ hx.2 hy.2 (fun e => sx (xeq ▸ (lower_mem ..).mp e))
      (fun e => sy (yeq ▸ (lower_mem ..).mp e))
    let next := fun a b => m≤a ∧ m≤b ∧ A.edge (a-m) (b-m)
    have lift {a b} (p : PathAvoiding A.edge (lowerNames m erased) a b) :
        PathAvoiding next erased (m+a) (m+b) := by
      induction p with
      | here ok => exact .here (fun h => ok ((lower_mem ..).mpr h))
      | @step a b p e ok ih =>
        apply ih.step (show next (m+a) (m+b) by simp [next,e])
        exact fun h => ok ((lower_mem ..).mpr h)
    exact xeq ▸ yeq ▸ lift orig

/-- One initial closed cap followed by k tetrahedral vertex sums.
The bound leaves a fresh interval of four names for the next tetrahedron. -/
private def growing : (k : Nat) → { A : Arm // ∀ v, A.vertex v → v < 22+4*k }
  | 0 => ⟨capArm false,fun _ hx => hx⟩
  | k+1 =>
    let ⟨A,ha⟩ := growing k
    ⟨extend A (22+4*k) ha,by
      intro v hv
      rcases hv with h|h
      · have := ha v h.1; omega
      · have t := h.1.2; omega⟩

def leftArm (n : Nat) := (growing (n+2)).val
def rightArm (n : Nat) := translate (capArm true) (22+4*(n+2))

/-- Vertex names and edges for the primal formed by the two caps and n+2
tetrahedra. Each matched port pair is an edge of the vertex sum. -/
def primalVertex (n : Nat) := keepVertex (leftArm n) (rightArm n)
def primalEdge (n : Nat) := Edge (leftArm n) (rightArm n)

theorem primalConnected (n : Nat) (erased : List Nat) (len : erased.length ≤ 2)
    {x y : Nat} (hx : primalVertex n x) (hy : primalVertex n y)
    (sx : x ∉ erased) (sy : y ∉ erased) : PathAvoiding (primalEdge n) erased x y := by
  apply vertexSumConnected (leftArm n) (rightArm n) _ erased len hx hy sx sy
  intro v lv rv
  exact Nat.not_le_of_lt ((growing (n+2)).property v lv) rv.1

structure VertexList (V : Nat → Prop) where
  names : List Nat
  distinct : names.Nodup
  mem : ∀ x, x ∈ names ↔ V x

private def unionList (A B : Arm) (d : ∀ x, A.vertex x → ¬B.vertex x)
    (a : VertexList A.vertex) (b : VertexList B.vertex) : VertexList (keepVertex A B) where
  names := a.names.erase A.cut ++ b.names.erase B.cut
  distinct := List.nodup_append.mpr ⟨a.distinct.erase _,b.distinct.erase _,by
    rintro x hx y hy rfl
    exact d x ((a.mem _).mp (List.erase_subset hx)) ((b.mem _).mp (List.erase_subset hy))⟩
  mem x := by
    simp [List.mem_append,a.distinct.mem_erase_iff,b.distinct.mem_erase_iff,a.mem,b.mem,keepVertex,Arm.stays,and_comm]

private theorem lengthUnion (A B : Arm) (d) (a : VertexList A.vertex) (b : VertexList B.vertex) :
    (unionList A B d a b).names.length = a.names.length-1+(b.names.length-1) := by
  simp [unionList,List.length_erase_of_mem ((a.mem _).mpr A.cutValid),
    List.length_erase_of_mem ((b.mem _).mpr B.cutValid)]

private def tetraList (m : Nat) : VertexList (tetra m).vertex where
  names := [m,m+1,m+2,m+3]
  distinct := by simp
  mem x := by change _ ↔ m≤x ∧ x<m+4; simp; omega

private def capList (flip : Bool) : VertexList (capArm flip).vertex where
  names := List.range 22
  distinct := List.nodup_range
  mem _ := List.mem_range

private def growList : (k : Nat) → {r : VertexList (growing k).val.vertex // r.names.length=22+2*k}
  | 0 => ⟨capList false,rfl⟩
  | k+1 =>
    let A := (growing k).val
    let m := 22+4*k
    let d : ∀ x, A.vertex x → ¬(tetra m).vertex x := fun x hx h =>
      (Nat.not_le_of_lt ((growing k).property x hx)) h.1
    let old := growList k
    ⟨unionList A (tetra m) d old.val (tetraList m),by
      rw [lengthUnion,old.property]
      change 22+2*k-1+(4-1)=22+2*(k+1)
      omega⟩

private def finalCapList (n : Nat) : VertexList (rightArm n).vertex where
  names := (List.range 22).map (22+4*(n+2)+·)
  distinct := List.pairwise_map.mpr (List.nodup_range.imp (fun h eq => h (Nat.add_left_cancel eq)))
  mem x := by
    change _ ↔ 22+4*(n+2) ≤ x ∧ x-(22+4*(n+2))<22
    simp only [List.mem_map,List.mem_range]
    constructor
    · rintro ⟨i,hi,eq⟩; omega
    · rintro ⟨lo,hi⟩; exact ⟨_,hi,by omega⟩

def primalVertices (n : Nat) : VertexList (primalVertex n) :=
  unionList (leftArm n) (rightArm n) (fun x hx h => Nat.not_le_of_lt ((growing (n+2)).property x hx) h.1)
    (growList (n+2)).val (finalCapList n)

theorem primalOrder (n : Nat) : (primalVertices n).names.length = 2*(n+12)+22 := by
  unfold primalVertices
  rw [lengthUnion (leftArm n) (rightArm n) _ (growList (n+2)).val (finalCapList n),(growList (n+2)).property]
  simp only [finalCapList,List.length_map,List.length_range]
  omega

def Cubic (V : Nat → Prop) (E : Nat → Nat → Prop) := ∀ v, V v →
  ∃ f : Fin 3 → Nat, Function.Injective f ∧ ∀ x, E x v ↔ ∃ i, f i=x

private theorem transpose (e : Edge A B x y) : Edge B A x y := by
  cases e with
  | left u v h => exact .right u v h
  | right u v h => exact .left u v h
  | bridge i => exact .back i
  | back i => exact .bridge i

private theorem cubicLeft (A B : Arm) (disjoint : ∀ x, A.vertex x → ¬B.vertex x)
    (ca : Cubic A.vertex A.edge) (v : Nat) (hv : A.stays v) :
    ∃ f : Fin 3 → Nat, Function.Injective f ∧ ∀ x, Edge A B x v ↔ ∃ i, f i=x := by
  classical
  obtain ⟨p,idx⟩ : ∃ p : Fin 3, ∀ j, A.port j=v → j=p := by
    by_cases h : ∃ j, A.port j=v
    · obtain ⟨p,hp⟩ := h; exact ⟨p,fun j hj => A.portsDifferent (hj.trans hp.symm)⟩
    · exact ⟨0,fun j hj => (h ⟨j,hj⟩).elim⟩
  let repl (x : Nat) := if x=A.cut then B.port p else x
  have outside (u : Nat) (hu : A.vertex u) : u ≠ B.port p :=
    fun eq => disjoint _ (eq ▸ hu) (B.portsValid p).1
  have nbors (x : Nat) : Edge A B x v ↔ ∃ z, A.edge z v ∧ repl z=x := by
    constructor
    · intro e
      cases e with
      | left hx _ ee => exact ⟨_,ee,by simp [repl,hx.2]⟩
      | right _ h _ => exact (disjoint _ hv.1 h.1).elim
      | bridge j => exact (disjoint _ hv.1 (B.portsValid j).1).elim
      | back j =>
        have he := idx j rfl
        exact ⟨A.cut,A.symm ((A.neighbors _).mpr ⟨j,rfl⟩),by simp [repl,he]⟩
    · rintro ⟨z,ee,rfl⟩
      by_cases h : z=A.cut
      · subst z
        obtain ⟨j,hh⟩ := (A.neighbors v).mp (A.symm ee)
        have jp := idx j hh
        subst j
        simpa [repl,hh] using (Edge.back (A:=A) (B:=B) p)
      · simpa [repl,h] using (Edge.left (B:=B) ⟨(A.endpoints ee).1,h⟩ hv ee)
  obtain ⟨f,inj,neigh⟩ := ca v hv.1
  have inA (i : Fin 3) : A.vertex (f i) := (A.endpoints ((neigh _).mpr ⟨i,rfl⟩)).1
  refine ⟨fun i => repl (f i),?_,?_⟩
  · intro i j eq
    apply inj
    have hi := outside _ (inA i)
    have hj := outside _ (inA j)
    change repl (f i) = repl (f j) at eq
    simp only [repl] at eq; split at eq <;> split at eq <;> grind
  · intro x
    rw [nbors]
    constructor
    · rintro ⟨z,ee,eq⟩; obtain ⟨i,rfl⟩ := (neigh z).mp ee; exact ⟨i,eq⟩
    · rintro ⟨i,rfl⟩; exact ⟨_,(neigh _).mpr ⟨i,rfl⟩,rfl⟩

theorem vertexSumCubic (A B : Arm) (disjoint : ∀ x, A.vertex x → ¬ B.vertex x)
    (ca : Cubic A.vertex A.edge) (cb : Cubic B.vertex B.edge) : Cubic (keepVertex A B) (Edge A B) := by
  intro v hv
  obtain h|h := hv
  · exact cubicLeft A B disjoint ca v h
  · obtain ⟨f,inj,eq⟩ := cubicLeft B A (fun x hb ha => disjoint x ha hb) cb v h
    exact ⟨f,inj,fun x => (show Edge A B x v ↔ Edge B A x v from ⟨transpose,transpose⟩).trans (eq _)⟩

private theorem capCubic (flip : Bool) : Cubic (capArm flip).vertex (capArm flip).edge := by
  have table : ∀ v : Fin 22, let row := capRows.rows[v.val]?.getD []
                             row.length=3 ∧ row.Nodup := by decide
  intro v hv
  let row := capRows.rows[v]?.getD []
  have ⟨three,nd⟩ := table ⟨v,hv⟩
  change row.length = 3 at three
  change row.Nodup at nd
  let f (i : Fin 3) := row[i.val]'(by omega)
  refine ⟨f,fun i j eq => Fin.ext (nd.getElem_inj.mp eq),?_⟩
  intro x
  change capRows.adj x v ↔ _
  rw [show capRows.adj x v ↔ capRows.adj v x from
    ⟨adj_symmetric capRowsValid _ _,adj_symmetric capRowsValid _ _⟩]
  change x ∈ row ↔ _
  constructor
  · intro h; obtain ⟨j,hj,eq⟩ := List.mem_iff_getElem.mp h; exact ⟨⟨j,by omega⟩,eq⟩
  · rintro ⟨i,rfl⟩; exact List.getElem_mem _

private theorem tetraCubic (m : Nat) : Cubic (tetra m).vertex (tetra m).edge := by
  intro v hv
  change m≤v ∧ v<m+4 at hv
  let f (i : Fin 3) := if m+i.val < v then m+i.val else m+i.val+1
  refine ⟨f,?_,?_⟩
  · intro i j eq; apply Fin.ext; simp only [f] at eq; split at eq <;> split at eq <;> omega
  · intro x
    change (m≤x ∧ x<m+4) ∧ (m≤v ∧ v<m+4) ∧ x≠v ↔ _
    constructor
    · intro h
      by_cases less : x<v
      · exact ⟨⟨x-m,by omega⟩,by simp [f]; split <;> omega⟩
      · exact ⟨⟨x-m-1,by omega⟩,by simp [f]; split <;> omega⟩
    · rintro ⟨i,rfl⟩; have := i.isLt; dsimp [f]; split <;> omega

private theorem growCubic (k : Nat) : Cubic (growing k).val.vertex (growing k).val.edge := by
  induction k with
  | zero => exact capCubic false
  | succ k ih =>
    exact vertexSumCubic _ (tetra (22+4*k))
      (fun x hx h => Nat.not_le_of_lt ((growing k).property x hx) h.1) ih (tetraCubic _)

private theorem shiftCubic (A : Arm) (m : Nat) (ca : Cubic A.vertex A.edge) :
    Cubic (translate A m).vertex (translate A m).edge := by
  intro v hv
  obtain ⟨f,inj,neigh⟩ := ca (v-m) hv.2
  refine ⟨fun i => m+f i,fun _ _ h => inj (Nat.add_left_cancel h),?_⟩
  intro x
  change (m≤x ∧ m≤v ∧ A.edge (x-m) (v-m)) ↔ ∃ i, m+f i=x
  constructor
  · rintro ⟨ge,_,edge⟩; obtain ⟨i,eq⟩ := (neigh _).mp edge; exact ⟨i,by omega⟩
  · rintro ⟨i,rfl⟩; exact ⟨by omega,hv.1,(neigh _).mpr ⟨i,by omega⟩⟩

theorem primalCubic (n : Nat) : Cubic (primalVertex n) (primalEdge n) :=
  vertexSumCubic _ _ (fun x hx h => Nat.not_le_of_lt ((growing (n+2)).property x hx) h.1)
    (growCubic (n+2)) (shiftCubic (capArm true) (22+4*(n+2)) (capCubic true))

def partialArm (k : Nat) := (growing k).val

theorem partialBound (k v : Nat) (h : (partialArm k).vertex v) : v < 22+4*k :=
  (growing k).property v h

def Arm.interiorEdge (A : Arm) (u v : Nat) := A.edge u v ∧ u≠A.cut ∧ v≠A.cut

theorem Arm.edgeBound (A : Arm) (h : A.interiorEdge u v) : A.stays u ∧ A.stays v :=
  ⟨⟨(A.endpoints h.1).1,h.2.1⟩,⟨(A.endpoints h.1).2,h.2.2⟩⟩

theorem Arm.interiorSymm (A : Arm) (h : A.interiorEdge u v) : A.interiorEdge v u :=
  ⟨A.symm h.1,h.2.2,h.2.1⟩

theorem portAdvance (k : Nat) :
    (partialArm (k+1)).port 0 = 22+4*k+2 ∧
    (partialArm (k+1)).port 1 = (partialArm k).port 0 ∧
    (partialArm (k+1)).port 2 = 22+4*k+3 := ⟨rfl,rfl,rfl⟩

/-- The open patch before coning the outgoing slot gains only a path of
three edges between the two disappearing ports, through the new P and S. -/
theorem partialAdvance (k u v : Nat) :
    let A := partialArm k
    let m := 22+4*k
    (partialArm (k+1)).interiorEdge u v ↔ A.interiorEdge u v ∨
      (u,v) ∈ [(A.port 1,m+2),(m+2,A.port 1),(A.port 2,m+3),
        (m+3,A.port 2),(m+2,m+3),(m+3,m+2)] := by
  dsimp only
  let A := partialArm k
  let m := 22+4*k
  change (Edge A (tetra m) u v ∧ u≠m+1 ∧ v≠m+1) ↔ A.interiorEdge u v ∨
    (u,v) ∈ [(A.port 1,m+2),(m+2,A.port 1),(A.port 2,m+3),(m+3,A.port 2),(m+2,m+3),(m+3,m+2)]
  have bound (x) := partialBound k x
  change ∀ x, A.vertex x → x<m at bound
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq]
  constructor
  · rintro ⟨e,hu,hv⟩
    cases e with
    | left ha hb e => exact Or.inl ⟨e,ha.2,hb.2⟩
    | right hx hy e =>
      right
      change (m≤_ ∧ _<m+4) ∧ _≠m at hx
      change (m≤_ ∧ _<m+4) ∧ _≠m at hy
      have ne := e.2.2
      omega
    | bridge i =>
      change m+1+i.val ≠ m+1 at hv
      have oneOr : i=1 ∨ i=2 := by
        have lim := i.isLt
        by_cases i.val=1
        · exact Or.inl (Fin.ext (by omega))
        · exact Or.inr (Fin.ext (by omega))
      obtain rfl|rfl := oneOr <;> simp [tetra]
    | back i =>
      change m+1+i.val ≠ m+1 at hu
      have oneOr : i=1 ∨ i=2 := by
        have lim := i.isLt
        by_cases i.val=1
        · exact Or.inl (Fin.ext (by omega))
        · exact Or.inr (Fin.ext (by omega))
      obtain rfl|rfl := oneOr <;> simp [tetra]
  · rintro (old|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · have ⟨ha,hb⟩ := A.edgeBound old
      have l := bound _ ha.1
      have r := bound _ hb.1
      exact ⟨.left ha hb old.1,by omega,by omega⟩
    · exact ⟨Edge.bridge 1,by have := bound _ (A.portsValid 1).1; omega,by omega⟩
    · exact ⟨Edge.back 1,by omega,by have := bound _ (A.portsValid 1).1; omega⟩
    · exact ⟨Edge.bridge 2,by have := bound _ (A.portsValid 2).1; omega,by omega⟩
    · exact ⟨Edge.back 2,by omega,by have := bound _ (A.portsValid 2).1; omega⟩
    all_goals refine ⟨.right ?_ ?_ ?_,by omega,by omega⟩ <;> simp [Arm.stays,tetra] <;> omega

theorem partialBase (u v : Nat) :
    (partialArm 0).interiorEdge u v ↔ (capRows.adj u v ∧ u≠16 ∧ v≠16) := Iff.rfl

theorem rightEdge (n u v : Nat) :
    (rightArm n).interiorEdge u v ↔
    let m := 22+4*(n+2)
    m ≤ u ∧ m ≤ v ∧ capRows.adj (u-m) (v-m) ∧ u ≠ m+16 ∧ v ≠ m+16 := by
  simp only [Arm.interiorEdge,rightArm,translate,capArm,and_assoc]

theorem finalEdges (n u v : Nat) :
    primalEdge n u v ↔ (leftArm n).interiorEdge u v ∨ (rightArm n).interiorEdge u v ∨
    (∃ i, u=(leftArm n).port i ∧ v=(rightArm n).port i) ∨
    (∃ i, u=(rightArm n).port i ∧ v=(leftArm n).port i) := by
  constructor
  · intro e; cases e with
    | left a b e => exact Or.inl ⟨e,a.2,b.2⟩
    | right a b e => exact Or.inr (Or.inl ⟨e,a.2,b.2⟩)
    | bridge i => exact Or.inr (Or.inr (Or.inl ⟨i,rfl,rfl⟩))
    | back i => exact Or.inr (Or.inr (Or.inr ⟨i,rfl,rfl⟩))
  · rintro (ea|eb|⟨i,rfl,rfl⟩|⟨i,rfl,rfl⟩)
    · exact .left ((leftArm _).edgeBound ea).1 ((leftArm _).edgeBound ea).2 ea.1
    · exact .right ((rightArm _).edgeBound eb).1 ((rightArm _).edgeBound eb).2 eb.1
    · exact .bridge i
    · exact .back i

end DiskFullerene.PrimalSplice
