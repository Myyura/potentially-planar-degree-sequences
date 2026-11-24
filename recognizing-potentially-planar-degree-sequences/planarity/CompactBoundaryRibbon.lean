import CompactBoundary
import RibbonCode

/-! A connected planar rotation system produces the two compact words.
The tree walk marks a tree band twice, or emits a placeholder. Each
placeholder consumes one parenthesis for the matching of non-tree darts. -/
namespace Recognition.CompactBoundary
open Equiv Equiv.Perm LeanPool.K5MinorFreeChoosability PlanarDegrees.MapCode

def tourTag (i t : Nat) : Tag :=
  if i=t then (false,false) else if i<t then (false,true) else (true,false)

def extra (i t c : Nat) : List Bool := if i=t then [decide (i<c)] else []

def expandTour : List Tag → List Bool → Option (List Bool × List Bool)
  | [],[] => some ([],[])
  | (false,false)::xs,b::bs => (expandTour xs bs).map fun (t,c) => (true::false::t,b::b::c)
  | (false,true)::xs,bs => (expandTour xs bs).map fun (t,c) => (true::true::t,true::false::c)
  | (true,false)::xs,bs => (expandTour xs bs).map fun (t,c) => (false::false::t,true::false::c)
  | _,_ => none

private theorem expand_correct {n} (T C : Perm (Fin n))
    (opposite : ∀ i, T i=i ↔ C i≠i) (xs : List (Fin n)) :
    expandTour (xs.map (fun (i : Fin n) => tourTag i (T i))) (xs.flatMap (fun (i : Fin n) => extra i (T i) (C i))) =
    some (xs.flatMap (fun i => [decide (i≤T i),decide (i<T i)]),
      xs.flatMap (fun i => [decide (i≤C i),decide (i<C i)])) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    by_cases tree : T i=i
    · have n := (opposite i).mp tree
      have ne : i.val≠(C i).val := fun h => n (Fin.ext h.symm)
      have mono : decide (i≤C i)=decide (i<C i) := by
        have pos : (i≤C i ↔ i<C i) := by change (i.val≤(C i).val ↔ i.val<(C i).val); omega
        simp [pos]
      simp [tourTag,extra,tree,expandTour,mono]; exact ih
    · have other := of_not_not ((opposite i).not.mp tree)
      have ne : i.val≠(T i).val := fun h => tree (Fin.ext h.symm)
      by_cases lt : i.val < (T i).val
      · have le : i≤T i := lt.le
        have strict : i<T i := lt
        simp [tourTag,extra,ne,le,strict,expandTour,other]; exact ih
      · have notle : ¬i≤T i := by omega
        have nlt : ¬i<T i := lt
        simp [tourTag,extra,ne,nlt,notle,expandTour,other]; exact ih

/-- Reconstruct permutation rows from the two words. The remaining payload
is returned exactly, so this decoder can precede marks and counters. -/
def readTour (src : List Bool) : Option (RibbonCode.Rows × List Bool) := do
  let (word,more) ← readField 2 src
  let (other,tail) ← readField 1 more
  let (ts,[]) ← readTags (word.length/2) word | none
  let (t,c) ← expandTour ts other
  let tp ← decodeChords t
  let cp ← decodeChords c
  return (⟨ts.length,tp,cp⟩,tail)

def tourWords (ts : List Tag) (other : List Bool) :=
  field ts.length (tagBits ts) ++ field other.length other

private theorem read_words {n : Nat} (T C : Perm (Fin n))
    (dis : ∀ x,T x=x ↔ C x≠x) (ps qs)
    (p : decodeChords (RibbonCode.pairedBits T)=some ps)
    (q : decodeChords (RibbonCode.pairedBits C)=some qs) (tail : List Bool) :
    let xs := List.finRange n
    let a := xs.map (fun (i : Fin n) => tourTag i (T i))
    let b := xs.flatMap (fun (i : Fin n) => extra i (T i) (C i))
    readTour (tourWords a b++tail)=some (⟨n,ps,qs⟩,tail) := by
  dsimp only
  let ts := (List.finRange n).map (fun (i : Fin n) => tourTag i (T i))
  let oth := (List.finRange n).flatMap (fun (i : Fin n) => extra i (T i) (C i))
  have tl : (tagBits ts).length=2*ts.length := by
    have h (zs : List Tag) : (tagBits zs).length=2*zs.length := by
      induction zs with | nil => rfl | cons a zs ih => simp_all [tagBits]; omega
    exact h ts
  have rt : readTags ts.length (tagBits ts)=some (ts,[]) := by simpa using read_tags ts []
  have ex := expand_correct T C dis (List.finRange n)
  change expandTour ts oth=some (RibbonCode.pairedBits T,RibbonCode.pairedBits C) at ex
  change readTour (tourWords ts oth++tail)=_
  have d : (tagBits ts).length/2=ts.length := by omega
  have size : ts.length=n := by simp [ts]
  simp [readTour,tourWords,List.append_assoc,read_field 2 ts.length (tagBits ts) (field oth.length oth++tail) tl,
    read_field 1 oth.length oth tail (by simp),d,rt,ex,p,q]
  exact size

private theorem extra_len {n} (T C : Perm (Fin n)) (xs : List (Fin n)) :
    (xs.flatMap (fun (i : Fin n) => extra i (T i) (C i))).length≤xs.length := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    have ne : (extra i (T i) (C i)).length≤1 := by unfold extra; split <;> simp
    simp only [List.flatMap_cons,List.length_append,List.length_cons]; omega

/-- For any connected sphere rotation system without fixed darts, both
the rotation and pairing of every dart are recovered in a common order.
There is one two-bit tour symbol per dart and at most one matching bit per dart. -/
theorem plane_tour {n : Nat} (σ α : Perm (Fin n)) (undo : ∀ x,α (α x)=x)
    (nofix : ∀ x,α x≠x) (flat : eulerDefect σ α=0) (joint : ∀ a b,compSetoid σ α a b) :
    ∃ ts : List Tag, ∃ other : List Bool, ∃ R : RibbonCode.Rows, ∃ e : Perm (Fin n),
      ts.length=n ∧ other.length≤n ∧ R.length=n ∧
      (∀ tail,readTour (tourWords ts other++tail)=some (R,tail)) ∧
      (∀ x : Fin n,R.rotation x.val=some ((e.permCongr σ) x).val) ∧
      ∀ x : Fin n,R.pairing x.val=some ((e.permCongr α) x).val := by
  obtain ⟨θ,T,C,H,one,genus⟩ := TreeBands.decompose σ α undo flat joint
  obtain ⟨e,turn⟩ := RibbonCode.cyclic θ one
  let A := e.permCongr T
  let B := e.permCongr C
  have opp (i : Fin n) : A i=i ↔ B i≠i := by
    have either : A i=i ∨ B i=i := by
      rcases H.disjoint (e.symm i) with h|h
      · exact .inl (by simp [A,h])
      · exact .inr (by simp [B,h])
    have move : (e.permCongr α) i≠i := by
      intro eq
      apply nofix (e.symm i)
      simpa [permCongr_apply] using congrArg e.symm eq
    have neq : ¬(A i=i ∧ B i=i) := by
      intro ⟨ha,hb⟩
      apply move
      rw [←H.pairing,permCongr_mul,Perm.mul_apply]
      change A (B i)=i; rw [hb,ha]
    tauto
  have band (X : Perm (Fin n)) (u : ∀ i,X (X i)=i) (g : eulerDefect θ X=0) :=
    RibbonCode.paired_band (e.permCongr X) (by intro x; simp [u])
      (by rw [←turn,eulerDefect_permCongr,g])
  obtain ⟨ps,rd,act⟩ := band T H.treeUndo genus
  obtain ⟨qs,rc,bct⟩ := band C H.cotreeUndo H.cotreeSphere
  let ts := (List.finRange n).map (fun (i : Fin n) => tourTag i (A i))
  let other := (List.finRange n).flatMap (fun (i : Fin n) => extra i (A i) (B i))
  let R : RibbonCode.Rows := ⟨n,ps,qs⟩
  refine ⟨ts,other,R,e,by simp [ts],(extra_len A B _).trans (by simp),rfl,
    read_words A B opp ps qs rd rc,?_,?_⟩
  · intro x
    change (do let y ← RibbonCode.bandAt ps x.val; return (y+1)%n)=_
    rw [act,←H.rotation,permCongr_mul,turn,Perm.mul_apply]
    change some (((e.permCongr T x).val+1)%n)=some ((finRotate n (e.permCongr T x)).val)
    cases n with
    | zero => exact Fin.elim0 x
    | succ n =>
      rw [coe_finRotate]
      split
      · next he => rw [he]; simp
      · next ne => simp only [Fin.ext_iff,Fin.val_last] at ne
                   have := (e.permCongr T x).isLt
                   rw [Nat.mod_eq_of_lt (by omega)]
  · intro x
    change (do let y ← RibbonCode.bandAt qs x.val; RibbonCode.bandAt ps y)=_
    rw [bct,←H.pairing,permCongr_mul,Perm.mul_apply]
    exact act _


/-- Count the distinct rotation cycles using only the recovered dart table. -/
def vertexCount (R : RibbonCode.Rows) (n : Nat) : Nat :=
  let xs := List.finRange n
  let next (d : Fin n) := (R.rotation d.val).bind fun i => if h : i<n then some (⟨i,h⟩ : Fin n) else none
  OrbitTable.count (OrbitTable.run xs (xs.map fun d => (d,(next d).getD d)))

private theorem vertex_count (R : RibbonCode.Rows) {n} (rot : Perm (Fin n))
    (read : ∀ i : Fin n,R.rotation i.val=some (rot i).val) : vertexCount R n=cycleCount rot := by
  unfold vertexCount
  simp only [read,Option.bind_some,Fin.is_lt,↓reduceDIte,Fin.eta,Option.getD_some]
  apply OrbitTable.count_correct List.mem_finRange _ (SameCycle.setoid rot)
  apply OrbitTable.generated _ List.mem_finRange
  · rintro z hz
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
    exact sameCycle_apply_right.mpr (SameCycle.refl _ _)
  · intro s h
    exact fun _ _ => sameCycle_of_step s (fun a => h (a,rot a) (List.mem_map.mpr ⟨a,List.mem_finRange _,rfl⟩))

structure PlaneDrawing where
  ribbon : RibbonCode.Rows
  vertexTags : List Tag
  edgeTags : List Tag
  redDegrees : List Nat

def readPlane : List Bool → Option (Option PlaneDrawing)
  | [false] => some none
  | true::bs => do
    let (R,tail) ← readTour bs
    let (vs,esTail) ← readTags (vertexCount R R.length) tail
    let (es,dsTail) ← readTags (R.length/2) esTail
    let (ds,rest) ← readCounts (vs.count original) dsTail
    if rest.isEmpty then return some ⟨R,vs,es,ds⟩ else none
  | _ => none

def planeFields (ts : List Tag) (other : List Bool) (vs es : List Tag) :=
  true::(tourWords ts other ++ (tagBits vs ++ tagBits es))

def packPlane (ts : List Tag) (other : List Bool) (vs es : List Tag) (ds : List Nat) :=
  planeFields ts other vs es ++ counts ds

private theorem tour_width (ts : List Tag) : (tagBits ts).length=2*ts.length := by
  induction ts with | nil => rfl | cons a ts ih => simp_all [tagBits]; omega

theorem plane_fields_width (ts : List Tag) (other : List Bool) (vs es : List Tag)
    (tour : ts.length=2*es.length) (matching : other.length≤ts.length) (vert : vs.length≤es.length+1) :
    (planeFields ts other vs es).length≤14*es.length+5 := by
  simp only [planeFields,tourWords,field,lengthTag,List.length_cons,List.length_append,
    List.length_replicate,List.length_nil,tour_width]; omega

private theorem read_plane {R : RibbonCode.Rows} {ts other vs es ds}
    (geometry : ∀ tail,readTour (tourWords ts other++tail)=some (R,tail))
    (vert : vs.length=vertexCount R R.length) (ed : es.length=R.length/2)
    (deg : ds.length=vs.count original) :
    readPlane (packPlane ts other vs es ds)=some (some ⟨R,vs,es,ds⟩) := by
  have rc : readCounts ds.length (counts ds)=some (ds,[]) := by simpa using read_counts ds []
  simp [packPlane,planeFields,List.append_assoc,readPlane,geometry,←vert,←ed,←deg,read_tags,rc]

/-- The two permutation rows, vertex marks, edge marks and red degrees in
the same record. Vertex and edge marks are listed in decoded order. -/
theorem plane_record {e n : Nat} (order : 0<n) (σ α : Perm (Fin (2*e)))
    (undo : ∀ x,α (α x)=x) (nofix : ∀ x,α x≠x)
    (flat : eulerDefect σ α=0) (joint : ∀ a b,compSetoid σ α a b)
    (vertices : cycleCount σ≤e+1) :
    ∃ ts : List Tag, ∃ other : List Bool, ∃ R : RibbonCode.Rows, ∃ rename : Perm (Fin (2*e)),
      R.length=2*e ∧ (∀ i : Fin (2*e),R.rotation i.val=some ((rename.permCongr σ) i).val) ∧
      (∀ i : Fin (2*e),R.pairing i.val=some ((rename.permCongr α) i).val) ∧
      ∀ (vs es : List Tag) (ds : List Nat),
        vs.length=cycleCount σ → es.length=e → ds.length=vs.count original →
        readPlane (packPlane ts other vs es ds)=some (some ⟨R,vs,es,ds⟩) ∧
        (planeFields ts other vs es).length≤14*e+5 ∧
        (e≤22*ds.length → (ds.map PlanarDegrees.Frontier.cost).sum^2≤220^2*n →
          (packPlane ts other vs es ds).length≤100000*ceilRoot n) := by
  obtain ⟨ts,bs,R,o,t,c,r,g,turn,mate⟩ := plane_tour σ α undo nofix flat joint
  have card := vertex_count R (o.permCongr σ) turn
  rw [cycleCount_permCongr] at card
  refine ⟨ts,bs,R,o,r,turn,mate,?_⟩
  intro vs es ds v E d
  have width := plane_fields_width ts bs vs es (by omega) (by omega) (by omega)
  rw [E] at width
  refine ⟨read_plane g (by rw [r,card,v]) (by omega) d,width,?_⟩
  intro small sumSq
  have active (xs : List Nat) : xs.length≤(xs.map PlanarDegrees.Frontier.cost).sum := by
    induction xs with
    | nil => rfl
    | cons p ps ih => have one : 1≤PlanarDegrees.Frontier.cost p := by simp [PlanarDegrees.Frontier.cost]
                      simp only [List.length_cons,List.map_cons,List.sum_cons]; omega
  have sq := (ceilRoot_le_iff n (ceilRoot n)).mp le_rfl
  have cap : (ds.map PlanarDegrees.Frontier.cost).sum≤220*ceilRoot n := by
    apply Nat.mul_self_le_mul_self_iff.mp
    nlinarith [Nat.mul_le_mul_left (220^2) sq]
  have pos : 0<ceilRoot n := by by_contra! h; have eq : ceilRoot n=0 := by omega
                                rw [eq] at sq; omega
  have length := counter_width ds
  have act := active ds
  simp only [packPlane,List.length_append]; omega

end Recognition.CompactBoundary
