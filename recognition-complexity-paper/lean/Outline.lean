import Frontier

/-! The weighted separator theorem is the sole ordering input. A recursion
produces a concrete permutation of the face list; vertices and face names are
kept distinct throughout this argument. -/
namespace Recognition.Outline
open PlanarDegrees.Frontier

abbrev Key := List Nat

def isAncestor : Key → Key → Prop
  | [], _ => True
  | _::_, [] => False
  | a::as,b::bs => a=b ∧ isAncestor as bs

private theorem reflP (p : Key) : isAncestor p p := by induction p <;> simp_all [isAncestor]
private theorem transP {p q r : Key} (h : isAncestor p q) (g : isAncestor q r) : isAncestor p r := by
  induction p generalizing q r with
  | nil => trivial
  | cons a as ih =>
    cases q with
    | nil => contradiction
    | cons b bs =>
      cases r with
      | nil => contradiction
      | cons c cs => exact ⟨h.1.trans g.1,ih h.2 g.2⟩

theorem isAncestor_le {p q : Key} (h : isAncestor p q) : p ≤ q := by
  induction p generalizing q with
  | nil => simp
  | cons a as ih =>
    cases q with
    | nil => contradiction
    | cons b bs => exact List.cons_le_cons_iff.mpr (Or.inr ⟨h.1,ih h.2⟩)

theorem convex {p a b c : Key} (ha : isAncestor p a) (hc : isAncestor p c)
    (ab : a ≤ b) (bc : b ≤ c) : isAncestor p b := by
  induction p generalizing a b c with
  | nil => trivial
  | cons x xs ih =>
    cases a with
    | nil => contradiction
    | cons i is =>
      cases c with
      | nil => contradiction
      | cons k ks =>
        cases b with
        | nil => simp at ab
        | cons j js =>
          have H := List.cons_le_cons_iff.mp ab
          have G := List.cons_le_cons_iff.mp bc
          have ⟨xi,pi⟩ := ha
          have ⟨xk,pk⟩ := hc
          have xj : x = j := by omega
          exact ⟨xj,ih pi pk (by grind) (by grind)⟩

def mass (f : Nat → Nat) (xs : List Nat) := (xs.map f).sum
def weight (c : Nat → Nat) (xs : List Nat) := mass (fun v => c v*c v) xs

def child (xs cut : List Nat) (region : Nat → Nat) (i : Nat) :=
  xs.filter (fun v => !(cut.contains v) && decide (region v=i))

private theorem child_mem {xs cut : List Nat} {region : Nat → Nat} {i v : Nat} :
    v ∈ child xs cut region i ↔ v ∈ xs ∧ v ∉ cut ∧ region v=i := by
  simp [child,List.mem_filter]

/-- A separator oracle for each induced subgraph. Region numbers identify the
components of the complement, and can be chosen arbitrarily. -/
def Separators (vertices : List Nat) (adj : Nat → Nat → Prop) (cost : Nat → Nat) : Prop :=
  ∀ xs : List Nat, xs ⊆ vertices → xs.Nodup → xs ≠ [] →
    ∃ cut : List Nat, ∃ region : Nat → Nat,
      cut ⊆ xs ∧ cut.Nodup ∧ mass cost cut * mass cost cut ≤ 64*weight cost xs ∧
      (∀ i, 2*weight cost (child xs cut region i) ≤ weight cost xs) ∧
      (∀ a ∈ xs, ∀ b ∈ xs, a ∉ cut → b ∉ cut → adj a b → region a = region b)

structure Layout (xs : List Nat) (adj : Nat → Nat → Prop) (cost : Nat → Nat) where
  home : Nat → Key
  nested : ∀ a ∈ xs, ∀ b ∈ xs, adj a b → isAncestor (home a) (home b) ∨ isAncestor (home b) (home a)
  path : ∀ p : Key, ∃ spine cs : List Nat,
    spine ⊆ xs ∧ spine.Nodup ∧ mass cost spine = cs.sum ∧
    SeparatorChain (weight cost xs) cs ∧
    ∀ v ∈ xs, isAncestor (home v) p → v ∈ spine

theorem layout {vs : List Nat} (adj : Nat → Nat → Prop) (c : Nat → Nat)
    (pos : ∀v ∈ vs, 0<c v) (oracle : Separators vs adj c) (nd : vs.Nodup) : Nonempty (Layout vs adj c) := by
  classical
  have build (w : Nat) (xs : List Nat) (eq : weight c xs=w) (sub : xs⊆vs) (hn : xs.Nodup) :
      Nonempty (Layout xs adj c) := by
    induction w using Nat.strongRecOn generalizing xs with
    | ind w ih =>
      by_cases empty : xs=[]
      · subst xs
        exact ⟨⟨fun _ => [],by simp,fun p => ⟨[],[],by simp,by simp,rfl,.stop _,by simp⟩⟩⟩
      obtain ⟨S,g,subsetS,ndS,budget,half,nocross⟩ := oracle xs sub hn empty
      have wp : 0<w := by
        cases xs with
        | nil => contradiction
        | cons x tail =>
          have hx := pos x (sub (by simp))
          have hw := Nat.mul_pos hx hx
          simp [weight,mass] at eq; omega
      let kids (i : Nat) := child xs S g i
      have down (i) : Nonempty (Layout (kids i) adj c) := by
        apply ih (weight c (kids i)) (by have h := half i; change 2*weight c (kids i) ≤ _ at h; omega) (kids i) rfl
        · exact fun _ h => sub (child_mem.mp h).1
        · exact List.filter_sublist.nodup hn
      let D (i : Nat) := Classical.choice (down i)
      let h (x : Nat) := if x∈S then [] else g x :: (D (g x)).home x
      refine ⟨⟨h,?_,?_⟩⟩
      · intro a ha b hb e
        by_cases sa : a∈S
        · exact Or.inl (by simp [h,sa,isAncestor])
        by_cases sb : b∈S
        · exact Or.inr (by simp [h,sb,isAncestor])
        have same := nocross a ha b hb sa sb e
        have A : a∈kids (g b) := child_mem.mpr ⟨ha,sa,same⟩
        have B : b∈kids (g b) := child_mem.mpr ⟨hb,sb,rfl⟩
        simp only [h,sa,sb,↓reduceIte,isAncestor]
        rw [same]
        simpa only [true_and] using (D (g b)).nested a A b B e
      · intro p
        cases p with
        | nil =>
          refine ⟨S,[mass c S],subsetS,ndS,by simp,.branch budget (child:=0) (by omega) (.stop _),?_⟩
          intro v _ pre
          by_cases hv : v∈S
          · exact hv
          · simp [h,hv,isAncestor] at pre
        | cons i p =>
          obtain ⟨s,cs,ss,ns,count,chain,enters⟩ := (D i).path p
          refine ⟨S++s,mass c S::cs,?_,?_,?_,.branch budget (half i) chain,?_⟩
          · intro v hv
            rcases List.mem_append.mp hv with f|f
            · exact subsetS f
            · exact (child_mem.mp (ss f)).1
          · exact List.nodup_append.mpr ⟨ndS,ns,fun _ f _ k e => (child_mem.mp (ss k)).2.1 (e ▸ f)⟩
          · simpa [mass,List.sum_append] using congrArg (fun k => mass c S+k) count
          · intro v hv pre
            by_cases here : v∈S
            · exact List.mem_append_left _ here
            · have ⟨e,pp⟩ : g v=i ∧ isAncestor ((D (g v)).home v) p := by simpa [h,here,isAncestor] using pre
              rw [e] at pp
              exact List.mem_append_right _ (enters v (child_mem.mpr ⟨hv,here,e⟩) pp)
  exact build _ vs rfl (fun _ h => h) nd


def cofacial (fs : List Face) (u v : Nat) : Prop :=
  ∃ f∈fs, u∈corners f ∧ v∈corners f

private def longer (a b : Key) := if a.length ≤ b.length then b else a

private theorem length_le {a b : Key} (p : isAncestor a b) : a.length ≤ b.length := by
  induction a generalizing b with
  | nil => simp
  | cons a as ih =>
    cases b with
    | nil => contradiction
    | cons b bs => simpa using ih p.2

private theorem equal_length {a b : Key} (p : isAncestor a b) (h : b.length ≤ a.length) : a=b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons a as ih =>
    cases b with
    | nil => contradiction
    | cons b bs => rw [show a=b from p.1, ih p.2 (by simpa using h)]

private theorem longer_contains (a b : Key) (p : isAncestor a b ∨ isAncestor b a) :
    isAncestor a (longer a b) ∧ isAncestor b (longer a b) := by
  by_cases h : a.length ≤ b.length
  · simp only [longer,h,↓reduceIte]
    rcases p with p|p
    · exact ⟨p,reflP _⟩
    · exact equal_length p h ▸ ⟨reflP _,reflP _⟩
  · simp only [longer,h,↓reduceIte]
    rcases p with p|p
    · exact False.elim (h (length_le p))
    · exact ⟨reflP _,p⟩

private def owner (home : Nat → Key) (f : Face) := longer (longer (home f.x) (home f.y)) (home f.z)

private theorem face_path {vs c fs} (D : Layout vs (cofacial fs) c) {f : Face} (mem : f∈fs)
    (names : ∀ f∈fs, ∀ v∈corners f, v∈vs) : ∀ v∈corners f, isAncestor (D.home v) (owner D.home f) := by
  have nested (u v : Nat) (a : u∈corners f) (b : v∈corners f) :=
    D.nested u (names _ mem _ a) v (names _ mem _ b) ⟨f,mem,a,b⟩
  have X : f.x∈corners f := by simp [corners]
  have Y : f.y∈corners f := by simp [corners]
  have Z : f.z∈corners f := by simp [corners]
  have p := longer_contains _ _ (nested f.x f.y X Y)
  have q : isAncestor (longer (D.home f.x) (D.home f.y)) (D.home f.z) ∨
      isAncestor (D.home f.z) (longer (D.home f.x) (D.home f.y)) := by
    unfold longer
    split
    · exact nested _ _ Y Z
    · exact nested _ _ X Z
  have r := longer_contains _ _ q
  intro v hv
  rcases (show v=f.x ∨ v=f.y ∨ v=f.z by simpa [corners] using hv) with rfl|rfl|rfl
  · exact transP p.1 r.1
  · exact transP p.2 r.1
  · exact r.2

private theorem flags {xs : List Face} {e : Edge} {v : Nat}
    (pos : 0<occurrences (xs.flatMap Face.sides) e) (incident : touches e v) :
    ∃ f∈xs, v∈corners f := by
  have hm := List.count_pos_iff.mp pos
  obtain ⟨item,hi,rfl⟩ := List.mem_map.mp hm
  obtain ⟨f,hf,he⟩ := List.mem_flatMap.mp hi
  refine ⟨f,hf,?_⟩
  simp only [Face.sides,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl <;> simp_all [corners,touches] <;> rcases incident with h|h <;> simp [h]

private theorem red_witness {xs : List Event} {e : Edge} (h : e∈reds xs) :
    ∃ a ∈ xs, a.edge=e ∧ a.red=true := by
  induction xs with
  | nil => simp [reds] at h
  | cons a xs ih =>
    unfold reds at h
    split at h
    next added =>
      rcases List.mem_cons.mp h with eq|prev
      · exact ⟨a,by simp,eq.symm,added.2⟩
      · obtain ⟨u,m,g⟩ := ih prev; exact ⟨u,List.mem_cons_of_mem _ m,g⟩
    next _ =>
      obtain ⟨u,m,g⟩ := ih h; exact ⟨u,List.mem_cons_of_mem _ m,g⟩

private theorem final_bound {xs : List Event} (red : List Edge) {s : Inventory}
    (passed : replay xs = some s) (valid : ∀ a∈xs, a.red=true → a.edge∈red) (v : Nat) :
    s.redDegree v ≤ simpleDegree red v := by
  rw [(replay_accurate passed).redDegree]
  unfold simpleDegree
  simp only [List.countP_eq_length_filter]
  apply (List.filter_sublist.nodup (reds_nodup _)).length_le_of_subset
  intro e he
  obtain ⟨hm,t⟩ := List.mem_filter.mp he
  obtain ⟨a,ha,rfl,yes⟩ := red_witness hm
  exact List.mem_filter.mpr ⟨valid _ ha yes,t⟩

private theorem square_eq (vs : List Nat) (d : Nat → Nat) :
    weight (fun x => cost (d x)) vs = squareMass (vs.map d) := by
  induction vs with
  | nil => rfl
  | cons x xs ih => simp [weight,mass,squareMass] at *; exact ih

/-- An actual permutation works for every prefix, with the bound evaluated
on the red degrees maintained by replay at that prefix. Edge colors come
from a fixed host red subgraph. The paired-side hypothesis is automatic for
the complete face list of a simple spherical triangulation. -/
theorem face_order_permuted (vs : List Nat) (faces : List Face) (red : List Edge)
    (distinct : vs.Nodup) (names : ∀ f∈faces, ∀ v∈corners f, v∈vs)
    (paired : ∀ e, occurrences (faces.flatMap Face.sides) e = 0 ∨
        occurrences (faces.flatMap Face.sides) e = 2)
    (redSide : ∀ f∈faces, ∀ a∈f.sides, a.red=true → a.edge∈red)
    (total : (vs.map (simpleDegree red)).sum ≤ 6*vs.length)
    (oracle : Separators vs (cofacial faces) (fun x => cost (simpleDegree red x))) :
    ∃ seq : List Face, seq.Perm faces ∧ ∀ prefix_ todo, seq=prefix_++todo → ∀ read : List Face, read.Perm prefix_ →
      ∃ s, replay (read.flatMap Face.sides) = some s ∧
        ∀ active : List Nat, active.Nodup →
          (∀ v∈active, ∃ e∈s.pending, touches e v) →
          let used := (active.map (fun v => cost (s.redDegree v))).sum
          used*used ≤ 220^2*vs.length := by
  classical
  let c := fun x => cost (simpleDegree red x)
  have pos (x : Nat) : 0<c x := by unfold c cost; omega
  obtain ⟨D⟩ := layout (cofacial faces) c (fun x _ => pos x) oracle distinct
  let key := owner D.home
  let comp := fun (a b : Face) => decide (key a ≤ key b)
  let seq := faces.mergeSort comp
  have perm : seq.Perm faces := List.mergeSort_perm .. 
  have sorted : seq.Pairwise (fun a b => key a ≤ key b) := by
    apply List.Pairwise.imp (l := seq) (R := fun a b => comp a b = true) (fun h => of_decide_eq_true h)
    exact List.pairwise_mergeSort (le := comp) (fun _ _ _ a b => decide_eq_true (List.le_trans (of_decide_eq_true a) (of_decide_eq_true b)))
      (fun a b => by rcases List.le_total (key a) (key b) with h|h <;> simp [comp,h]) faces
  refine ⟨seq,perm,?_⟩
  intro prefix_ todo cut read shuffled
  have permuted : (read++todo).Perm faces := (shuffled.append_right todo).trans (cut ▸ perm)
  have decomp (e) : occurrences (faces.flatMap Face.sides) e =
      occurrences (read.flatMap Face.sides) e + occurrences (todo.flatMap Face.sides) e := by
    have H := ((permuted.flatMap_right Face.sides).map Event.edge).count e
    simpa [occurrences,List.flatMap_append,List.count_append] using H.symm
  obtain ⟨s,replayed⟩ := (replay_succeeds_iff (read.flatMap Face.sides)).mpr (fun e => by have := paired e; have := decomp e; omega)
  refine ⟨s,replayed,?_⟩
  intro active nd live
  have point {xs ys} (eq : seq=xs++ys) (x : Face) (hx : x∈xs) : x∈faces :=
    perm.mem_iff.mp (eq ▸ List.mem_append_left ys hx)
  have split (v : Nat) (hv : v∈active) : (∃ f∈read,v∈corners f) ∧ (∃ f∈todo,v∈corners f) := by
    obtain ⟨e,he,t⟩ := live v hv
    have hr := ((replay_accurate replayed).pending _).mp he
    have := decomp e
    have := paired e
    exact ⟨flags (by omega : 0<occurrences (read.flatMap Face.sides) e) t,
      flags (by omega : 0<occurrences (todo.flatMap Face.sides) e) t⟩
  cases todo with
  | nil =>
    have empty : active=[] := List.eq_nil_iff_forall_not_mem.mpr (fun v hv => by have := (split v hv).2; simp at this)
    simp [empty]
  | cons pivot rest =>
    obtain ⟨_,after,cross⟩ := List.pairwise_append.mp (cut ▸ sorted)
    have memCurrent : pivot∈pivot::rest := by simp
    have spineMembership (v) (hv : v∈active) : v∈vs ∧ isAncestor (D.home v) (key pivot) := by
      obtain ⟨⟨f,seen,old⟩,⟨g,unseen,later⟩⟩ := split v hv
      have F := point cut f (shuffled.mem_iff.mp seen)
      have G : g∈faces := perm.mem_iff.mp (cut ▸ List.mem_append_right _ unseen)
      have earlier : key f ≤ key pivot := cross _ (shuffled.mem_iff.mp seen) _ memCurrent
      have last : key pivot ≤ key g := by
        rcases List.mem_cons.mp unseen with rfl | tail
        · exact List.le_refl _
        · exact (List.pairwise_cons.mp after).1 g tail
      exact ⟨names _ F _ old,convex (face_path D F names v old) (face_path D G names v later) earlier last⟩
    obtain ⟨spine,cs,_,ns,sc,chain,onCone⟩ := D.path (key pivot)
    have hb (v : Nat) : s.redDegree v ≤ simpleDegree red v := final_bound red replayed (by
      intro a ha yes
      obtain ⟨f,hf,g⟩ := List.mem_flatMap.mp ha
      exact redSide _ (point cut f (shuffled.mem_iff.mp hf)) _ g yes) v
    have h := active_cost_bound nd ns (fun v hv =>
      onCone v (spineMembership v hv).1 (spineMembership v hv).2) (fun v _ => hb v)
      sc (ds := vs.map (simpleDegree red)) (by simpa using total)
      (square_eq vs (simpleDegree red) ▸ chain)
    simpa using h

theorem face_order (vs : List Nat) (faces : List Face) (red : List Edge)
    (distinct : vs.Nodup) (names : ∀ f∈faces, ∀ v∈corners f, v∈vs)
    (paired : ∀ e, occurrences (faces.flatMap Face.sides) e = 0 ∨
        occurrences (faces.flatMap Face.sides) e = 2)
    (redSide : ∀ f∈faces, ∀ a∈f.sides, a.red=true → a.edge∈red)
    (total : (vs.map (simpleDegree red)).sum ≤ 6*vs.length)
    (oracle : Separators vs (cofacial faces) (fun x => cost (simpleDegree red x))) :
    ∃ seq : List Face, seq.Perm faces ∧ ∀ read todo, seq=read++todo →
      ∃ s, replay (read.flatMap Face.sides) = some s ∧
        ∀ active : List Nat, active.Nodup →
          (∀ v∈active, ∃ e∈s.pending, touches e v) →
          let used := (active.map (fun v => cost (s.redDegree v))).sum
          used*used ≤ 220^2*vs.length := by
  obtain ⟨seq,perm,order⟩ := face_order_permuted vs faces red distinct names paired redSide total oracle
  exact ⟨seq,perm,fun read todo cut => order read todo cut read (.refl _)⟩

#print axioms face_order
end Recognition.Outline
