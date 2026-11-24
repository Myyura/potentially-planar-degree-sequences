import TraceDerivative
import ForestSelection
import Mathlib.Logic.Equiv.Fin.Rotate

/-! A rotation and one starting end at each vertex recover an ordered
bijection between derivative slots and edge ends. -/
namespace Recognition.TraceRotationFibre
open Equiv Equiv.Perm
open TraceDerivative
open scoped BigOperators
noncomputable section
open Classical

variable {A B V : Type*}

/-- One orbit on each vertex fibre, including singleton fibres. -/
structure ByVertex (tail : A → V) (s : Perm A) : Prop where
  preserve : ∀ i, tail (s i) = tail i
  orbit : ∀ i j, tail i = tail j → s.SameCycle i j

abbrev Rotation (tail : A → V) := {s : Perm A // ByVertex tail s}

private def localPerm {tail : A → V} {s : Perm A} (r : ByVertex tail s) (x : V) :
    Perm {i // tail i = x} :=
  s.subtypePerm fun i => by rw [r.preserve]

private theorem localCycle {tail : A → V} {s : Perm A} (r : ByVertex tail s) (x : V) :
    (localPerm r x).IsCycleOn (Set.univ : Set {i // tail i = x}) :=
  ⟨(localPerm r x).bijOn (fun _ => Iff.rfl), fun i _ j _ =>
    (r.orbit i.val j.val (i.property.trans j.property.symm)).subtypePerm⟩

/-- Number a single finite cycle by starting at x and iterating forward. -/
private def numbering [Fintype A] (s : Perm A) (cyc : s.IsCycleOn Set.univ) (x : A) :
    Fin (Fintype.card A) ≃ A :=
  Equiv.ofBijective (fun i => (s ^ i.val) x) ((Fintype.bijective_iff_surjective_and_card _).2
    ⟨fun y => by
        have h : s.IsCycleOn (↑(Finset.univ : Finset A) : Set A) := by simpa using cyc
        obtain ⟨n,hn,hy⟩ := h.exists_pow_eq (Finset.mem_univ x) (Finset.mem_univ y)
        exact ⟨⟨n,by simpa using hn⟩,hy⟩,by simp⟩)

private theorem numbering_next [Fintype A] (s : Perm A) (cyc : s.IsCycleOn Set.univ)
    (x : A) (i : Fin (Fintype.card A)) :
    numbering s cyc x (finRotate _ i) = s (numbering s cyc x i) := by
  let := i.neZero
  change (s ^ (finRotate _ i).val) x = s ((s ^ i.val) x)
  rw [←Perm.mul_apply,←pow_succ',finRotate_apply,Fin.val_add,Fin.val_one',Nat.add_mod_mod]
  by_cases last : i.val+1 = Fintype.card A
  · have h : s.IsCycleOn (↑(Finset.univ : Finset A) : Set A) := by simpa using cyc
    have fixed := h.pow_card_apply (Finset.mem_univ x)
    simp only [last,Nat.mod_self,pow_zero,coe_one,id_eq]
    exact (by simpa using fixed.symm)
  · rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]

private theorem numbering_initial [Fintype A] (s : Perm A) (cyc : s.IsCycleOn Set.univ)
    (x : A) (h : 0 < Fintype.card A) : numbering s cyc x ⟨0,h⟩ = x := by
  change (s^0) x = x
  simp

private theorem finCongr_rotate {m n : Nat} (h : m = n) (i : Fin m) :
    finCongr h (finRotate m i) = finRotate n (finCongr h i) := by subst n; rfl

private theorem conjugate_iff (f : A ≃ B) (s : Perm A) (t : Perm B) :
    f.symm.trans (s.trans f) = t ↔ ∀ x, f (s x) = t (f x) := by
  constructor
  · intro eq x
    simpa using (Equiv.congr_fun eq (f x))
  · intro eq
    ext y
    simpa using eq (f.symm y)

private theorem intertwine_pow {f : A → B} {s : Perm A} {t : Perm B}
    (inter : ∀ x, f (s x) = t (f x)) (n : Nat) (x : A) :
    f ((s^n) x) = (t^n) (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Perm.mul_apply,inter,ih]

private def numberedMatch [Fintype A] [Fintype B]
    (s : Perm A) (t : Perm B) (cs : s.IsCycleOn Set.univ) (ct : t.IsCycleOn Set.univ)
    (x : A) (y : B) (size : Fintype.card A = Fintype.card B) : A ≃ B :=
  (numbering s cs x).symm.trans ((finCongr size).trans (numbering t ct y))

private theorem numberedMatch_start [Fintype A] [Fintype B]
    (s : Perm A) (t : Perm B) (cs : s.IsCycleOn Set.univ) (ct : t.IsCycleOn Set.univ)
    (x : A) (y : B) (size : Fintype.card A = Fintype.card B) :
    numberedMatch s t cs ct x y size x = y := by
  have hp := Fintype.card_pos_iff.mpr ⟨x⟩
  have hx := (numbering s cs x).symm_apply_eq.mpr (numbering_initial s cs x hp).symm
  change numbering t ct y (finCongr size ((numbering s cs x).symm x)) = y
  rw [hx]
  exact numbering_initial t ct y (size ▸ hp)

private theorem numberedMatch_commute [Fintype A] [Fintype B]
    (s : Perm A) (t : Perm B) (cs : s.IsCycleOn Set.univ) (ct : t.IsCycleOn Set.univ)
    (x : A) (y : B) (size : Fintype.card A = Fintype.card B) (i : A) :
    numberedMatch s t cs ct x y size (s i) = t (numberedMatch s t cs ct x y size i) := by
  obtain ⟨k,rfl⟩ := (numbering s cs x).surjective i
  simp only [numberedMatch,Equiv.trans_apply,←numbering_next,Equiv.symm_apply_apply,finCongr_rotate]

/-- Conjugating the cyclic successor on the slots gives a rotation on the ends. -/
def induced {f : A → V} {g : B → V} {s : Perm A} [Finite A] (cs : ByVertex f s)
    (e : Matching f g) : Rotation g := by
  let t := e.val.symm.trans (s.trans e.val)
  have inter := (conjugate_iff e.val s t).mp rfl
  refine ⟨t,⟨fun j => ?_,fun i j eq => ?_⟩⟩
  · obtain ⟨p,rfl⟩ := e.val.surjective j
    rw [←inter,e.property,cs.preserve,e.property]
  · obtain ⟨p,rfl⟩ := e.val.surjective i
    obtain ⟨q,rfl⟩ := e.val.surjective j
    rw [e.property,e.property] at eq
    obtain ⟨k,hk⟩ := (cs.orbit p q eq).exists_nat_pow_eq
    exact ⟨k,by simp [←intertwine_pow inter,hk]⟩

/-- The fibre of a fixed rotation is parametrised by one target end per vertex.
The positivity assumption is expressed by a choice of one source port per vertex. -/
def startingEnds [Fintype A] [Fintype B] {f : A → V} {g : B → V}
    {s : Perm A} (cs : ByVertex f s) (t : Rotation g) (base : ∀ v, {i // f i = v})
    (size : ∀ v, Fintype.card {i // f i=v} = Fintype.card {j // g j=v}) :
    {e : Matching f g // induced cs e = t} ≃ (∀ v, {j // g j=v}) := by
  let atBase (e : {e : Matching f g // induced cs e = t}) (v : V) : {j // g j=v} :=
    ⟨e.val.val (base v), (e.val.property _).trans (base v).property⟩
  apply Equiv.ofBijective atBase
  constructor
  · intro e e' h
    have intertwines (z : {e : Matching f g // induced cs e = t}) :
        ∀ x, z.val.val (s x) = t.val (z.val.val x) :=
      (conjugate_iff _ _ _).mp (congrArg Subtype.val z.property)
    apply Subtype.ext
    apply Subtype.ext
    ext i
    obtain ⟨k,hk⟩ := (cs.orbit (base (f i)).val i (base (f i)).property).exists_nat_pow_eq
    have h0 : e.val.val (base (f i)) = e'.val.val (base (f i)) :=
      congrArg Subtype.val (congrFun h (f i))
    rw [←hk,intertwine_pow (intertwines e),intertwine_pow (intertwines e'),h0]
  · intro target
    let b v := numberedMatch (localPerm cs v) (localPerm t.property v)
      (localCycle cs v) (localCycle t.property v) (base v) (target v) (size v)
    let e : Matching f g := ⟨Equiv.ofFiberEquiv b,Equiv.ofFiberEquiv_map b⟩
    have ev (v : V) (i : {i // f i=v}) : e.val i.val = (b v i).val := by
      obtain ⟨i,hi⟩ := i
      subst v
      rfl
    have eq : induced cs e = t := by
      apply Subtype.ext
      apply (conjugate_iff _ _ _).mpr
      intro i
      let v := f i
      let p : {j // f j=v} := ⟨i,rfl⟩
      change e.val (localPerm cs v p).val = t.val (e.val p.val)
      rw [ev v (localPerm cs v p),ev v p]
      exact congrArg Subtype.val (numberedMatch_commute _ _ _ _ _ _ _ p)
    refine ⟨⟨e,eq⟩,?_⟩
    funext v
    apply Subtype.ext
    change e.val (base v).val = (target v).val
    rw [ev]
    exact congrArg Subtype.val (numberedMatch_start _ _ _ _ _ _ _)

/-- Regroup any weight determined by the induced rotation. Each rotation
has exactly the product of the vertex degrees as its multiplicity. -/
theorem sum_induced [Fintype A] [Fintype B] [Fintype V] {f : A → V} {g : B → V}
    {s : Perm A} (cs : ByVertex f s) (base : ∀ v, {i // f i = v})
    (size : ∀ v, Fintype.card {i // f i=v} = Fintype.card {j // g j=v})
    (w : Rotation g → Nat) :
    ∑ e : Matching f g, w (induced cs e) =
      (∏ v, Nat.card {j // g j=v}) * ∑ t, w t := by
  classical
  rw [←(Equiv.sigmaFiberEquiv (fun e : Matching f g => induced cs e)).sum_comp
    (fun e => w (induced cs e)),Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  have key := Nat.card_congr (startingEnds cs t base size)
  rw [Nat.card_pi,Nat.card_eq_fintype_card] at key
  change ∑ x : {e : Matching f g // induced cs e = t}, w (induced cs x.val) = _
  have at_t (x : {e : Matching f g // induced cs e = t}) : w (induced cs x.val) = w t :=
    congrArg w x.property
  simp only [at_t,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,key,Nat.cast_id]

theorem traceEvaluation_rotations [Fintype B] [Fintype V] {n : Nat} (f : Fin n → V) (g : B → V)
    (s : Perm (Fin n)) (flip : Perm B) (inv : Function.Involutive flip) (q : Nat)
    (cs : ByVertex f s) (base : ∀ v, {i // f i=v})
    (size : ∀ v, Fintype.card {i // f i=v} = Fintype.card {j // g j=v}) :
    traceEvaluation g flip q f s = (∏ v, Nat.card {j // g j=v}) *
      ∑ t : Rotation g, q ^ LeanPool.K5MinorFreeChoosability.cycleCount (t.val * flip) :=
  by
    rw [traceEvaluation_faces g flip q f s inv]
    rw [←sum_induced cs base size (w := fun t => q ^ LeanPool.K5MinorFreeChoosability.cycleCount (t.val * flip))]
    apply Finset.sum_equiv (Equiv.refl (Matching f g)) (fun _ => by simp)
    intro e _
    rfl

/-- If there is a vertex with the wrong number of incident ends, all terms
for this graph vanish, irrespective of matrix size or the successor. -/
theorem traceEvaluation_wrong [Fintype B] [Fintype V] {n : Nat} (f : Fin n → V) (g : B → V)
    (s : Perm (Fin n)) (flip : Perm B) (inv : Function.Involutive flip) (q : Nat)
    (wrong : multiplicity g ≠ multiplicity f) : traceEvaluation g flip q f s = 0 := by
  classical
  rw [traceEvaluation_faces g flip q f s inv]
  have eq := count_matchings f g
  rw [ite_eq_right wrong] at eq
  rw [Nat.card_eq_fintype_card] at eq
  have : IsEmpty (Matching f g) := Fintype.card_eq_zero_iff.mp eq
  exact Finset.sum_eq_zero fun e _ => (isEmptyElim e : _)

open LeanPool.K5MinorFreeChoosability

/-- The vertex fibre of graph darts is the ordinary neighbor set. -/
def outgoing (G : SimpleGraph V) (v : V) :
    {d : G.Dart // d.fst=v} ≃ {j // G.Adj v j} where
  toFun := fun ⟨d,h⟩ => ⟨d.snd,h ▸ d.adj⟩
  invFun j := ⟨⟨(v,j.val),j.property⟩,rfl⟩
  left_inv := by rintro ⟨⟨⟨u,w⟩,h⟩,rfl⟩; rfl
  right_inv _ := rfl

private def graphRotation (G : SimpleGraph V) : Rotation (fun d : G.Dart => d.fst) ≃
    ArithmeticRotation.Rotation G where
  toFun r := ⟨r.val,⟨r.property.preserve,r.property.orbit⟩⟩
  invFun r := ⟨r.val,⟨r.property.fst_apply,r.property.sameCycle⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- On a simple graph with the prescribed positive degrees, the evaluated
mixed differential trace equals the rotation polynomial, including its
starting-end weight. -/
theorem graph_inventory [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : Nat} (f : Fin n → V) (s : Perm (Fin n)) (q : Nat) (cs : ByVertex f s)
    (base : ∀ v, {i // f i=v}) (size : ∀ v, multiplicity f v = Nat.card {j // G.Adj v j}) :
    ((traceEvaluation (fun d : G.Dart => d.fst) (dartSymm G) q f s : Nat) : ℤ) =
      (ArithmeticRotation.inventory G (fun _ => ∏ v, multiplicity f v)).eval (q : ℤ) := by
  classical
  let tail (d : G.Dart) := d.fst
  have eq (v : V) : multiplicity f v = Nat.card {d // tail d = v} :=
    (size v).trans (Nat.card_congr (outgoing G v)).symm
  have counts (v : V) : Fintype.card {i // f i=v} = Fintype.card {d // tail d=v} := by
    simpa only [multiplicity_apply,Nat.card_eq_fintype_card] using eq v
  rw [traceEvaluation_rotations f tail s (dartSymm G) SimpleGraph.Dart.symm_involutive q cs base counts]
  simp_rw [←eq]
  let := Fintype.ofFinite (ArithmeticRotation.Rotation G)
  simp only [ArithmeticRotation.inventory,Polynomial.eval_finsetSum,Polynomial.eval_monomial,
    Nat.cast_mul,Nat.cast_sum,Nat.cast_pow,Finset.mul_sum]
  apply Finset.sum_equiv (graphRotation G) (fun _ => by simp)
  intro r _
  rfl

section Row
variable (ds : List Nat)

/-- The derivative positions of vertex v are its labelled cyclic array
of length d_v. Flattening these arrays only chooses the order in which
formal partial derivatives are applied. -/
abbrev Slot := (v : Fin ds.length) × Fin ds[v.val]
def slotsOrder : Slot ds ≃ Fin (Fintype.card (Slot ds)) := Fintype.equivFin _
def slotTail (p : Fin (Fintype.card (Slot ds))) := ((slotsOrder ds).symm p).fst
def turn : Perm (Slot ds) := Equiv.sigmaCongrRight fun v => finRotate ds[v.val]
def slotTurn := ((slotsOrder ds).symm.trans ((turn ds).trans (slotsOrder ds)))

private theorem circle : ByVertex (fun p : Slot ds => p.fst) (turn ds) := by
  refine ⟨fun _ => rfl,?_⟩
  rintro ⟨v,i⟩ ⟨w,j⟩ eq
  change v = w at eq
  subst w
  let e : Fin ds[v.val] → Slot ds := fun j => ⟨v,j⟩
  have step (z : Fin ds[v.val]) : e (finRotate _ z) = turn ds (e z) := rfl
  let := i.neZero
  let k := (j-i).val
  have hit : ((finRotate _ ^ k) i) = j := by
    rw [Perm.coe_pow,←finCycle_eq_finRotate_iterate]
    simp [finCycle_apply]
  refine ⟨(k : ℤ),?_⟩
  rw [zpow_natCast]
  exact (intertwine_pow step k i).symm.trans (congrArg e hit)

private theorem slotCycle : ByVertex (slotTail ds) (slotTurn ds) :=
  (induced (circle ds) (⟨slotsOrder ds,fun p => by simp [slotTail]⟩ :
    Matching (fun p : Slot ds => p.fst) (slotTail ds))).property

private def slotFiber (v : Fin ds.length) : {p // slotTail ds p = v} ≃ Fin ds[v.val] :=
  ((slotsOrder ds).symm.subtypeEquiv (q := fun p : Slot ds => p.fst=v) (fun p => by rfl)).trans {
    toFun := fun ⟨⟨_,i⟩,h⟩ => h ▸ i
    invFun := fun i => ⟨⟨v,i⟩,rfl⟩
    left_inv := by rintro ⟨⟨w,i⟩,rfl⟩; rfl
    right_inv := fun _ => rfl }

private theorem slotCount (v : Fin ds.length) : multiplicity (slotTail ds) v = ds[v.val] :=
  (multiplicity_apply _ _).trans ((Nat.card_congr (slotFiber ds v)).trans (Nat.card_fin _))

variable (q : Nat)
def rowTrace (G : SimpleGraph (Fin ds.length)) : Nat := by
  classical
  exact traceEvaluation (fun d : G.Dart => d.fst) (dartSymm G) q (slotTail ds) (slotTurn ds)

private theorem rowProd : (∏ v : Fin ds.length, multiplicity (slotTail ds) v) = ds.prod := by
  simp_rw [slotCount]
  rw [←List.prod_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

/-- On every matching degree row, the graph trace equals the evaluation
of the explicit starting-end-weighted rotation polynomial. -/
theorem rowTrace_inventory (pos : ∀ k ∈ ds, 0 < k)
    (G : SimpleGraph (Fin ds.length)) (degrees : ∀ v : Fin ds.length, Nat.card {j // G.Adj v j}=ds[v.val]) :
    (rowTrace ds q G : ℤ) = (ArithmeticRotation.inventory G (fun _ => ds.prod)).eval (q : ℤ) := by
  classical
  change (traceEvaluation _ _ _ _ _ : ℤ) = _
  rw [←rowProd ds]
  apply graph_inventory G _ _ _ (slotCycle ds)
    (fun v => (slotFiber ds v).symm ⟨0, pos _ (List.getElem_mem v.isLt)⟩)
  intro v
  exact (slotCount ds v).trans (degrees v).symm

/-- Every graph of a different degree row contributes zero. -/
theorem rowTrace_wrong (G : SimpleGraph (Fin ds.length))
    (wrong : ¬∀ v : Fin ds.length, Nat.card {j // G.Adj v j}=ds[v.val]) :
    rowTrace ds q G = 0 := by
  classical
  apply traceEvaluation_wrong _ _ _ _ SimpleGraph.Dart.symm_involutive
  intro eq
  apply wrong
  intro v
  have same := DFunLike.congr_fun eq v
  rw [slotCount,multiplicity_apply] at same
  exact (Nat.card_congr (outgoing G v)).symm.trans same

/-- Summing all tree-weighted differential evaluations gives the row
inventory whose top finite difference detects planarity. -/
theorem tree_sum_inventory (pos : ∀ k ∈ ds, 0 < k) :
    (∑ G : ArithmeticRotation.ConnectedRealization ds,
       ((MatrixTreeWeight.trees G.val).card : ℤ) * rowTrace ds q G.val) =
      (ArithmeticRotation.rowInventory ds (MatrixTreeWeight.rotationWeight ds)).eval (q : ℤ) := by
  classical
  rw [ArithmeticRotation.rowInventory,Polynomial.eval_finsetSum]
  apply Finset.sum_equiv (Equiv.refl _) (fun _ => by simp)
  intro G _
  simp only [Equiv.refl_apply,rowTrace_inventory ds q pos G.val G.property.2,ArithmeticRotation.inventory,
    Polynomial.eval_finsetSum,Polynomial.eval_monomial,Finset.mul_sum,MatrixTreeWeight.rotationWeight,
    Nat.cast_mul,mul_assoc]
  apply Finset.sum_equiv (Equiv.refl (ArithmeticRotation.Rotation G.val))
  · intro _
    exact ⟨fun _ => @Finset.mem_univ _ (Fintype.ofFinite _) _,fun _ => @Finset.mem_univ _ (Fintype.ofFinite _) _⟩
  · intro _ _
    rfl


/-- The differential expansion may sum over all simple labelled graphs.
Disconnected terms have zero tree weight; wrong degrees have zero trace. -/
theorem all_graphs_inventory (pos : ∀ k ∈ ds, 0 < k) :
    (∑ G : SimpleGraph (Fin ds.length), ((MatrixTreeWeight.trees G).card : ℤ) * rowTrace ds q G) =
      (ArithmeticRotation.rowInventory ds (MatrixTreeWeight.rotationWeight ds)).eval (q : ℤ) := by
  classical
  let good (G : SimpleGraph (Fin ds.length)) := G.Connected ∧
    ∀ v : Fin ds.length, Nat.card {j // G.Adj v j} = ds[v.val]
  let w (G : SimpleGraph (Fin ds.length)) : ℤ := (MatrixTreeWeight.trees G).card * rowTrace ds q G
  have zero : ∑ H : {G // ¬ good G}, w H.val = 0 := by
    apply Finset.sum_eq_zero
    intro H _
    by_cases connected : H.val.Connected
    · have wrong := fun deg => H.property ⟨connected,deg⟩
      simp [w,rowTrace_wrong ds q H.val wrong]
    · have no := mt (MatrixTreeWeight.trees_pos_iff H.val).mp connected
      have card : (MatrixTreeWeight.trees H.val).card = 0 := by omega
      simp [w,card]
  rw [←tree_sum_inventory ds q pos]
  change (∑ G, w G) = _
  rw [←Fintype.sum_subtype_add_sum_subtype good w,zero,add_zero]


private theorem rowTrace_zero (nonempty : ds ≠ []) (pos : ∀ k ∈ ds, 0 < k)
    (G : SimpleGraph (Fin ds.length)) : rowTrace ds 0 G = 0 := by
  classical
  let v : Fin ds.length := ⟨0,List.length_pos_iff.mpr nonempty⟩
  let i : Slot ds := ⟨v,⟨0,pos _ (List.getElem_mem v.isLt)⟩⟩
  have : IsEmpty (Fin (Fintype.card (Slot ds)) → Fin 0) :=
    ⟨fun a => Fin.elim0 (a (slotsOrder ds i))⟩
  exact Finset.sum_eq_zero fun a _ => isEmptyElim a

/-- The finite difference in the paper starts at 1, since the graph
trace has zero value at q = 0 for a nonempty positive row. -/
theorem difference_inventory (nonempty : ds ≠ []) (pos : ∀ k ∈ ds, 0 < k) (f : Nat) :
    (∑ q ∈ Finset.Icc 1 f, (-1 : ℤ)^(f-q) * f.choose q *
      ∑ G : SimpleGraph (Fin ds.length), ((MatrixTreeWeight.trees G).card : ℤ) * rowTrace ds q G) =
      SphericalTerm.alternating (ArithmeticRotation.rowInventory ds (MatrixTreeWeight.rotationWeight ds)) f := by
  classical
  rw [SphericalTerm.alternating]
  simp_rw [←all_graphs_inventory ds _ pos]
  let term (q : Nat) : ℤ := (-1 : ℤ)^(f-q) * f.choose q *
    ∑ G : SimpleGraph (Fin ds.length), ((MatrixTreeWeight.trees G).card : ℤ) * rowTrace ds q G
  change ∑ q ∈ Finset.Icc 1 f, term q = ∑ q ∈ Finset.range (f+1), term q
  have iz : Finset.Icc 1 f = (Finset.range (f+1)).erase 0 := by
    ext x
    simp only [Finset.mem_Icc,Finset.mem_erase,Finset.mem_range]
    omega
  rw [iz,Finset.sum_erase_eq_sub (Finset.mem_range.mpr (Nat.zero_lt_succ _))]
  simp [term,rowTrace_zero ds nonempty pos]

/-- The alternating sum of the actual graphwise mixed partial evaluations
decides ordinary potential planarity in the dense positive branch. -/
theorem difference_planaric (nonempty : ds ≠ []) (pos : ∀ k ∈ ds, 0 < k)
    (dense : 2*ds.length ≤ ds.sum) :
    let f := ds.sum / 2 + 2 - ds.length
    0 < (∑ q ∈ Finset.Icc 1 f, (-1 : ℤ)^(f-q) * f.choose q *
      ∑ G : SimpleGraph (Fin ds.length), ((MatrixTreeWeight.trees G).card : ℤ) * rowTrace ds q G) ↔
      SparseBoundary.Planaric ds := by
  dsimp only
  rw [difference_inventory ds nonempty pos]
  exact ForestSelection.tree_weighted_iff_planaric ds nonempty pos dense

end Row

end
end Recognition.TraceRotationFibre
