import StellationResult

/-! Full-face insertion and saturation for the fixed subdivision-budget reduction. -/

namespace RecognizingPotentiallyPlanarDegreeSequences.FixedBudget

open Recognition Recognition.Rigidity Recognition.Layers SparseBoundary

private theorem mass_mul {V : Type} (xs : List V) (f : V → Nat) (k : Nat) :
    mass xs (fun v => k * f v) = k * mass xs f := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih => simpa [mass, Nat.mul_add] using congrArg (k*f x + ·) ih

private theorem add_mass {V : Type} (xs : List V) (f g : V → Nat) :
    mass xs (fun v => f v + g v) = mass xs f + mass xs g := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih =>
    change f x + g x + mass xs _ = (f x + mass xs f) + (g x + mass xs g)
    rw [ih]
    omega

private theorem mass_mono {V : Type} (xs : List V) (f g : V → Nat) (h : ∀ v ∈ xs, f v ≤ g v) :
    mass xs f ≤ mass xs g := by
  induction xs with
  | nil => simp [mass]
  | cons x xs ih =>
    exact Nat.add_le_add (h x (by simp)) (ih (fun v hv => h v (by simp [hv])))

private theorem agree_of_mass {V : Type} (xs : List V) (f g : V → Nat)
    (le : ∀ v ∈ xs, f v ≤ g v) (eq : mass xs f = mass xs g) :
    ∀ v ∈ xs, f v = g v := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := le x (by simp)
    have tail := fun v hv => le v (List.mem_cons_of_mem x hv)
    have ht := mass_mono xs f g tail
    change f x + mass xs f = g x + mass xs g at eq
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · exact ih tail (by omega) v hv

/-- If the number of designated cubic stars accounts for every face,
the pre-deletion degree at each surviving vertex is twice its degree after
deletion. The proof starts with an actual triangular map and counts flags. -/
theorem saturated_peeling {V : Type} {M : Map V} (P : Peeling M) (E : Enumeration V)
    (total : mass E.vertices (degree (M := M) E) = 9 * P.newCount E)
    (v : P.Old) :
    degree (M := M) E v.val = 2 * degree (M := P.map) (P.enumeration E) v := by
  classical
  let required (x : V) := 2 * starNeighbors P E x + 3 * mark (P.fresh x)
  have le (x : V) : required x ≤ degree (M := M) E x := by
    by_cases hx : P.fresh x
    · have cube := (cubic_iff_degree E x).mp (P.cubic x hx)
      simp [required, zero_stars P E hx, mark, hx, cube]
    · have flags := count_omitted_flags P E (⟨x,hx⟩ : P.Old)
      have split := split_degree P E x
      dsimp only at flags
      simp [required, mark, hx]
      omega
  have eq : mass E.vertices required = mass E.vertices (degree (M := M) E) := by
    change mass E.vertices (fun x => 2 * starNeighbors P E x + 3 * mark (P.fresh x)) = _
    rw [add_mass, mass_mul, mass_mul, total_new_neighbors, total]
    change 2 * (3 * P.newCount E) + 3 * P.newCount E = 9 * P.newCount E
    omega
  have actual := agree_of_mass E.vertices required _ (fun x _ => le x) eq v.val (E.complete _)
  simp [required, mark, v.property] at actual
  rw [degree_of_peeled_map]
  have split := split_degree P E v.val
  omega

/-- The row operation which doubles old degrees and adds a cubic in every face. -/
def full (xs : List Nat) : List Nat := xs.map (2 * ·) ++ List.replicate (2 * xs.length - 4) 3

theorem full_length (xs : List Nat) : (full xs).length = xs.length + (2 * xs.length - 4) := by
  simp [full]

theorem full_euler (xs : List Nat) (hn : 4 ≤ xs.length) (hs : xs.sum + 12 = 6*xs.length) :
    (full xs).sum + 12 = 6*(full xs).length := by
  have dbl : (xs.map (2 * ·)).sum = 2 * xs.sum := by
    simpa [mass] using mass_mul xs id 2
  simp only [full, List.sum_append, dbl, List.sum_replicate_nat, List.length_append, List.length_map,
    List.length_replicate]
  omega

theorem full_low {xs : List Nat} (lo : ∀ d ∈ xs, 3 ≤ d) :
    ∀ d ∈ full xs, 3 ≤ d := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
    have := lo d hd
    omega
  · rw [List.eq_of_mem_replicate h]

theorem full_lift (xs : List Nat) : full xs = StellationResult.lift xs [] 0 := by
  unfold full StellationResult.lift Reduction.raised
  simp only [Nat.sub_zero]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.getElem_zipIdx]

/-- A complete face round preserves the ordinary planar degree language in both
directions on the graphic maximal-sum instances supplied by the hardness reduction. -/
theorem planaric_full_iff {xs : List Nat} (hv : Reduction.TableValid xs) :
    Planaric (full xs) ↔ Planaric xs := by
  have size := hv.1
  rw [full_lift, StellationResult.planaric_iff xs [] 0 (by omega) hv.2.1
    (fun d mem => (hv.2.2 d mem).1) (by simp) (by simp) (by simp)]
  constructor
  · rintro ⟨R, hp, _⟩
    exact ⟨Transfer.graph R, Transfer.graph_realizes R, hp⟩
  · rintro ⟨G, hg, hp⟩
    obtain ⟨R, _⟩ := Wagner.tight_embedding xs G hv hg hp
    refine ⟨R, EliminationResult.model_planar R hv, ⟨?_⟩⟩
    exact {
      fill := fun _ => True
      covers := fun _ => by simp [Stacking.vacant]
      disjoint := fun _ _ _ _ _ h => False.elim (h.2 trivial) }


theorem full_valid {xs : List Nat} (hv : Reduction.TableValid xs) : Reduction.TableValid (full xs) := by
  have size := hv.1
  refine ⟨by rw [full_length]; omega, full_euler xs (by omega) hv.2.1, ?_⟩
  intro x hx
  refine ⟨full_low (fun d hd => (hv.2.2 d hd).1) _ hx, ?_⟩
  rcases List.mem_append.mp hx with h | h
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp h
    have := (hv.2.2 d hd).2
    rw [full_length]
    omega
  · rw [List.eq_of_mem_replicate h, full_length]
    omega

private theorem full_value_old (xs : List Nat) {i : Nat} (hi : i < xs.length) :
    (full xs)[i]?.getD 0 = 2 * xs[i]?.getD 0 := by
  have ho : i < (full xs).length := by rw [full_length]; omega
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem ho]
  simp [full, List.getElem_append_left, hi]

private theorem full_value_new (xs : List Nat) {i : Nat}
    (lo : xs.length ≤ i) (hi : i < (full xs).length) : (full xs)[i]?.getD 0 = 3 := by
  rw [List.getElem?_eq_getElem hi]
  simp [full, List.getElem_append_right (by simpa : (xs.map (2*·)).length ≤ i)]

private theorem mass_suffix (n k : Nat) :
    mass (List.range (n+k)) (fun i => mark (n ≤ i)) = k := by
  unfold mass
  rw [List.range_add, List.map_append, List.map_map, List.sum_append]
  rw [List.map_congr_left (l := List.range n) (g := fun _ => 0) (fun i hi => by
    have := List.mem_range.mp hi
    simp [mark, show ¬n ≤ i by omega])]
  simp [Function.comp_def, mark]

/-- The inner full layer eliminates the one unit of degree slack at every
marked vertex. The input is an ordinary planar triangulation degree row;
evenness is derived by peeling its actual labelled spherical map. -/
theorem recover_marked_full {base g : List Nat} (valid : Reduction.TableValid base)
    (gv : Reduction.TableValid g) (gp : Planaric g)
    (size : g.length = (full base).length) (boost : Nat → Nat)
    (small : ∀ i, boost i ≤ 3) (fresh : ∀ i, base.length ≤ i → boost i = 0)
    (upper : ∀ i < g.length, 2*(g[i]?.getD 0) ≤ 2*((full base)[i]?.getD 0) + boost i) :
    g = full base ∧ Planaric base := by
  classical
  obtain ⟨G, hg, hp⟩ := gp
  obtain ⟨R, _⟩ := Wagner.tight_embedding g G gv hg hp
  have n := valid.1
  have sz : g.length = base.length + (2*base.length-4) := size.trans (full_length _)
  have cubic (i : Nat) (lo : base.length ≤ i) (hi : i < g.length) : g[i]?.getD 0 = 3 := by
    have h := upper i hi
    rw [full_value_new base lo (size ▸ hi), fresh i lo] at h
    have low := (gv.2.2 g[i] (List.getElem_mem hi)).1
    simp only [List.getElem?_eq_getElem hi,Option.getD_some] at *
    omega
  let P : Peeling R.map := {
    fresh := fun v => base.length ≤ R.label v
    cubic := fun v hv => (cubic_iff_degree R.vertices v).mpr
      ((R.value v).trans (cubic _ hv (bound R v)))
    fourOld := fun x y z => by
      obtain ⟨i, hi, hx, hy, hz⟩ := choose_old base.length (R.label x) (R.label y) (R.label z) (by omega)
      obtain ⟨w, hw⟩ := (R.hits i).mp (by omega)
      exact ⟨w, by grind⟩ }
  have stars : P.newCount R.vertices = 2*base.length-4 := by
    change mass R.vertices.vertices (fun x => mark (base.length ≤ R.label x)) = _
    rw [label_sum R (fun i => mark (base.length ≤ i)), sz, mass_suffix]
  have count : mass R.vertices.vertices (degree (M := R.map) R.vertices) = g.sum := by
    unfold mass
    rw [List.map_congr_left (fun v _ => R.value v)]
    change mass R.vertices.vertices (fun v => g[R.label v]?.getD 0) = _
    rw [label_sum R (fun i => g[i]?.getD 0)]
    exact mass_get g 0
  have total : mass R.vertices.vertices (degree (M := R.map) R.vertices) = 9 * P.newCount R.vertices := by
    rw [count, stars]
    have h := gv.2.1
    omega
  have le (i : Nat) (hi : i < g.length) : g[i]?.getD 0 ≤ (full base)[i]?.getD 0 := by
    by_cases lo : base.length ≤ i
    · rw [cubic i lo hi, full_value_new base lo (size ▸ hi)]
    obtain ⟨v, hv⟩ := (R.hits i).mp hi
    have hvold : ¬P.fresh v := by change ¬base.length ≤ R.label v; rwa [hv]
    have par := saturated_peeling P R.vertices total ⟨v,hvold⟩
    rw [R.value v, hv] at par
    have h := upper i hi
    have old := full_value_old base (Nat.lt_of_not_ge lo)
    rw [old] at h ⊢
    have := small i
    omega
  have sums : g.sum = (full base).sum := by
    have a := gv.2.1
    have b := (full_valid valid).2.1
    omega
  have eq := agree_of_mass (List.range g.length) (fun i => g[i]?.getD 0)
    (fun i => (full base)[i]?.getD 0) (fun i hi => le i (List.mem_range.mp hi)) (by
      calc
        _ = g.sum := mass_get g 0
        _ = (full base).sum := sums
        _ = _ := by rw [size]; exact (mass_get (full base) 0).symm)
  have rows : g = full base := by
    apply List.ext_getElem size
    intro i hi hj
    simpa [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using eq i (List.mem_range.mpr hi)
  exact ⟨rows, (planaric_full_iff valid).mp (rows ▸ ⟨G,hg,hp⟩ : Planaric (full base))⟩

/-- The first r original labels and the first r labels of the first cubic generation. -/
def marks (n r : Nat) := List.range r ++ List.range' n r

theorem marks_nodup {n r : Nat} (small : r ≤ n) : (marks n r).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨List.nodup_range, List.nodup_range' 1, ?_⟩
  intro i hi j hj hij
  subst j
  have a := List.mem_range.mp hi
  obtain ⟨j, _, e⟩ := List.mem_range'.mp hj
  omega

theorem marks_bounded {n r i : Nat} (_small : r ≤ n) (hi : i ∈ marks n r) :
    i < n+r := by
  rcases List.mem_append.mp hi with h | h
  · have h := List.mem_range.mp h; omega
  · obtain ⟨j, hj, e⟩ := List.mem_range'.mp h; omega

private def markedBoost (U : List Nat) (i : Nat) := 3*(U.contains i).toNat

/-- Old degrees in the output before adjoining either generation of low vertices. -/
def oldRow (xs U : List Nat) :=
  (List.range xs.length).map (fun i => 2*xs[i]?.getD 0 + markedBoost U i)

theorem oldRow_sum {xs U : List Nat} (nd : U.Nodup) (bound : ∀ i∈U, i<xs.length) :
    (oldRow xs U).sum = 2*xs.sum + 3*U.length := by
  change mass (List.range xs.length) (fun i => 2*xs[i]?.getD 0 + 3*(U.contains i).toNat) = _
  rw [add_mass, mass_mul, mass_mul, selected_mass U nd xs.length bound]
  have q := mass_get xs 0
  simp only [Nat.add_zero] at q
  rw [q]

theorem oldRow_get (xs U : List Nat) {i : Nat} (hi : i < xs.length) :
    (oldRow xs U)[i]?.getD 0 = 2*xs[i]?.getD 0 + 3*(U.contains i).toNat := by
  simp [oldRow, hi, markedBoost]

/-- The unpadded maximal-sum list in the reduction. -/
def core (d : List Nat) (r : Nat) :=
  let a := full (full d)
  oldRow a (marks d.length r) ++ List.replicate (2*a.length-4+2*r) 3

theorem core_length {d : List Nat} (r : Nat) (hv : Reduction.TableValid d) :
    (core d r).length + 52 = 27*d.length + 2*r := by
  have hn := hv.1
  simp only [core,oldRow,List.length_append,List.length_map,List.length_range,
    List.length_replicate,full_length]
  omega

theorem core_euler {d : List Nat} {r : Nat} (hv : Reduction.TableValid d) (fit : r+3 ≤ d.length) :
    (core d r).sum + 12 = 6*(core d r).length := by
  have hn := hv.1
  have av := (full_valid (full_valid hv)).2.1
  have lenA := full_length (full d)
  have lenD := full_length d
  have bounded (i : Nat) (hi : i ∈ marks d.length r) : i < (full (full d)).length := by
    have h := marks_bounded (by omega : r ≤ d.length) hi; omega
  have h := oldRow_sum (marks_nodup (by omega : r ≤ d.length)) bounded
  have mlen : (marks d.length r).length = 2*r := by simp [marks, Nat.two_mul]
  rw [mlen] at h
  simp only [core,List.sum_append,List.sum_replicate_nat,List.length_append,oldRow,
    List.length_map,List.length_range,List.length_replicate] at *
  omega

theorem linear_budget {d : List Nat} (hv : Reduction.TableValid d) :
    (core d (d.length-3)).length = 29*((d.length-3)+1) := by
  have := core_length (d.length-3) hv
  have := hv.1
  omega

/-- Once the old induced graph is a triangulation with the degree inequalities
forced by saturation of the old-to-new cut, the unpadded source itself is planaric. -/
theorem recover_source {d g : List Nat} {r : Nat} (dv : Reduction.TableValid d)
    (fit : r+3 ≤ d.length) (gv : Reduction.TableValid g) (gp : Planaric g)
    (len : g.length=(full (full d)).length)
    (cut : ∀ i < g.length, 2*(g[i]?.getD 0) ≤ (oldRow (full (full d)) (marks d.length r))[i]?.getD 0) :
    Planaric d := by
  let U := marks d.length r
  have hd := full_length d
  have small (i) : markedBoost U i ≤ 3 := by
    have := Bool.toNat_le (U.contains i)
    unfold markedBoost
    omega
  have old (i) (hi : (full d).length ≤ i) : markedBoost U i = 0 := by
    have no : i ∉ U := fun h => by
      have := marks_bounded (by omega : r ≤ d.length) h
      omega
    simp [markedBoost, no]
  apply (planaric_full_iff dv).mp
  refine (recover_marked_full (full_valid dv) gv gp len (markedBoost U) small old ?_).2
  intro i hi
  simpa only [oldRow_get (full (full d)) U (len ▸ hi),markedBoost,U] using cut i hi

end RecognizingPotentiallyPlanarDegreeSequences.FixedBudget
