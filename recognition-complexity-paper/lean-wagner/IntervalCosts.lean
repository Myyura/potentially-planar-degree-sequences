import IntervalSearch
import AlgorithmCost
import WireSearch

/-! A costed implementation of the interval table. It compares rows by
scanning the four successive cuts and stops at the first matching move.
List and integer operations in a leaf are charged conservatively at the
maximum bit width of its entries (bounded here even by their values). -/
namespace Recognition.IntervalCosts
open IntervalSearch RowRule
open LayerCost (seek seek_val seek_cost collect collect_val collect_cost)

def anyM (p : α → Bool × Nat) (xs : List α) : Bool × Nat :=
  let (v,c) := seek p xs
  (v.isSome,c)

theorem anyM_spec (p : α → Bool × Nat) (xs : List α) :
    (anyM p xs).1 = true ↔ ∃ x∈xs,(p x).1=true := by
  simp [anyM,seek_val]

theorem anyM_bound (p : α → Bool × Nat) (xs : List α) (u : Nat)
    (h : ∀x∈xs,(p x).2≤u) : (anyM p xs).2≤xs.length*(u+1)+1 := seek_cost p xs u h

private def cutScan (xs : List Nat) (p : List Nat × List Nat → Bool × Nat) : Bool × Nat :=
  let (v,c) := anyM p (cuts xs)
  -- The recursive enumeration maps cons across each shorter list of cuts.
  (v,c+4*(xs.length+1)^2)

private theorem cutScan_spec (xs) (p : List Nat × List Nat → Bool × Nat) :
    (cutScan xs p).1 = true ↔ ∃ l r, xs=l++r ∧ (p (l,r)).1=true := by
  simp [cutScan,anyM_spec,Prod.exists,cuts_spec]

private def cutBound (b u : Nat) := (b+1)*(u+1)+1+4*(b+1)^2

private theorem cutScan_bound {xs : List Nat} (p : List Nat × List Nat → Bool × Nat) {b u : Nat}
    (hl : xs.length≤b) (h : ∀ l r, xs=l++r → (p (l,r)).2≤u) :
    (cutScan xs p).2 ≤ cutBound b u := by
  have all := anyM_bound p (cuts xs) u (fun ⟨l,r⟩ e => h l r ((cuts_spec ..).1 e))
  simp only [cuts_length] at all
  change (anyM p (cuts xs)).2 + 4*(xs.length+1)^2 ≤ _
  unfold cutBound
  apply Nat.add_le_add (all.trans ?_) ?_ <;> gcongr

private def leaf (b d : Nat) (goal l a mid z r : List Nat) : Bool × Nat :=
  let eligible := decide (a.length≤1 ∧ z.length≤1 ∧ (∀ x∈mid,x=1) ∧ (a++mid++z).length≤d)
  let result := (l ++ (a++mid).map (·-1) ++ (d-(a++mid++z).length) :: (z.map (·-1) ++ r)).filter (0<·)
  -- Tests, construction and entrywise comparison take a constant number
  -- of scans of at most b+1 entries of at most b+1 bits.
  (eligible && result==goal, 40*(b+2)^2)

def checkMove (b : Nat) (row : List Nat) (d : Nat) (goal : List Nat) : Bool × Nat :=
  cutScan row fun (l,s₁) => cutScan s₁ fun (a,s₂) =>
    cutScan s₂ fun (mid,s₃) => cutScan s₃ fun (z,r) => leaf b d goal l a mid z r

theorem matches_spec (b row d goal) :
    (checkMove b row d goal).1=true ↔ goal∈following row d := by
  simp only [checkMove, cutScan_spec,leaf,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,
    following,List.mem_flatMap,List.mem_filterMap,Prod.exists,cuts_spec]
  constructor
  · rintro ⟨l,s₁,h₁,a,s₂,h₂,mid,s₃,h₃,z,r,h₄,ok,e⟩
    exact ⟨l,s₁,h₁,a,s₂,h₂,mid,s₃,h₃,z,r,h₄,by simp only [ite_eq_left ok,Option.some.injEq]; exact e⟩
  · rintro ⟨l,s₁,h₁,a,s₂,h₂,mid,s₃,h₃,z,r,h₄,h⟩
    refine ⟨l,s₁,h₁,a,s₂,h₂,mid,s₃,h₃,z,r,h₄,?_⟩
    split at h
    · exact ⟨by assumption,Option.some.inj h⟩
    · contradiction

private def moveBound (b : Nat) :=
  cutBound b (cutBound b (cutBound b (cutBound b (40*(b+2)^2))))

theorem matches_bound (b row d goal) (h : row.length≤b) :
    (checkMove b row d goal).2 ≤ moveBound b := by
  have suffix {xs l r : List Nat} (sz : xs.length≤b) (e : xs=l++r) : r.length≤b := by
    rw [e,List.length_append] at sz; omega
  apply cutScan_bound _ h; intro l s₁ h₁
  apply cutScan_bound _ (suffix h h₁); intro a s₂ h₂
  apply cutScan_bound _ (suffix (suffix h h₁) h₂); intro mid s₃ h₃
  apply cutScan_bound _ (suffix (suffix (suffix h h₁) h₂) h₃); intros; exact le_rfl

def edge (b : Nat) (prev next : Key) : Bool × Nat :=
  anyM (fun d =>
    if prev.1 = next.1.erase d then
      let (hit,w) := checkMove b prev.2 d next.2
      (hit,w+8*(b+2)^2)
    else (false,8*(b+2)^2)) next.1

theorem edge_val (b prev next) : (edge b prev next).1=advances prev next := by
  apply Bool.eq_iff_iff.mpr
  cases prev with | mk u r =>
    cases next with | mk v s =>
      rw [advances_spec]
      simp only [edge,anyM_spec]
      constructor
      · rintro ⟨d,hd,h⟩
        split at h
        · exact ⟨d,hd,by assumption,(following_spec ..).1 ((matches_spec ..).1 h)⟩
        · contradiction
      · rintro ⟨d,hd,e,m,h⟩
        exact ⟨d,hd,by simpa [e] using (matches_spec b r d s).2 ((following_spec ..).2 ⟨m,h⟩)⟩

private def edgeBound (b : Nat) := b*(moveBound b+8*(b+2)^2+1)+1

theorem edge_bound (b prev next) (hr : prev.2.length≤b) (hu : next.1.length≤b) :
    (edge b prev next).2 ≤ edgeBound b := by
  unfold edge
  apply le_trans (anyM_bound _ _ (moveBound b+8*(b+2)^2) ?_)
  · unfold edgeBound; gcongr
  · intro d _
    split
    · exact Nat.add_le_add_right (matches_bound _ _ _ _ hr) _
    · dsimp; omega

def levels (b : Nat) (keys : List Key) : Nat → List Key × Nat
  | 0 => ([([],[])],1)
  | k+1 =>
    let (prev,w) := levels b keys k
    let (next,c) := collect (fun s =>
      let (hit,cost) := anyM (fun t => edge b t s) prev
      (if hit then some s else none,cost+1)) keys
    (next,w+c+1)

theorem levels_val (b keys k) : (levels b keys k).1=layer keys k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [levels,layer,collect_val,ih]
    have pred (s : Key) :
        (anyM (fun t => edge b t s) (layer keys k)).1=(layer keys k).any (advances · s) := by
      apply Bool.eq_iff_iff.mpr
      simp [anyM_spec,List.any_eq_true,edge_val]
    simp only [pred]
    exact congrFun (List.filterMap_eq_filter (p := fun s => (layer keys k).any (advances · s))) keys

private def layerBudget (b p : Nat) := p*((p+1)*(edgeBound b+1)+3)+2

private theorem positive_length (r : List Nat) (p : ∀ x∈r,0<x) : r.length≤r.sum := by
  induction r with
  | nil => simp
  | cons a r ih =>
    have h := p a (.head _)
    have := ih (fun x hx => p x (.tail _ hx))
    simp; omega

private theorem key_lengths {ds : List Nat} {x : Key} (h : x∈pool ds) :
    x.1.length≤ds.length ∧ x.2.length≤ds.sum := by
  obtain ⟨a,ha,rest⟩ := List.mem_flatMap.mp h
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp rest
  obtain ⟨pos,weight⟩ := rows_sound hr
  exact ⟨(List.mem_sublists'.mp ha).length_le,(positive_length _ pos).trans weight⟩

private theorem prev_size (keys : List Key) (k) : (layer keys k).length≤keys.length+1 := by
  cases k with
  | zero => simp [layer]
  | succ k => exact (List.length_filter_le ..).trans (by omega)

private theorem row_limit {ds} {k} {v : Key} (h : v∈layer (pool ds) k) :
    v.2.length≤ds.sum := by
  cases k with
  | zero => have eq : v=([],[]) := by simpa [layer] using h
            rw [eq]; simp
  | succ k => exact (key_lengths (List.mem_filter.mp h).1).2

theorem levels_cost (ds : List Nat) (k b) (h₁ : ds.length≤b) (h₂ : ds.sum≤b) :
    (levels b (pool ds) k).2 ≤ k*layerBudget b (pool ds).length+1 := by
  induction k with
  | zero => simp [levels]
  | succ k ih =>
    let keys := pool ds
    let previous := (levels b keys k).1
    have prev : previous=layer keys k := levels_val ..
    let test (s : Key) :=
      let (yes,w) := anyM (fun t => edge b t s) previous
      (if yes then some s else none,w+1)
    have one (s) (hs : s∈keys) : (test s).2≤(keys.length+1)*(edgeBound b+1)+2 := by
      have ee := anyM_bound (fun t => edge b t s) previous (edgeBound b)
        (fun t ht => edge_bound b t s ((row_limit (prev ▸ ht)).trans h₂)
          ((key_lengths hs).1.trans h₁))
      have sz : previous.length≤keys.length+1 := prev ▸ prev_size keys k
      have bound := ee.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ sz) 1)
      exact Nat.add_le_add_right bound 1
    have all := collect_cost test keys _ one
    change (levels b keys k).2 + (collect test keys).2 + 1 ≤ _
    change (levels b keys k).2 ≤ _ at ih
    unfold layerBudget at *
    change (collect test keys).2 ≤ (pool ds).length * (((pool ds).length+1)*(edgeBound b+1)+3)+1 at all
    rw [Nat.succ_mul]
    omega

private def subsets : List Nat → List (List Nat) × Nat
  | [] => ([[]],1)
  | a::r => let (old,w) := subsets r; (old ++ old.map (a::·),w+4*(old.length+1))

private theorem subsets_val (ds) : (subsets ds).1=List.sublists' ds := by
  induction ds with
  | nil => rfl
  | cons a r ih => simp [subsets,List.sublists'_cons,ih]

private theorem subsets_cost (ds) : (subsets ds).2≤8*(ds.length+1)*2^ds.length := by
  induction ds with
  | nil => decide
  | cons a r ih =>
    simp only [subsets,subsets_val,List.length_sublists',List.length_cons,pow_succ]
    nlinarith [Nat.one_le_two_pow (n:=r.length)]

private def rowCodes : Nat → List (List Nat) × Nat
  | 0 => ([[]],1)
  | k+1 =>
    let (old,w) := rowCodes k
    ([] :: (old.map (1::·) ++ old.map (fun | [] => [1] | a::r => (a+1)::r)),
      w+8*(old.length+1)*(k+2))

private theorem rowCodes_val (k) : (rowCodes k).1=rows k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rowCodes,rows,ih]; rfl

private theorem rowCodes_cost (k) : (rowCodes k).2≤8*(k+1)^2*2^(k+1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [rowCodes,rowCodes_val,rows_size,pow_succ (a:=2) (n:=k+1)]
    nlinarith [Nat.one_le_two_pow (n:=k+1)]

private def makePool (ds : List Nat) : List Key × Nat :=
  let (sets,w) := subsets ds
  let (rs,c) := rowCodes ds.sum
  (sets.flatMap (fun s => rs.map (s,·)), w+c+4*(sets.length+1)*(rs.length+1))

private theorem makePool_val (ds) : (makePool ds).1=pool ds := by simp [makePool,subsets_val,rowCodes_val,pool]

private def poolBudget (n s : Nat) := 8*(n+1)*2^n+8*(s+1)^2*2^(s+1)+4*(2^n+1)*2^(s+1)

private theorem makePool_cost (ds) : (makePool ds).2≤poolBudget ds.length ds.sum := by
  simp only [makePool,subsets_val,rowCodes_val,List.length_sublists',rows_size,poolBudget]
  gcongr
  · exact subsets_cost _
  · exact rowCodes_cost _

/-- The input has already passed the degree-field check. The volume test is
included; at most two scans are needed to remove zeros and compute the sum.
Lookup compares two explicit lists of entries. -/
def run (ds : List Nat) : Bool × Nat :=
  let n := ds.length
  let prep := 16*(n+2)^3
  if ds.sum≤6*n then
    let xs := ds.filter (0<·)
    let b := xs.length+xs.sum+1
    let (keys,g) := makePool xs
    let (out,c) := levels b keys xs.length
    let (ok,q) := anyM (fun x => (x == (xs,[]),8*(b+2)^2)) out
    (ok,prep+g+c+q+1)
  else (false,prep)

theorem run_correct (ord : CanonicalRow.CanonicalOrderingInput) (ds : List Nat) :
    (run ds).1=true ↔ SparseBoundary.Planaric ds := by
  by_cases h : ds.sum≤6*ds.length
  · simp only [run,ite_eq_left h,makePool_val,levels_val,anyM_spec,beq_iff_eq]
    rw [← accepts_iff ord]
    simp [accepts]
  · have no : ¬ SparseBoundary.Planaric ds := fun yes => h (MainResult.volume yes)
    simp [run,h,no]

/-- A monotone bound expressed in the order, volume, and number of table
keys. It includes the initial and terminal scans and table allocation. -/
private def budget (n s p : Nat) :=
  let b:=n+s+1
  16*(n+2)^3 + poolBudget n s + (n*layerBudget b p+1) +
    ((p+1)*(8*(b+2)^2+1)+1)+1

private theorem total_work (ds : List Nat) :
    (run ds).2≤budget ds.length (6*ds.length) (2^(7*ds.length+1)) := by
  by_cases h : ds.sum≤6*ds.length
  · let xs := ds.filter (0<·)
    have hn : xs.length≤ds.length := List.length_filter_le ..
    have hm : xs.sum≤ds.sum := (List.filter_sublist).sum_le_sum (by simp)
    let b := xs.length+xs.sum+1
    let p := (pool xs).length
    have pv : p ≤ 2^(7*ds.length+1) := by
      have rs := rows_size xs.sum
      change (pool xs).length≤_
      rw [pool_size]
      calc
        _ ≤ 2^xs.length * 2^(xs.sum+1) := Nat.mul_le_mul_left _ (by omega)
        _ = 2^(xs.length+(xs.sum+1)) := (Nat.pow_add ..).symm
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
    have hb : b≤ds.length+6*ds.length+1 := by dsimp [b]; omega
    have l := levels_cost xs xs.length b (by dsimp [b]; omega) (by dsimp [b]; omega)
    have terminal := anyM_bound (fun x : Key => (x == (xs,[]),8*(b+2)^2))
      (layer (pool xs) xs.length) (8*(b+2)^2) (by intros; rfl)
    have out := terminal.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (prev_size ..)) _)
    simp only [run,ite_eq_left h,makePool_val,levels_val]
    change _ + (makePool xs).2 + (levels b (pool xs) xs.length).2 +
      (anyM _ (layer (pool xs) xs.length)).2 + 1 ≤ _
    have combined := Nat.add_le_add_right
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (makePool_cost xs) (16*(ds.length+2)^3)) l) out) 1
    apply le_trans combined
    unfold budget poolBudget layerBudget edgeBound moveBound cutBound
    dsimp only
    gcongr <;> first | exact pv | exact hn | exact hb | exact hm.trans h
  · simp only [run,ite_eq_right h]
    dsimp only [budget]
    omega

private def Exponential (f : Nat → Nat) :=
  ∃ c : Nat, ∀ n, f n ≤ 2^(c*(n+1))

private theorem exp_add {f g : Nat→Nat} (hf : Exponential f) (hg : Exponential g) :
    Exponential (fun n => f n+g n) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  refine ⟨max a b+1,fun n => ?_⟩
  have A : AlgorithmCost.Fits (n*n) a (f n) := by simpa [AlgorithmCost.Fits] using ha n
  have B : AlgorithmCost.Fits (n*n) b (g n) := by simpa [AlgorithmCost.Fits] using hb n
  simpa [AlgorithmCost.Fits] using A.plus B

private theorem exp_mul {f g : Nat→Nat} (hf : Exponential f) (hg : Exponential g) :
    Exponential (fun n => f n*g n) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  refine ⟨a+b,fun n => ?_⟩
  rw [Nat.add_mul,Nat.pow_add]
  exact Nat.mul_le_mul (ha n) (hb n)

private theorem exp_pow {f : Nat→Nat} (e : Nat) (hf : Exponential f) :
    Exponential (fun n => (f n)^e) := by
  obtain ⟨a,ha⟩ := hf
  refine ⟨a*e,fun n => ?_⟩
  rw [show a*e*(n+1)=(a*(n+1))*e by ring,Nat.pow_mul]
  exact Nat.pow_le_pow_left (ha n) e

private theorem exp_const (a : Nat) : Exponential (fun _ => a) :=
  ⟨a,fun n => by simpa [AlgorithmCost.Fits] using AlgorithmCost.constant (n*n) a⟩

private theorem exp_order : Exponential (fun n => n) :=
  ⟨1,fun n => by simp; exact (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))⟩

private theorem majorant : Exponential (fun n => budget n (6*n) (2^(7*n+1))) := by
  have a : Exponential (fun n => 2^n) :=
    ⟨1,fun n => Nat.pow_le_pow_right (by decide) (by omega)⟩
  have b : Exponential (fun n => 2^(6*n+1)) :=
    ⟨6,fun n => Nat.pow_le_pow_right (by decide) (by omega)⟩
  have c : Exponential (fun n => 2^(7*n+1)) :=
    ⟨7,fun n => Nat.pow_le_pow_right (by decide) (by omega)⟩
  dsimp only [budget,poolBudget,layerBudget,edgeBound,moveBound,cutBound]
  repeat first | assumption | exact exp_order | exact exp_const _ |
    apply exp_add | apply exp_mul | apply exp_pow

theorem single_exponential : ∃ C : Nat, ∀ ds : List Nat, (run ds).2≤2^(C*(ds.length+1)) := by
  obtain ⟨C,h⟩ := majorant
  exact ⟨C,fun ds => (total_work ds).trans (h ds.length)⟩

/-- The binary interface first discards malformed or out-of-range fields.
It leaves only integers of at most the input order for all counted scans. -/
def wire (bs : List Bool) : Bool × Nat :=
  let (v,w) := WireSearch.decode bs
  match v with
  | none | some [] => (false,w+1)
  | some (d::ds) => let result := run (d::ds); (result.1,w+result.2+1)

theorem wire_correct (ord : CanonicalRow.CanonicalOrderingInput) (bs : List Bool) :
    (wire bs).1=true ↔ Wire.degreeLanguage SparseBoundary.Planaric bs := by
  have val := (WireSearch.decode_work bs).1
  cases eq : (WireSearch.decode bs).1 with
  | none =>
    have miss := val.symm.trans eq
    simp only [wire,eq,Bool.false_eq_true,false_iff]
    rintro ⟨ds,h,_,yes⟩
    have ok := (WireSearch.parse_exact ..).2 ⟨h,WireSearch.degrees_fit yes⟩
    rw [miss] at ok
    contradiction
  | some ds =>
    have raw := ((WireSearch.parse_exact ..).1 (val.symm.trans eq)).1
    cases ds with
    | nil => simp [wire,eq,Wire.degreeLanguage,raw]
    | cons d ds => simp [wire,eq,Wire.degreeLanguage,raw,run_correct ord]

theorem wire_cost : ∃ C : Nat, ∀ bs : List Bool,
    (wire bs).2 ≤ 6*bs.length+3+2^(C*(WireSearch.arity bs+1)) := by
  obtain ⟨C,H⟩ := single_exponential
  refine ⟨C,fun bs => ?_⟩
  obtain ⟨value,cost⟩ := WireSearch.decode_work bs
  have early : (WireSearch.decode bs).2+1 ≤ 6*bs.length+3 := by omega
  cases eq : (WireSearch.decode bs).1 with
  | none => simpa only [wire,eq] using early.trans (Nat.le_add_right _ (2^(C*(WireSearch.arity bs+1))))
  | some ds =>
    have order := WireSearch.arity_eq bs (((WireSearch.parse_exact ..).1 (value.symm.trans eq)).1)
    cases ds with
    | nil => simpa only [wire,eq] using early.trans (Nat.le_add_right _ (2^(C*(WireSearch.arity bs+1))))
    | cons d ds =>
      have bound := H (d::ds)
      rw [order]
      simp only [wire,eq]; omega

end Recognition.IntervalCosts
