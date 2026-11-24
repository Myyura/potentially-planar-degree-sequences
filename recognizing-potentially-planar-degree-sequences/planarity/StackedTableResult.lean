import StackedTableCost
import AlgorithmCost

namespace Recognition.StackedTable
open StackedQuota AlgorithmCost

/-- One layer's metered traversal. The list generation charge includes all
outer-loop cells, including empty inner loops. Profile copying is charged by
`place` for each generated triple, whether or not its profile fits. -/
def build (ds : List Nat) : Nat → Table × Nat
  | 0 => (insert blank base,20)
  | k+1 =>
    let p := build ds k
    let q := gatherWork ds p.1 (proposals p.1.rows)
    (q.1, p.2+q.2+8*(p.1.rows.length+1)^3)

private def B (ds : List Nat) := profileCount ds*(ds.length+1)^3
private def phase (ds : List Nat) := (B ds+1)^3*(1000000*(ds.length+2)^4+20)

private theorem build_spec (ds : List Nat) (vol : ds.sum≤6*ds.length) (k : Nat) :
    (build ds k).1=table ds k ∧ (build ds k).2≤(k+1)*phase ds := by
  induction k with
  | zero =>
    refine ⟨rfl,?_⟩
    simp only [build,Nat.zero_add,Nat.one_mul]
    unfold phase
    have pow := Nat.one_le_pow' 3 (B ds)
    exact (show 20≤1000000*(ds.length+2)^4+20 by omega).trans (Nat.le_mul_of_pos_left _ pow)
  | succ k ih =>
    obtain ⟨out,old⟩ := ih
    have g := gather_work_spec (ds : Multiset Nat) (table ds k) (proposals (table ds k).rows) ds.length
      (by simp) vol (fun _ mem => proposal_span ds k mem)
    rw [proposals_length] at g
    have len : (table ds k).rows.length≤B ds := table_size ds k
    have left := Nat.pow_le_pow_left (len.trans (Nat.le_succ _)) 3
    have right := Nat.pow_le_pow_left (Nat.succ_le_succ len) 3
    have pos := Nat.one_le_pow' 3 (B ds)
    simp only [build,out,table,g.1,true_and]
    rw [Nat.succ_mul]
    apply (Nat.add_le_add_right (Nat.add_le_add old g.2) _).trans
    unfold phase
    nlinarith [Nat.mul_le_mul_right (1000000*(ds.length+2)^4+2) left]

abbrev Query := Record × Record × Record × Quota

def queries (n : Nat) (t : Table) : List Query :=
  t.rows ×ˢ (t.rows ×ˢ (t.rows ×ˢ quotas n))

theorem query_length (n t) : (queries n t).length=t.rows.length^3*(n+1)^3 := by
  simp [queries,quotas_length,List.length_product]; ring

def probeShell (d : Multiset Nat) (t : Table) (query : Query) : Bool × Nat :=
  let (p,q,r,s) := query
  let u := cornerPart p q r s
  let c := eraseCost u d
  let alloc := 8*(u.card+u.sum+1)
  if u≤d then
    let w : Record := ⟨s,d-u⟩
    let z := t.index.probe (key w)
    (z.1, alloc+2*c+keyCost w+z.2+4)
  else (false,alloc+c+1)

theorem probeShell_value (d t) (x : Query) :
    (probeShell d t x).1=lastDisk d t x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  obtain ⟨p,q,r,s⟩:=x
  by_cases fit : cornerPart p q r s≤d <;> simp [probeShell,lastDisk,fit,Trie.probe_spec]

private theorem sum_mono {a b : Multiset Nat} (h : a≤b) : a.sum≤b.sum := by
  obtain ⟨x,eq⟩ := Multiset.le_iff_exists_add.mp h
  simp [eq]

theorem probeShell_cost (ds : List Nat) (vol : ds.sum≤6*ds.length) (k : Nat)
    {x : Query} (m : x∈queries ds.length (table ds k)) :
    (probeShell ds (table ds k) x).2≤1000000*(ds.length+2)^4 := by
  let n := ds.length
  let d : Multiset Nat := ds
  obtain ⟨p,q,r,s⟩:=x
  simp only [queries,List.mem_product,mem_quotas] at m
  obtain ⟨mp,mq,mr,bound⟩:=m
  have P := sound mp; have Q := sound mq; have R := sound mr
  have ps := Multiset.card_le_card P.2; have qs := Multiset.card_le_card Q.2; have rs := Multiset.card_le_card R.2
  have pa := rule_span P.1; have qa := rule_span Q.1; have ra := rule_span R.1
  let u := cornerPart p q r s
  have us : u.card≤3*n+4 := by
    simp only [u,cornerPart,Multiset.card_add,corners,Multiset.coe_card,List.length_cons,List.length_nil]
    change p.profile.card≤n at ps; change q.profile.card≤n at qs; change r.profile.card≤n at rs
    omega
  have uw : u.sum≤21*n+12 := by
    simp only [u,cornerPart,Multiset.sum_add,corners,Multiset.sum_coe,List.sum_cons,List.sum_nil]
    change p.profile.card≤n at ps; change q.profile.card≤n at qs; change r.profile.card≤n at rs
    change s.a≤n ∧ s.b≤n ∧ s.c≤n at bound
    omega
  let w : Record := ⟨s,d-u⟩
  have wc : w.profile.card≤n := Multiset.card_le_card (tsub_le_self : d-u≤d)
  have ws : w.profile.sum≤6*n := (sum_mono (tsub_le_self : d-u≤d)).trans vol
  have width : (key w).length≤10*n+3 := by
    rw [key_size,span]; change (d-u).card+(d-u).sum+s.a+s.b+s.c+1+2 ≤ _
    change (d-u).card≤n at wc; change (d-u).sum≤6*n at ws
    change s.a≤n ∧ s.b≤n ∧ s.c≤n at bound
    omega
  have look := (Trie.probe_spec (table ds k).index (key w)).2
  have ec : eraseCost u d≤(3*n+5)*(n+1)*(27*n+14) := by
    unfold eraseCost; change d.sum≤6*n at vol
    change (u.card+1)*(n+1)*(u.sum+d.sum+2)≤_
    exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) (by omega)
  have kc : keyCost w≤(n+1)^2*(6*n+1)+3*(10*n+4) := by
    exact Nat.add_le_add (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.succ_le_succ wc) _) (Nat.succ_le_succ ws))
      (Nat.mul_le_mul_left 3 (by omega))
  have cap : 8*((3*n+4)+(21*n+12)+1)+2*((3*n+5)*(n+1)*(27*n+14))+
      ((n+1)^2*(6*n+1)+3*(10*n+4))+(10*n+4)+4 ≤ 1000000*(n+2)^4 := by
    nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4)]
  change (if u≤d then ((_,8*(u.card+u.sum+1)+2*eraseCost u d+keyCost w+((table ds k).index.probe (key w)).2+4) : Bool × Nat)
      else (false,8*(u.card+u.sum+1)+eraseCost u d+1)).2 ≤ 1000000*(n+2)^4
  split <;> simp only <;> omega

/-- Tail-recursive first-hit scan, including rejected queries. -/
def scan (test : α → Bool × Nat) (acc : Nat) : List α → Bool × Nat
  | [] => (false,acc+1)
  | x::xs =>
    let z := test x
    if z.1 then (true,acc+z.2+1) else scan test (acc+z.2+1) xs

theorem scan_spec (test : α → Bool × Nat) (xs : List α) (acc : Nat) :
    (scan test acc xs).1=(xs.any fun x => (test x).1) ∧
      (scan test acc xs).2=acc+(LayerCost.seek test xs).2 := by
  induction xs generalizing acc with
  | nil => simp [scan,LayerCost.seek]
  | cons x xs ih =>
    cases h : (test x).1
    · simp only [scan,h,Bool.false_eq_true,ite_false,LayerCost.seek,List.any_cons,Bool.false_or]
      exact ⟨(ih _).1,by rw [(ih _).2]; omega⟩
    · simp [scan,LayerCost.seek,h,Nat.add_assoc]

def finish (ds : List Nat) (t : Table) : Bool × Nat :=
  let xs := queries ds.length t
  let z := scan (probeShell ds t) 0 xs
  (z.1,z.2+8*(xs.length+(t.rows.length+1)^3+(ds.length+1)^3+1))

theorem finish_value (ds : List Nat) (t : Table) : (finish ds t).1=shells ds t := by
  apply Bool.eq_iff_iff.mpr
  simp only [finish,(scan_spec ..).1,List.any_eq_true,
    shells,Multiset.coe_card,queries,probeShell_value]
  constructor
  · rintro ⟨⟨p,q,r,s⟩,mem,yes⟩
    obtain ⟨hp,hq,hr,hs⟩ := (show p∈t.rows ∧ q∈t.rows ∧ r∈t.rows ∧ s∈quotas ds.length from by simpa using mem)
    exact ⟨p,hp,q,hq,r,hr,s,hs,yes⟩
  · rintro ⟨p,hp,q,hq,r,hr,s,hs,yes⟩
    exact ⟨⟨p,q,r,s⟩,by simpa using And.intro hp ⟨hq,hr,hs⟩,yes⟩

/-- Prechecks run before any disk is generated. Each input field has already
been read. Comparing its stored length to the size bound permits immediate
rejection of an oversize field; summation is performed only on bounded fields. -/
def run (ds : List Nat) : Bool × Nat :=
  let c := 12*(ds.length+2)^3
  if checks ds then
    let t := build ds (ds.length-4)
    let z := finish ds t.1
    (z.1,c+t.2+z.2)
  else (false,c)

theorem run_iff (ds : List Nat) : (run ds).1=true ↔ StackedHistory.SequentialRealization ds := by
  rw [←recognize_iff]
  by_cases check : checks ds=true
  · obtain ⟨_,mass,_⟩ := (checks_spec ds).mp check
    simp [run,recognize,check,(build_spec ds (by omega) (ds.length-4)).1,finish_value]
  · simp [run,recognize,check]


private def slots (ds : List Nat) := (B ds+1)^3*(ds.length+2)^3

private theorem parts_le_slots (ds : List Nat) (k : Nat) :
    (queries ds.length (table ds k)).length≤slots ds ∧
    ((table ds k).rows.length+1)^3≤slots ds ∧ (ds.length+1)^3≤slots ds ∧ 1≤slots ds := by
  have len : (table ds k).rows.length≤B ds := table_size ds k
  have b := Nat.one_le_pow' 3 (B ds)
  have n := Nat.one_le_pow' 3 (ds.length+1)
  unfold slots
  rw [query_length]
  exact ⟨Nat.mul_le_mul (Nat.pow_le_pow_left (len.trans (Nat.le_succ _)) _) (Nat.pow_le_pow_left (by omega) _),
    (Nat.pow_le_pow_left (Nat.succ_le_succ len) _).trans (Nat.le_mul_of_pos_right _ n),
    (Nat.pow_le_pow_left (show ds.length+1≤ds.length+2 by omega) 3).trans (Nat.le_mul_of_pos_left _ b),
    Nat.mul_pos b n⟩

private theorem finish_cost (ds : List Nat) (vol : ds.sum≤6*ds.length) (k : Nat) :
    (finish ds (table ds k)).2 ≤ slots ds*(1000000*(ds.length+2)^4+40) := by
  obtain ⟨a,b,c,h⟩ := parts_le_slots ds k
  have f := LayerCost.seek_cost (probeShell ds (table ds k)) (queries ds.length (table ds k))
    (1000000*(ds.length+2)^4) (fun _ m => probeShell_cost ds vol k m)
  simp only [finish,(scan_spec ..).2,Nat.zero_add]
  change (LayerCost.seek _ _).2+8*((queries ds.length (table ds k)).length+((table ds k).rows.length+1)^3+(ds.length+1)^3+1)≤_
  nlinarith [Nat.mul_le_mul_right (1000000*(ds.length+2)^4+1) a]

private theorem build_cost (ds : List Nat) (vol : ds.sum≤6*ds.length) :
    (build ds (ds.length-4)).2 ≤ slots ds*(1000000*(ds.length+2)^4+20) := by
  apply (build_spec ds vol (ds.length-4)).2.trans
  apply (Nat.mul_le_mul_right _ (show ds.length-4+1≤ds.length+1 by omega)).trans
  unfold slots phase
  rw [←Nat.mul_assoc, Nat.mul_comm (ds.length+1)]
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left
  exact (Nat.le_succ _).trans (Nat.le_self_pow (by decide : 3≠0) _)

private theorem count_pos (ds : List Nat) : 1≤profileCount ds := by
  apply Finset.card_pos.mpr
  exact ⟨0,Finset.mem_Iic.mpr zero_le⟩

private theorem slots_bound (ds : List Nat) :
    slots ds ≤ 8*profileCount ds^3*(ds.length+2)^12 := by
  have pos := count_pos ds
  have n := Nat.one_le_pow' 3 ds.length
  have b : 1≤B ds := Nat.mul_pos pos n
  have h : B ds+1≤2*(profileCount ds*(ds.length+2)^3) := by
    have upper : B ds≤profileCount ds*(ds.length+2)^3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  apply (Nat.mul_le_mul_right ((ds.length+2)^3) (Nat.pow_le_pow_left h 3)).trans
  exact le_of_eq (by ring)

/-- Runtime after the input fields have been read, with M the product of
one plus each degree multiplicity. -/
theorem cost (ds : List Nat) :
    (run ds).2 ≤ 100000000*(ds.length+2)^16*(profileCount ds)^3 := by
  let n := ds.length
  let m := profileCount ds
  have pow : 1≤(n+2)^4 := Nat.one_le_pow' _ _
  have pow3 : (n+2)^3≤(n+2)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  have size := (parts_le_slots ds 0).2.2.2
  have base : 12*(n+2)^3 ≤ slots ds*(12*(n+2)^4) :=
    (Nat.mul_le_mul_left _ pow3).trans (Nat.le_mul_of_pos_left _ size)
  have big : slots ds*(2100000*(n+2)^4) ≤ 100000000*(n+2)^16*m^3 := by
    apply (Nat.mul_le_mul_right _ (slots_bound ds)).trans
    change (8*m^3*(n+2)^12)*(2100000*(n+2)^4) ≤ _
    rw [show (8*m^3*(n+2)^12)*(2100000*(n+2)^4) = 16800000*(n+2)^16*m^3 by ring]
    gcongr; decide
  unfold run
  split
  next yes =>
    obtain ⟨_,mass,_⟩ := (checks_spec ds).mp yes
    have vol : ds.sum≤6*ds.length := by omega
    change 12*(n+2)^3 + (build ds (ds.length-4)).2 + (finish ds (build ds (ds.length-4)).1).2 ≤ _
    rw [(build_spec ds vol (ds.length-4)).1]
    apply le_trans _ big
    have bc := build_cost ds vol
    have fc := finish_cost ds vol (ds.length-4)
    change (build ds (ds.length-4)).2 ≤ slots ds*(1000000*(n+2)^4+20) at bc
    change (finish ds (table ds (ds.length-4))).2 ≤ slots ds*(1000000*(n+2)^4+40) at fc
    have charges : 12*(n+2)^4+(1000000*(n+2)^4+20)+(1000000*(n+2)^4+40)≤2100000*(n+2)^4 := by omega
    nlinarith [Nat.mul_le_mul_left (slots ds) charges]
  next no =>
    apply base.trans ((Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by decide : 12≤2100000))).trans big)

theorem fixed_types (ds : List Nat) :
    (run ds).2 ≤ 100000000*(ds.length+2)^(16+3*ds.toFinset.card) := by
  apply (cost ds).trans
  have h := (profileCount_fixed ds).trans (Nat.pow_le_pow_left (show ds.length+1≤ds.length+2 by omega) _)
  rw [pow_add, Nat.mul_comm 3, Nat.pow_mul,←Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

theorem sqrt_cost (ds : List Nat) : Fits ds.length 100000102 (run ds).2 := by
  by_cases yes : checks ds=true
  · obtain ⟨_,mass,degs⟩ := (checks_spec ds).mp yes
    have m : Fits ds.length 18 (profileCount ds) :=
      profileCount_sqrt ds (fun a ha => (degs a ha).1.trans_lt' (by decide)) (by omega)
    have f := Fits.prod (polynomial ds.length 100000000 16) (Fits.pow 3 m)
    have eq : 100000000+3*16+18*3=100000102 := by decide
    rw [eq] at f
    exact (cost ds).trans f
  · have small := polynomial ds.length 12 3
    simp only [run,yes]
    have ex : 12+3*3≤100000102 := by decide
    exact small.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ ex))

end Recognition.StackedTable
