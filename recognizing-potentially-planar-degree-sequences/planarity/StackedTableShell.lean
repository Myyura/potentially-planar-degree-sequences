import StackedTable

namespace Recognition.StackedTable
open StackedQuota

def quotas (n : Nat) := (List.range (n+1)).flatMap fun a =>
  (List.range (n+1)).flatMap fun b => (List.range (n+1)).map fun c => Quota.mk a b c

theorem mem_quotas (n : Nat) (s : Quota) :
    s∈quotas n ↔ s.a≤n ∧ s.b≤n ∧ s.c≤n := by
  cases s
  simp [quotas, Nat.lt_succ_iff]

def cornerPart (p q r : Record) (s : Quota) : Multiset Nat :=
  (corners p.quota q.quota r.quota s : Multiset Nat)+p.profile+q.profile+r.profile

/-- The fourth multiset is uniquely determined by the other choices. -/
def lastDisk (d : Multiset Nat) (t : Table) (p q r : Record) (s : Quota) : Bool :=
  let used := cornerPart p q r s
  decide (used≤d) && t.index.get (key ⟨s,d-used⟩)

def shells (d : Multiset Nat) (t : Table) : Bool :=
  let qs := quotas d.card
  t.rows.any fun p => t.rows.any fun q => t.rows.any fun r =>
    qs.any (lastDisk d t p q r)

theorem shells_iff (d : Multiset Nat) :
    shells d (table d (d.card-4))=true ↔ Accepts d := by
  simp only [shells,List.any_eq_true, lastDisk, Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨p,mp,q,mq,r,mr,s,_,fit,last⟩
    have mem := ((table_valid d (d.card-4)).2 _).mp last
    exact ⟨_,_,_,_,_,_,_,_,(sound mp).1,(sound mq).1,(sound mr).1,(sound mem).1,
      (add_tsub_cancel_of_le fit).symm⟩
  · rintro ⟨p,q,r,s,P,Q,R,S,hp,hq,hr,hs,hd⟩
    let a : Record := ⟨p,P⟩
    let b : Record := ⟨q,Q⟩
    let c : Record := ⟨r,R⟩
    let u := cornerPart a b c s
    change d=u+S at hd
    have uf : u≤d := hd ▸ Multiset.le_add_right .. 
    have sf : S≤d := hd ▸ Multiset.le_add_left ..
    have pf : P≤u := ((Multiset.le_add_left P _).trans (Multiset.le_add_right _ _)).trans (Multiset.le_add_right _ _)
    have qf : Q≤u := (Multiset.le_add_left Q _).trans (Multiset.le_add_right _ _)
    have rf : R≤u := Multiset.le_add_left .. 
    have sz := congrArg Multiset.card hd
    change d.card=(((corners p q r s : Multiset Nat)+P+Q+R)+S).card at sz
    simp only [Multiset.card_add,corners,Multiset.coe_card,List.length_cons,List.length_nil] at sz
    have member {x F} (h : Rule x F) (f : F≤d) (shallow : F.card≤d.card-4) :=
      complete h f (d.card-4) shallow
    obtain ⟨sa,sb,sc⟩ := quota_bound hs
    have small := Multiset.card_le_card sf
    refine ⟨a,member hp (pf.trans uf) (by omega),b,member hq (qf.trans uf) (by omega),c,member hr (rf.trans uf) (by omega),
      s,(mem_quotas ..).mpr ⟨by omega,by omega,by omega⟩,uf,?_⟩
    apply ((table_valid ..).2 _).mpr
    change (⟨s,d-u⟩ : Record)∈_
    have eq : d-u=S := by rw [hd]; simp
    rw [eq]
    exact member hs sf (by omega)

theorem budget_rule {x F} (r : Rule x F) :
    F.sum+x.a+x.b+x.c=6*F.card ∧ ∀ a∈F, 3≤a ∧ a≤F.card+2 := by
  induction r with
  | empty => simp
  | @split p q s P Q S k hp hq hs e lp lq ls =>
    subst k
    have p' := quota_bound hp
    have q' := quota_bound hq
    have s' := quota_bound hs
    simp only [merge,Multiset.sum_add,Multiset.sum_singleton,Multiset.card_add,Multiset.card_singleton,
      Multiset.mem_add, Multiset.mem_singleton]
    refine ⟨by omega, ?_⟩
    intro a mem
    rcases mem with (((eq|m)|m)|m)
    · omega
    · have := lp.2 _ m; omega
    · have := lq.2 _ m; omega
    · have := ls.2 _ m; omega

theorem checks_of_accepts {d : Multiset Nat} (h : Accepts d) :
    4≤d.card ∧ d.sum+12=6*d.card ∧ ∀ a∈d, 3≤a ∧ a<d.card := by
  obtain ⟨p,q,r,s,P,Q,R,S,hp,hq,hr,hs,rfl⟩ := h
  have p' := quota_bound hp
  have q' := quota_bound hq
  have r' := quota_bound hr
  have s' := quota_bound hs
  have hp' := budget_rule hp
  have hq' := budget_rule hq
  have hr' := budget_rule hr
  have hs' := budget_rule hs
  simp only [corners, Multiset.card_add,Multiset.coe_card, List.length_cons,List.length_nil,
    Multiset.sum_add,Multiset.sum_coe,List.sum_cons,List.sum_nil,Multiset.mem_add,
    Multiset.mem_coe,List.mem_cons,List.not_mem_nil,or_false]
  refine ⟨by omega,by omega,?_⟩
  intro a m
  rcases m with ((((m|m)|m)|m)|m)
  · rcases m with eq|eq|eq|eq <;> omega
  · have := hp'.2 _ m; omega
  · have := hq'.2 _ m; omega
  · have := hr'.2 _ m; omega
  · have := hs'.2 _ m; omega

def checks (ds : List Nat) : Bool :=
  decide (4≤ds.length) && ds.all (fun v => decide (3≤v ∧ v<ds.length)) &&
    decide (ds.sum+12=6*ds.length)

theorem checks_spec (ds : List Nat) :
    checks ds=true ↔ 4≤ds.length ∧ ds.sum+12=6*ds.length ∧ ∀ a∈ds, 3≤a ∧ a<ds.length := by
  simp only [checks, Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  tauto

def recognize (ds : List Nat) : Bool :=
  if checks ds then shells ds (table ds (ds.length-4)) else false

theorem recognize_iff (ds : List Nat) :
    recognize ds=true ↔ StackedHistory.SequentialRealization ds := by
  rw [←StackedHistory.accepts_iff_sequential]
  unfold recognize
  split
  · exact shells_iff _
  next no =>
    simp only [Bool.false_eq_true,false_iff]
    intro h
    exact no ((checks_spec ds).mpr (checks_of_accepts h))

end Recognition.StackedTable
