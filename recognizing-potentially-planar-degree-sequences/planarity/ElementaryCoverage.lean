import ShadowRoutes
import CoveredOrder

/-! The zero-error compression can discard large comparison graphs and
patterns without a narrow elimination order. Only the retained table keys
on an accepting order need witnesses. -/
namespace Recognition.ElementaryCoverage
open QuotientDP PlanarDegrees.Frontier PlanarDegrees.FrontierStep PlanarDegrees.Topology
open OverlayCoverage BoundaryState ShortBoundary Witness

def budget (n : Nat) := 6600*(n.sqrt+1)
def width (n : Nat) := 84*((budget n).sqrt+1)

private def size (t : State n) := (StateIncidence.names t).length+
  (SparseCompare.blocks (StateIncidence.graph t)).length

private theorem size_eq {r t : State n} (same : Same r t) : size r=size t := by
  obtain ⟨p,_,_⟩ := (SparseCompare.graph_iff _ _).mpr (((StateIncidence.same_iff r t).mp same).2.2.2)
  simpa [size] using Fintype.card_congr p

private theorem active_le (s : Inventory) :
    (activeNames s).eraseDups.length≤activeCost s := by
  have aux (xs : List Nat) : xs.length≤(xs.map (fun v => cost (s.redDegree v))).sum := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.length_cons,List.map_cons,List.sum_cons];unfold cost at *;omega
  exact aux _

/-- Any table predicate which admits the small, narrow entries retains a
complete accepting path. The fixed width depends only on the input length. -/
theorem path (x : Nat) (ds : List Nat) (C : ClosedTrace ds.length f)
    (terminal : f+1+4=2*(ds.length+1)) (degrees : (witnessDegrees C).Perm (x::ds))
    (sep : SeparatorInput.WeightedPlanarSeparator) (keep : State (ds.length+1) → Bool)
    (retained : ∀ t, (StateIncidence.names t).length+(SparseCompare.blocks (StateIncidence.graph t)).length≤budget (ds.length+1) →
      MinorWidth.Hierarchy (SparseCompare.graph (StateIncidence.graph t)) (width (ds.length+1)) → keep t=true) :
    ∃ t : State (ds.length+1), Table.Path Same ((catalogue (x::ds)).filter keep)
      (successors (f+1)) (start ((x::ds : List Nat) : Multiset Nat)) (f+1) t ∧ finished (f+1) t := by
  classical
  obtain ⟨D,_,_,dc,col,color⟩ := OrderInput.repainted_trace C (Equiv.refl _)
  have weighted := SeparatorInput.host sep D terminal (fun v => cost (simpleDegree D.ledger.sealed v))
    (by intro i hi;simp [cost])
  obtain ⟨seq,perm,ordered⟩ := bounded_codes_permuted D terminal D.ledger.sealed
    (fun i _ h _ => ShortBoundary.seen D i h) (ShortBoundary.hostMass D terminal) weighted
  obtain ⟨fs,U,s,rows,run,done⟩ := OrderInput.literal_run D terminal col color seq.reverse ((List.reverse_perm _).trans perm)
  have target : (witnessDegrees D : Multiset Nat)=((x::ds : List Nat) : Multiset Nat) := Multiset.coe_eq_coe.mpr (dc ▸ degrees)
  rw [target] at run
  have len : fs.length=f+1 := by
    have a := congrArg List.length rows
    have b := perm.length_eq
    simp only [List.length_reverse,List.length_map,List.length_ofFn] at a b;omega
  suffices actual : Table.Path Same ((catalogue (x::ds)).filter keep) (successors (f+1))
      (start ((x::ds : List Nat) : Multiset Nat)) fs.length (prune s) from ⟨prune s,by rwa [len] at actual,done⟩
  apply cover_path _ run
  intro tail U t suffix subrun
  obtain ⟨past,eq⟩ := suffix
  have orderEq : seq=(tail.map FullDegrees.row).reverse++(past.map FullDegrees.row).reverse := by
    have h := congrArg List.reverse rows.symm
    simpa [←eq,List.map_append,List.reverse_append] using h
  let read := tail.map FullDegrees.row
  let todo := (past.map FullDegrees.row).reverse
  have permute : (read++todo).Perm (List.ofFn D.faces) := ((List.reverse_perm read).symm.append_right todo).trans (orderEq ▸ perm)
  obtain ⟨led,ok,bs,covered,short,sz⟩ := ordered _ _ orderEq read (List.reverse_perm _).symm
  obtain ⟨led',ok',M⟩ := CatalogueRun.model_of_run subrun
  rw [ok] at ok'
  obtain rfl := Option.some.inj ok'
  have bound (u) (h : live led u) : u<(x::ds).length := ShortBoundary.bounds D read todo permute ok h
  obtain ⟨d,code,same⟩ := state_round_trip covered ok bound (prune t) M
  have inCatalogue : d∈catalogue (x::ds) := by
    apply table_mem.mpr
    refine ⟨bs,t.remaining,t.used,t.faces,BoundaryState.length_cut _ _ _ short sz,
      (ResidualTable.mem_table ..).mpr ?_,?_,?_,code⟩
    · rw [←FullDegrees.histogram subrun];exact Multiset.le_add_right ..
    · rw [(FullDegrees.facts subrun).used];simpa using U.card_le_univ
    · have hist := (FullDegrees.facts subrun).faces
      have listEq := congrArg List.length eq
      simp only [List.length_append,List.length_cons] at *;omega
  have geom := ShadowRoutes.prefix_hierarchy D terminal read todo permute ok M sep
  obtain ⟨num,⟨H⟩⟩ := geom
  let b := (activeNames led).eraseDups.length
  let n := ds.length+1
  have bw : b≤220*(n.sqrt+1) := by
    have le := active_le led
    have sh := Nat.lt_succ_sqrt n
    change _ ≤ 220^2*n at sz
    change b≤activeCost led at le
    nlinarith
  have graphSize : size d≤budget n := by
    rw [size_eq same]; change size (prune t)≤6600*(n.sqrt+1)
    change size (prune t)≤30*b at num
    omega
  have generous : 10*b≤budget n := by dsimp [budget];omega
  have widen : 84*((10*b).sqrt+1)≤width n := by
    unfold width;exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.sqrt_le_sqrt generous) _)
  let H' : MinorWidth.Hierarchy (SparseCompare.graph (StateIncidence.graph (prune t))) (width n) :=
    { H with cap := fun k => (H.cap k).trans widen }
  obtain ⟨D'⟩ := ShadowRoutes.same_transfer same H'
  exact ⟨d,List.mem_filter.mpr ⟨inCatalogue,retained d graphSize D'⟩,equivalence.symm same⟩

end Recognition.ElementaryCoverage
