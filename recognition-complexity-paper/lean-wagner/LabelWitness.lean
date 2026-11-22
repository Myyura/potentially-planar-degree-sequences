import FullDegrees
import TracePlanarity
import SparseBoundary.GraphPerm

/-! Match equal degrees to the input positions by consuming vertices in
their original order. This preserves isolates and repeated degrees. -/
namespace Recognition.LabelWitness
open SparseBoundary Recognition.QuotientDP PlanarDegrees.Frontier Recognition.Witness

def positions (value : Fin n → Nat) : List Nat → List (Fin n) → Option (List (Fin n))
  | [],vs => if vs.isEmpty then some [] else none
  | a::as,vs => do
    let x ← vs.find? (fun x => value x==a)
    let tail ← positions value as (vs.erase x)
    return x::tail

private theorem matched (value : Fin n → Nat) (ds : List Nat) (vs : List (Fin n))
    (p : (vs.map value).Perm ds) :
    ∃ out,positions value ds vs=some out ∧ out.Perm vs ∧ out.map value=ds := by
  induction ds generalizing vs with
  | nil =>
    have eq : vs=[] := List.length_eq_zero_iff.mp (by simpa using p.length_eq)
    subst vs; exact ⟨[],rfl,.nil,rfl⟩
  | cons a as ih =>
    have mem := p.mem_iff.mpr (List.mem_cons_self (a := a) (l := as))
    obtain ⟨z,mz,az⟩ := List.mem_map.mp mem
    have someX : (vs.find? (fun x => value x==a)).isSome :=
      List.isSome_find?.trans (List.any_eq_true.mpr ⟨z,mz,beq_iff_eq.mpr az⟩)
    obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp someX
    have v := beq_iff_eq.mp (List.find?_some (p := fun x => value x==a) hx)
    have split := List.perm_cons_erase (List.mem_of_find?_eq_some hx)
    have q := (split.map value).symm.trans p
    simp only [List.map_cons,v,List.perm_cons] at q
    obtain ⟨out,get,order,labels⟩ := ih (vs.erase x) q
    exact ⟨x::out,by simp [positions,hx,get],(order.cons x).trans split.symm,by simp [v,labels]⟩

def relabel (G : Graph n) (ds : List Nat) : Option (Graph ds.length) := do
  let out ← positions G.degree ds (List.finRange n)
  if eq : out.length=ds.length then return G.restrict (fun i => out[i.val]'(by omega))
  else none

theorem relabel_correct (G : Graph n) (ds : List Nat) (planar : G.Planar)
    (p : ((List.finRange n).map G.degree).Perm ds) :
    ∃ H,relabel G ds=some H ∧ H.Planar ∧ H.Realizes ds := by
  obtain ⟨out,hit,perm,labels⟩ := matched G.degree ds (List.finRange n) p
  have len : out.length=ds.length := by simpa using congrArg List.length labels
  let f (i : Fin ds.length) := out[i.val]'(by omega)
  have inject : Function.Injective f := by
    intro i j eq
    have nd := perm.nodup_iff.mpr (List.nodup_finRange n)
    exact Fin.ext (congrArg (@Fin.val out.length) (List.nodup_iff_injective_get.mp nd
      (a₁ := ⟨i.val,by omega⟩) (a₂ := ⟨j.val,by omega⟩) eq))
  have all : (List.finRange ds.length).map f=out := by
    apply List.ext_getElem <;> simp [f,len]
  refine ⟨G.restrict f,by simp [relabel,hit,len,f],Graph.planar_restrict planar _ (fun _ _ => @inject _ _),?_⟩
  intro i
  have count := (((List.Perm.of_eq all).trans perm).filter (G.adj (f i))).length_eq
  have adj : (G.restrict f).adj i=(G.adj (f i)) ∘ f := funext (Graph.restrict_adj G f i)
  have degree : (G.restrict f).degree i=G.degree (f i) := by
    rw [List.filter_map,List.length_map] at count
    simpa only [Graph.degree,adj] using count
  rw [degree]
  have atI := congrArg (fun a : List Nat => a[i.val]?) labels
  simpa [f,List.getElem?_map,i.isLt,show i.val<out.length by omega] using atI

def redGraph (fs : List (Triangle n)) := Witness.graph n (reds (FullDegrees.rows fs))

/-- Reconstruct the red graph of this very accepting run and give each
vertex a label carrying its prescribed input degree. -/
theorem output_graph {v f : Nat} (ds : List Nat) {fs : List (Triangle (v+1))} {s : State (v+1)}
    {U : Finset (Fin (v+1))} (run : FullRun (f+1) (ds : Multiset Nat) fs U s)
    (done : finished (f+1) s) (count : f+1+4=2*(v+1)) :
    ∃ H,relabel (redGraph fs) ds=some H ∧ H.Planar ∧ H.Realizes ds := by
  obtain ⟨C,_,trace⟩ := FullDegrees.terminal_trace run done
  have same : witnessGraph C=redGraph fs := by simp [witnessGraph,redGraph,trace]
  have pg := Graph.planar_subgraph_map (TracePlanarity.host_planar C count) id
    (fun _ _ eq => eq) (Witness.red_subgraph C)
  apply relabel_correct _ _ (same ▸ pg)
  have val (x : Fin (v+1)) : (redGraph fs).degree x=simpleDegree (reds (FullDegrees.rows fs)) x.val := by
    rw [←same,witness_degree]
    simpa only [trace] using (replay_accurate C.accepted).redDegree x.val
  apply Multiset.coe_eq_coe.mp
  rw [FullDegrees.terminal_histogram run done]
  have all : ((List.finRange (v+1) : List (Fin (v+1))) : Multiset _)=(Finset.univ : Finset (Fin (v+1))).val := by
    have eq : (List.finRange (v+1)).toFinset=Finset.univ := by ext; simp
    rw [←eq,List.toFinset_val,List.dedup_eq_self.mpr (List.nodup_finRange _)]
  rw [←Multiset.map_coe,all]
  exact Multiset.map_congr rfl (fun i _ => val i)

end Recognition.LabelWitness
