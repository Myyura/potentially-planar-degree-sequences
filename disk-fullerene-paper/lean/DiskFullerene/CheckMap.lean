import DiskFullerene.Connectivity

namespace DiskFullerene.Certificates

/-- Read the interior of the forward arc from a to b in a cyclic word.
Soundness does not depend on this candidate being the intended arc: joins
and internal disjointness are checked again in detoursOK. -/
def arc (ring : List Nat) (a b : Nat) : List Nat :=
  (((ring ++ ring).dropWhile (· != a)).tail).takeWhile (· != b)

def detours (M : MapData) (rings : List (List Nat)) : List (List Detour) :=
  M.rows.zipIdx.map fun (r,x) =>
    let ring := rings[x]?.getD []
    r.flatMap fun a => r.map fun b =>
      ⟨a,b,arc ring a b,arc ring.reverse a b⟩

/-- Concatenate the three facial arcs around a cubic vertex. The verifier
checks all proposed routes, so malformed facial words cannot certify a map. -/
def ringsAround (M : MapData) : List (List Nat) :=
  (List.range M.ord).map fun x => Id.run do
    let arcs := (M.faces.filter (·.contains x)).map fun f =>
      (((f ++ f).dropWhile (· != x)).tail).takeWhile (· != x)
    let a := arcs.head!
    let b := (arcs.find? (fun q => q.head? == a.getLast?)).getD []
    let c := (arcs.find? (fun q => q.head? == b.getLast?)).getD []
    return a.dropLast ++ b.dropLast ++ c.dropLast

def descending (M : MapData) : Bool :=
  (List.range M.ord).all fun x => x == 0 || (M.rows[x]?.getD []).any (· < x)

theorem adj_symmetric {M : MapData} (good : M.rotationOK = true) :
    ∀ x y, M.adj x y → M.adj y x := by
  intro x y h
  by_cases bound : x < M.rows.length
  · have mem : (M.rows[x],x) ∈ M.rows.zipIdx := by
      apply List.mem_iff_getElem.mpr
      exact ⟨x,by simp [bound],by simp⟩
    have row := (Bool.and_eq_true_iff.mp (List.all_eq_true.mp good _ mem)).2
    have h' : y ∈ M.rows[x] := by simpa [MapData.adj,bound] using h
    have check := List.all_eq_true.mp row y h'
    simpa [MapData.adj] using (Bool.and_eq_true_iff.mp check).2
  · have hn : M.rows[x]? = none := List.getElem?_eq_none (by omega)
    simp [MapData.adj,hn] at h

private theorem downPath {M : MapData} (symm : ∀ x y, M.adj x y → M.adj y x)
    (desc : descending M = true) (x : Nat) (hx : x < M.ord) :
    PathAvoiding M.adj [] 0 x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp desc x (List.mem_range.mpr hx)) with hz | hc
    · have := beq_iff_eq.mp hz; subst x; exact .here (by simp)
    · obtain ⟨u,hu,lt⟩ := List.any_eq_true.mp hc
      have lt' : u < x := of_decide_eq_true lt
      exact (ih u lt' (by omega)).step (symm x u hu) (by simp)

def check (M : MapData) (h : Nat) (rings : List (List Nat)) : Bool :=
  (M.rows.all fun r => r.length == 3) &&
  M.rotationOK && M.faces.all M.faceOK && (M.faces.flatMap sides).isPerm M.darts &&
  (2*M.ord + 2*M.faces.length == M.darts.length + 4) && (4 ≤ M.ord) &&
  descending M && detoursOK M (detours M rings) &&
  (M.outer.length == h) && (M.inner.all fun f => f.length == 5 || f.length == 6)

theorem sound {M h rings} (ok : check M h rings = true) : IsDiskFullerene M h := by
  simp only [check,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨c,rot⟩,fo⟩,cov⟩,euler⟩,ord⟩,desc⟩,ds⟩,outer⟩,inner⟩ := ok
  have symm := adj_symmetric rot
  refine ⟨?_,rot,fo,List.isPerm_iff.mp cov,euler,?_,outer,?_⟩
  · exact fun r hr => beq_iff_eq.mp (List.all_eq_true.mp c r hr)
  · apply robust_of_detours M _ ds ord symm
    intro u v hu hv
    exact ((downPath symm desc u hu).reverse symm).trans (downPath symm desc v hv)
  · intro f hf
    simpa using List.all_eq_true.mp inner f hf

end DiskFullerene.Certificates
