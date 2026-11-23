import DiskFullerene.Map

namespace DiskFullerene
namespace PathAvoiding

theorem trans (p : PathAvoiding E gone a b) (q : PathAvoiding E gone b c) :
    PathAvoiding E gone a c := by
  induction q with
  | here => exact p
  | step _ e h ih => exact ih.step e h

theorem lastOK (p : PathAvoiding E gone a b) : b ∉ gone := by
  cases p <;> assumption

theorem reverse (symm : ∀ x y, E x y → E y x) (p : PathAvoiding E gone a b) :
    PathAvoiding E gone b a := by
  induction p with
  | here h => exact .here h
  | step path e ok ih => exact ((here ok).step (symm _ _ e) path.lastOK).trans ih

/-- Replace every visit to x by a detour between its predecessor and successor. -/
theorem reroute (p : PathAvoiding E gone a b) (start : a ≠ x) (finish : b ≠ x)
    (bypass : ∀ u v, E u x → E x v → u ∉ x::gone → v ∉ x::gone →
      PathAvoiding E (x::gone) u v) : PathAvoiding E (x::gone) a b := by
  suffices (b ≠ x → PathAvoiding E (x::gone) a b) ∧
      (b = x → ∃ u, E u x ∧ PathAvoiding E (x::gone) a u) from this.1 finish
  clear finish
  induction p with
  | here h =>
    exact ⟨fun _ => .here (by simp [h,start]), fun hx => (start hx).elim⟩
  | @step b c p e hc ih =>
    constructor
    · intro ne
      have last : c ∉ x::gone := by simp [ne,hc]
      by_cases same : b = x
      · obtain ⟨u,hu,pu⟩ := ih.2 same
        exact pu.trans (bypass u c hu (same ▸ e) pu.lastOK last)
      · exact (ih.1 same).step e last
    · intro hcx
      by_cases same : b = x
      · exact ih.2 same
      · exact ⟨b,hcx ▸ e,ih.1 same⟩

end PathAvoiding

namespace Certificates

def edge (M : MapData) (a b : Nat) : Bool := (M.rows[a]?.getD []).contains b

@[simp] theorem edge_iff (M : MapData) (a b : Nat) : edge M a b = true ↔ M.adj a b := by
  simp [edge,MapData.adj]

/-- The internal vertex list of a route from a to b. -/
def joins (M : MapData) (a : Nat) (via : List Nat) (b : Nat) : Bool :=
  match via with
  | [] => edge M a b
  | v :: vs => edge M a v && joins M v vs b

theorem joins_sound {M a via b gone} (h : joins M a via b = true)
    (ha : a ∉ gone) (hb : b ∉ gone) (hi : ∀ t ∈ via, t ∉ gone) :
    PathAvoiding M.adj gone a b := by
  induction via generalizing a with
  | nil => exact (PathAvoiding.here ha).step ((edge_iff ..).mp h) hb
  | cons v vs ih =>
    obtain ⟨e,rest⟩ := Bool.and_eq_true_iff.mp h
    have hv := hi v (by simp)
    exact ((PathAvoiding.here ha).step ((edge_iff ..).mp e) hv).trans
      (ih rest hv (fun t ht => hi t (by simp [ht])))

structure Detour where
  a : Nat
  b : Nat
  p : List Nat
  q : List Nat
  deriving Repr

def Detour.valid (d : Detour) (M : MapData) (x : Nat) : Bool :=
  joins M d.a d.p d.b && joins M d.a d.q d.b &&
    !d.p.contains x && !d.q.contains x && d.p.all (fun t => !d.q.contains t)

private theorem Detour.usable (d : Detour) (hd : d.valid M x = true)
    (old : List Nat) (len : old.length ≤ 1) (ha : d.a ∉ x :: old) (hb : d.b ∉ x :: old) :
    PathAvoiding M.adj (x::old) d.a d.b := by
  simp [Detour.valid, Bool.and_eq_true] at hd
  obtain ⟨⟨⟨⟨p,q⟩,hp⟩,hq⟩,disjoint⟩ := hd
  by_cases good : ∀ t ∈ d.p, t ∉ old
  · exact joins_sound p ha hb (fun t ht => by
      simp only [List.mem_cons,not_or]; exact ⟨fun eq => hp (eq ▸ ht),good t ht⟩)
  · have other : ∀ t ∈ d.q, t ∉ old := by
      cases old with
      | nil => simp
      | cons y ys =>
        have empty : ys = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
        subst ys
        simp at good ⊢
        intro t ht eq
        exact disjoint y good (eq ▸ ht)
    exact joins_sound q ha hb (fun t ht => by
      simp only [List.mem_cons,not_or]; exact ⟨fun eq => hq (eq ▸ ht),other t ht⟩)

/-- A finite check of both directions of every local detour. Neighbours of x
are read from its actual adjacency row. -/
def detoursOK (M : MapData) (book : List (List Detour)) : Bool :=
  (List.range M.ord).all fun x =>
    let r := M.rows[x]?.getD []
    r.all (fun a => r.all fun b => a == b ||
      (book[x]?.getD []).any fun d => d.a == a && d.b == b && d.valid M x)

private theorem row_at {M : MapData} {x y : Nat} (h : M.adj x y) : x < M.ord := by
  by_cases hx : x < M.rows.length
  · exact hx
  · have hn : M.rows[x]? = none := List.getElem?_eq_none (by omega)
    simp [MapData.adj,hn] at h

private theorem localRoute (M : MapData) (D : List (List Detour)) (ok : detoursOK M D = true)
    (symm : ∀ x y, M.adj x y → M.adj y x) (x a b : Nat) (old : List Nat) (len : old.length ≤ 1)
    (ax : M.adj a x) (xb : M.adj x b) (ha : a ∉ x::old) (hb : b ∉ x::old) :
    PathAvoiding M.adj (x::old) a b := by
  have hx := List.all_eq_true.mp ok x (List.mem_range.mpr (row_at xb))
  have h := List.all_eq_true.mp (List.all_eq_true.mp hx a (symm _ _ ax)) b xb
  rcases Bool.or_eq_true_iff.mp h with eq|ex
  · exact (beq_iff_eq.mp eq) ▸ PathAvoiding.here ha
  · obtain ⟨d,_,hd⟩ := List.any_eq_true.mp ex
    simp only [Bool.and_eq_true,beq_iff_eq] at hd
    obtain ⟨⟨rfl,rfl⟩,valid⟩ := hd
    exact d.usable valid old len ha hb

/-- A collection of routes from a root to every vertex certifies connectedness.
The two local, internally disjoint detours then prove three-connectivity. -/
theorem robust_of_detours (M : MapData) (D : List (List Detour))
    (ok : detoursOK M D = true) (ord : 4 ≤ M.ord)
    (symm : ∀ x y, M.adj x y → M.adj y x)
    (connected : ∀ u v, u < M.ord → v < M.ord → PathAvoiding M.adj [] u v) :
    M.ThreeConnected := by
  refine ⟨ord,?_⟩
  intro gone len u v hu hv gu gv
  have base := connected u v hu hv
  cases gone with
  | nil => exact base
  | cons x xs =>
    cases xs with
    | nil =>
      apply base.reroute (x := x) (by simpa using gu) (by simpa using gv)
      exact fun a b => localRoute M D ok symm x a b [] (by decide)
    | cons y ys =>
      have empty : ys = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at len; omega)
      subst ys
      simp at gu gv
      have p := base.reroute (x := y) gu.2 gv.2
        (fun a b => localRoute M D ok symm y a b [] (by decide))
      exact p.reroute gu.1 gv.1 (fun a b => localRoute M D ok symm x a b [y] (by simp))

end Certificates
end DiskFullerene
