import DiskFullerene.TerminalInterior

namespace DiskFullerene.Dual
open EndEuler

private theorem count_union_bound {α} (xs : List α) (a b u : α → Bool)
    (apart : ∀ t, ¬(a t=true ∧ b t=true))
    (inside : ∀ t, a t=true ∨ b t=true → u t=true) :
    xs.countP a + xs.countP b ≤ xs.countP u := by
  induction xs with
  | nil => simp
  | cons t ts ih =>
    have h := apart t; have k := inside t
    cases A : a t <;> cases B : b t <;> cases U : u t <;> simp_all <;> omega

theorem two_core_budget {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d e : EndPiece M G)
    (apart : ∀ v, ¬(vertexSide d.seam d.side v=true ∧ vertexSide e.seam e.side v=true)) :
    num (sectorCore d.seam d.side)+num (sectorCore e.seam e.side)≤6+M.hexagons := by
  classical
  let A := sectorCore d.seam d.side; let B := sectorCore e.seam e.side
  let inner := fun f : Face M => decide (f∈diskInterior G)
  have inside {x y : Face M} {S : TriangleSide G (apex M) x y} {t B} (hit : sectorCore S B t=true) : inner t=true :=
    (Bool.and_eq_true_iff.mp hit).1
  have inequality := count_union_bound (List.finRange _) A B inner (EndPiece.disjoint_core hh d e apart)
    (fun _ hv => hv.elim inside inside)
  have eq : ((List.finRange _).filter inner).Perm (diskInterior G) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) ?_).mpr
    · intro f; simp [inner]
    · exact (List.nodup_finRange _).filter _
  rw [List.countP_eq_length_filter (p:=inner),eq.length_eq,interior_count G hh] at inequality
  exact inequality

theorem exact_end_sizes {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d e : EndPiece M G)
    (apart : ∀ v, ¬(vertexSide d.seam d.side v=true ∧ vertexSide e.seam e.side v=true))
    (ld : 6≤num (sectorCore d.seam d.side)) (le : 6≤num (sectorCore e.seam e.side))
    (six : M.hexagons=6) : num (sectorCore d.seam d.side)=6 ∧ num (sectorCore e.seam e.side)=6 := by
  have budget := two_core_budget hh d e apart
  omega


private theorem count_union {α} (xs : List α) (a b : α → Bool) (apart : ∀ t, ¬(a t=true ∧ b t=true)) :
    xs.countP (fun t => a t || b t) = xs.countP a + xs.countP b := by
  induction xs with
  | nil => simp
  | cons t ts ih =>
    have := apart t; cases A : a t <;> cases B : b t <;> simp_all <;> omega

theorem exact_end_cover {M} {G : IsDiskFullerene M h} (hh : 3≤h) (d e : EndPiece M G)
    (apart : ∀ f, ¬(sectorCore d.seam d.side f=true ∧ sectorCore e.seam e.side f=true))
    (ld : num (sectorCore d.seam d.side)=6) (le : num (sectorCore e.seam e.side)=6)
    (six : M.hexagons=6) (f : Face M) : f∈diskInterior G ↔
      sectorCore d.seam d.side f=true ∨ sectorCore e.seam e.side f=true := by
  classical
  let all := List.finRange M.faces.length
  let A := sectorCore d.seam d.side
  let B := sectorCore e.seam e.side
  let joined := fun t => A t || B t
  let inner := fun t : Face M => decide (t∈diskInterior G)
  have subset (t : Face M) (m : joined t=true) : inner t=true := by
    rcases Bool.or_eq_true_iff.mp m with l|r
    · exact (Bool.and_eq_true_iff.mp l).1
    · exact (Bool.and_eq_true_iff.mp r).1
  have h := count_union all A B apart
  change all.countP joined = num (sectorCore d.seam d.side)+num (sectorCore e.seam e.side) at h
  have nd : (all.filter joined).Nodup := (List.nodup_finRange _).filter _
  have contains : all.filter joined ⊆ diskInterior G :=
    fun v m => of_decide_eq_true (subset v (List.mem_filter.mp m).2)
  have count := interior_count G hh
  have allsize : (all.filter joined).length=(diskInterior G).length := by
    rw [← List.countP_eq_length_filter,h,ld,le,count,six]
  have diff : (diskInterior G).filter (fun t=> !joined t)=[] := by
    have ndI : (diskInterior G).Nodup := (List.nodup_finRange _).filter _
    have extra : ((all.filter joined) ++ (diskInterior G).filter (fun t => !joined t)).Nodup := by
      apply List.nodup_append.mpr
      refine ⟨nd,ndI.filter _,?_⟩
      intro a ha b hb same; subst b
      have yes := (List.mem_filter.mp ha).2
      have no := (List.mem_filter.mp hb).2
      simp [yes] at no
    have le := extra.length_le_of_subset (List.append_subset.mpr ⟨contains,fun _ m => (List.mem_filter.mp m).1⟩)
    simp only [List.length_append] at le
    exact List.eq_nil_of_length_eq_zero (by omega)
  constructor
  · intro mem
    by_cases J : joined f=true
    · exact Bool.or_eq_true_iff.mp J
    · have impossible : f∈(diskInterior G).filter (fun t => !joined t) := List.mem_filter.mpr ⟨mem,by simp_all⟩
      simp [diff] at impossible
  · intro inside
    exact of_decide_eq_true (subset f (Bool.or_eq_true_iff.mpr inside))

end DiskFullerene.Dual
