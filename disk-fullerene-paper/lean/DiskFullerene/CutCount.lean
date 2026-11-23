import DiskFullerene.CoreArms

namespace DiskFullerene.Dual
open Separation EndEuler

def IsCoreCut {M} (G : IsDiskFullerene M h) (c : Face M) : Prop :=
  c∈diskInterior G ∧ ∃ a b, a∈diskInterior G ∧ b∈diskInterior G ∧
    a∈dualRow G c ∧ b∈dualRow G c ∧ ¬Walk (CoreAvoid G c) a b

structure Branch {M} (G : IsDiskFullerene M h) where
  root : Face M
  seed : Face M
  rootIn : root∈diskInterior G
  seedIn : seed∈diskInterior G
  edge : seed∈dualRow G root

noncomputable def Branch.members {M} {G : IsDiskFullerene M h} (D : Branch G) :=
  open Classical in (diskInterior G).filter (fun v => decide (Walk (CoreAvoid G D.root) D.seed v))

private theorem flipWalk {M} {G : IsDiskFullerene M h} {u a b}
    (p : Walk (CoreAvoid G u) a b) : Walk (CoreAvoid G u) b a :=
  p.symm (fun _ _ e => ⟨e.2.1,e.1,InteriorAdj.symm G _ _ e.2.2⟩)

theorem Branch.mem_iff {M} {G : IsDiskFullerene M h} (D : Branch G) (t : Face M) :
    t∈D.members ↔ Walk (CoreAvoid G D.root) D.seed t := by
  classical
  simp only [members,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
  exact fun p => arm_stays_inside D.rootIn D.seedIn (in_arm.mpr (Or.inr p))

theorem Branch.out {M} {G : IsDiskFullerene M h} (hh : 3≤h) (D : Branch G) : D.root∉D.members := by
  intro hit
  have p := (D.mem_iff _).mp hit
  have ne : D.seed≠D.root := fun eq => row_no_loop G hh _ (eq ▸ D.edge)
  have endpoint {t} (w : Walk (CoreAvoid G D.root) D.seed t) : t≠D.root := by
    cases w with
    | refl => exact ne
    | step _ e => exact e.2.1
  exact endpoint p rfl

theorem Branch.five {M} {G : IsDiskFullerene M h} (hh : 3≤h) (hc : ¬HasChord G) (D : Branch G) :
    5≤D.members.length := by
  have hi := arm_six G hh hc D.rootIn D.seedIn D.edge
  have nd : (diskInterior G).Nodup := (List.nodup_finRange _).filter _
  have perm : ((List.finRange _).filter (arm G D.root D.seed)).Perm (D.root::D.members) := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _)
      (List.nodup_cons.mpr ⟨D.out hh,nd.filter _⟩)).mpr
    intro t; simp [in_arm,D.mem_iff]
  have sz := perm.length_eq
  rw [← List.countP_eq_length_filter,List.length_cons] at sz
  change num (arm G D.root D.seed)=D.members.length+1 at sz
  omega

private theorem transportWalk {M} {G : IsDiskFullerene M h} {u d a z}
    (p : Walk (CoreAvoid G u) a z) (avoid : ¬Walk (CoreAvoid G u) a d) :
    Walk (CoreAvoid G d) a z := by
  induction p with
  | refl => exact .refl
  | @step v w path e ih =>
    exact ih.step ⟨fun eq => avoid (eq ▸ path),fun eq => avoid (eq ▸ path.step e),e.2.2⟩

/-- If a cut vertex lies strictly inside a branch, it cuts off a smaller
branch on the side away from the old root. -/
private theorem smaller_branch {M} {G : IsDiskFullerene M h} (hh : 3≤h)
    (D : Branch G) {v} (hit : v∈D.members) (cut : IsCoreCut G v) :
    ∃ E : Branch G, E.members⊆D.members ∧ E.members.length<D.members.length := by
  classical
  obtain ⟨vi,a,b,ai,bi,av,bv,apart⟩ := cut
  have chooseSeed : ∃ s, s∈diskInterior G ∧ s∈dualRow G v ∧ ¬Walk (CoreAvoid G v) s D.root := by
    by_cases h : Walk (CoreAvoid G v) a D.root
    · exact ⟨b,bi,bv,fun k => apart (h.trans (flipWalk k))⟩
    · exact ⟨a,ai,av,h⟩
  obtain ⟨s,si,sv,far⟩ := chooseSeed
  let E : Branch G := ⟨v,s,vi,si,sv⟩
  have vn : v≠D.root := fun eq => D.out hh (eq ▸ hit)
  have sn : s≠D.root := fun eq => far (eq ▸ Walk.refl)
  have sub : E.members⊆D.members := by
    intro z hz
    apply (D.mem_iff _).mpr
    have vs : CoreAvoid G D.root v s := ⟨vn,sn,vi,si,sv⟩
    exact (((D.mem_iff _).mp hit).step vs).trans (transportWalk ((E.mem_iff _).mp hz) far)
  have nd : (diskInterior G).Nodup := (List.nodup_finRange _).filter _
  have nodup : (v::E.members).Nodup := List.nodup_cons.mpr ⟨E.out hh,nd.filter _⟩
  have high := nodup.length_le_of_subset (show v::E.members⊆D.members from List.cons_subset.mpr ⟨hit,sub⟩)
  exact ⟨E,sub,by simp only [List.length_cons] at high; omega⟩

private theorem leaf_of_branch {M} {G : IsDiskFullerene M h} (hh : 3≤h) (D : Branch G) :
    ∃ E : Branch G, E.members⊆D.members ∧ ∀ v∈E.members, ¬IsCoreCut G v := by
  classical
  generalize size : D.members.length=n
  induction n using Nat.strongRecOn generalizing D with
  | ind n ih =>
    by_cases found : ∃ v∈D.members, IsCoreCut G v
    · obtain ⟨v,hv,cut⟩ := found
      obtain ⟨F,sub,lt⟩ := smaller_branch hh D hv cut
      obtain ⟨E,part,leaf⟩ := ih F.members.length (by omega) F rfl
      exact ⟨E,fun _ m => sub (part m),leaf⟩
    · exact ⟨D,fun _ m => m,fun v mv cv => found ⟨v,mv,cv⟩⟩

/-- Two disjoint branches with no cut vertex; each has at least five
vertices distinct from its own attachment. The argument descends inside
actual components rather than presupposing a block tree. -/
theorem two_leaf_branches {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    {v} (cut : IsCoreCut G v) :
    ∃ D E : Branch G, 5≤D.members.length ∧ 5≤E.members.length ∧
      (∀ t∈D.members, t∉E.members) ∧ (∀ t∈D.members, ¬IsCoreCut G t) ∧
      (∀ t∈E.members, ¬IsCoreCut G t) := by
  obtain ⟨vi,a,b,ai,bi,av,bv,apart⟩ := cut
  let left : Branch G := ⟨v,a,vi,ai,av⟩
  let right : Branch G := ⟨v,b,vi,bi,bv⟩
  obtain ⟨D,subD,leafD⟩ := leaf_of_branch hh left
  obtain ⟨E,subE,leafE⟩ := leaf_of_branch hh right
  exact ⟨D,E,D.five hh hc,E.five hh hc,
    fun t dt et => apart (((left.mem_iff t).mp (subD dt)).trans (flipWalk ((right.mem_iff t).mp (subE et)))),leafD,leafE⟩

noncomputable def coreCuts {M} (G : IsDiskFullerene M h) :=
  open Classical in (diskInterior G).filter (fun v => decide (IsCoreCut G v))

theorem cut_budget {M} (G : IsDiskFullerene M h) (hh : 3≤h) (hc : ¬HasChord G)
    {v} (cut : IsCoreCut G v) : (coreCuts G).length+10≤(diskInterior G).length := by
  classical
  obtain ⟨D,E,ds,es,de,ld,le⟩ := two_leaf_branches G hh hc cut
  have nd : (diskInterior G).Nodup := (List.nodup_finRange _).filter _
  have both : (D.members++E.members).Nodup := List.nodup_append.mpr
    ⟨nd.filter _,nd.filter _,fun a ha b hb eq => de a ha (eq ▸ hb)⟩
  have big : (coreCuts G ++ (D.members++E.members)).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨nd.filter _,both,?_⟩
    intro a ha b hb eq; subst b
    have yes : IsCoreCut G a := of_decide_eq_true (List.mem_filter.mp ha).2
    rcases List.mem_append.mp hb with l|r
    · exact ld a l yes
    · exact le a r yes
  have sub (E : Branch G) : E.members⊆diskInterior G := fun _ m => (List.mem_filter.mp m).1
  have sz := big.length_le_of_subset (List.append_subset.mpr
    ⟨fun _ m => (List.mem_filter.mp m).1,List.append_subset.mpr ⟨sub D,sub E⟩⟩)
  simp only [List.length_append] at sz
  omega

end DiskFullerene.Dual
