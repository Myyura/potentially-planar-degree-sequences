import SparseBoundary.FanOuter
import SparseBoundary.FanSpokes
import SparseBoundary.FanLoops
import SparseBoundary.GraphSeries
import SparseBoundary.GraphPerm

namespace SparseBoundary.Fan

open Graph

private def squareAdj (a b : Nat) : Bool :=
  decide (a≠b ∧ (a=0 ∨ b=0 ∨ (a≤b+2 ∧ b≤a+2)))

/-- The cone over the square of the path on q vertices. The apex is zero. -/
def squareCone (q : Nat) : Graph (q+1) :=
  ofRelation (fun i j => squareAdj i.val j.val)

private theorem square_adj (q : Nat) (i j : Fin (q+1)) :
    (squareCone q).adj i j = squareAdj i.val j.val := by
  apply adj_ofRelation
  · intro x y; simp only [squareAdj,decide_eq_decide]; omega
  · intro x; simp [squareAdj]

private def zig (n i : Nat) := if i%2=0 then i else 2*n-i

private theorem zig_inj {a b n : Nat} (ha : a<n) (hb : b<n)
    (h : zig n a=zig n b) : a=b := by
  unfold zig at h; split at h <;> split at h <;> omega

private theorem between_order (a b c : Nat) : min a b<c ∧ c<max a b ↔
    (a<c ∧ c<b ∨ b<c ∧ c<a) := by
  by_cases h : a≤b <;> simp only [Nat.min_def,Nat.max_def,h,ite_true,ite_false] <;> omega

set_option maxHeartbeats 4000000 in
private theorem zig_noncross {a b x y n : Nat} (ha : a<n) (hb : b<n) (hx : x<n) (hy : y<n)
    (ax : a≠x) (ay : a≠y) (bx : b≠x) (by' : b≠y)
    (h1 : a≤b+2) (h2 : b≤a+2) (h3 : x≤y+2) (h4 : y≤x+2) :
    ((min (zig n a) (zig n b)<zig n x ∧ zig n x<max (zig n a) (zig n b)) ↔
     (min (zig n a) (zig n b)<zig n y ∧ zig n y<max (zig n a) (zig n b))) := by
  simp only [between_order,zig]
  by_cases e1 : a%2=0 <;> by_cases e2 : b%2=0 <;>
    by_cases e3 : x%2=0 <;> by_cases e4 : y%2=0 <;>
    simp only [e1,e2,e3,e4,ite_true,ite_false] <;> omega

theorem square_cone_planar (q : Nat) : (squareCone q).Planar := by
  apply outer_order_planar (v:=0)
  refine ⟨fun v => zig (q+1) v.val,fun i j h => Fin.ext (zig_inj i.isLt j.isLt h),?_⟩
  intro a b x y av bv xv yv ax ay bx by' ab xy
  have nz {v : Fin (q+1)} (ne : v≠0) : v.val≠0 := fun eq => ne (Fin.ext eq)
  have h1 := nz av; have h2 := nz bv; have h3 := nz xv; have h4 := nz yv
  simp only [square_adj,squareAdj,decide_eq_true_eq] at ab xy
  simp only [decide_eq_decide]
  apply zig_noncross a.isLt b.isLt x.isLt y.isLt (fun e => ax (Fin.ext e)) (fun e => ay (Fin.ext e))
    (fun e => bx (Fin.ext e)) (fun e => by' (Fin.ext e)) <;> omega


@[simp] private theorem square_spoke (q : Nat) (i : Fin q) :
    (squareCone q).adj 0 i.succ=true := by simp [square_adj,squareAdj]

private theorem square_hub_degree (q : Nat) : (squareCone q).degree 0=q := by
  simp [degree,List.finRange_succ,List.filter_eq_self.mpr]

private def near (i j : Nat) := decide (i≠j ∧ i≤j+2 ∧ j≤i+2)

private theorem count_near (n j : Nat) :
    (List.range n).countP (near j)=
      (if 1≤j ∧ j≤n then 1 else 0)+(if 2≤j ∧ j≤n+1 then 1 else 0)+
      (if j+1<n then 1 else 0)+(if j+2<n then 1 else 0) := by
  induction n with
  | zero => simp (disch := omega) only [List.range_zero,List.countP_nil,ite_eq_right]
  | succ n ih =>
    rw [List.range_succ,List.countP_append,ih]
    simp only [List.countP_cons,List.countP_nil,near,decide_eq_true_eq]
    repeat' split <;> try omega

private def base (q i : Nat) : Nat := 1+(if 1≤i then 1 else 0)+(if 2≤i then 1 else 0)+
    (if i+1<q then 1 else 0)+(if i+2<q then 1 else 0)

private theorem square_path_degree (q : Nat) (i : Fin q) :
    (squareCone q).degree i.succ=base q i.val := by
  have tail (j : Fin q) : (squareCone q).adj i.succ j.succ=near i.val j.val := by
    simp [square_adj,squareAdj,near,Fin.val_succ]
  have back : (squareCone q).adj i.succ 0=true := (adj_comm ..).trans (square_spoke ..)
  have vals : (List.finRange q).map Fin.val=List.range q := by apply List.ext_getElem <;> simp
  have hf : ((List.finRange q).filter (fun j => near i.val j.val)).length=
      (List.range q).countP (near i.val) := by
    rw [← vals,List.countP_eq_length_filter,List.filter_map,List.length_map]; rfl
  rw [degree,List.finRange_succ,List.filter_cons,ite_eq_left back,List.length_cons,
    List.filter_map,List.length_map]
  rw [show (squareCone q).adj i.succ ∘ Fin.succ=(fun j => near i.val j.val) from funext tail,hf,count_near]
  simp (disch := omega) only [show i.val≤q by omega,show i.val≤q+1 by omega,and_true,base]
  omega

theorem sum_maps (xs : List α) (f g : α → Nat) :
    (xs.map (fun i => f i+g i)).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons]; omega

theorem indicators (n s : Nat) :
    ((List.range n).map (fun i => if s≤i then 1 else 0)).sum=n-s ∧
    ((List.range n).map (fun i => if i<s then 1 else 0)).sum=min n s := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
      List.sum_nil,Nat.add_zero,ih.1,ih.2]
    by_cases h : s≤n <;> by_cases h' : n+1≤s <;> by_cases h'' : n≤s <;>
      simp (disch := omega) only [Nat.min_def,ite_eq_left,ite_eq_right] <;> try omega
    all_goals simp [Nat.sub_eq_zero_of_le h',Nat.sub_eq_zero_of_le h'']

private theorem base_sum (q : Nat) (hq : 2≤q) :
    ((List.finRange q).map (fun i => (squareCone q).degree i.succ)).sum+6=5*q := by
  have vals : (List.finRange q).map Fin.val=List.range q := by apply List.ext_getElem <;> simp
  have eqn : (List.finRange q).map (fun i => (squareCone q).degree i.succ)=
      (List.range q).map (base q) := by
    rw [← vals,List.map_map]
    apply List.map_congr_left; intro i _; exact square_path_degree q i
  rw [eqn]
  have cut (i k : Nat) : i+k<q ↔ i<q-k := by omega
  change ((List.range q).map (fun i => 1+(if 1≤i then 1 else 0)+(if 2≤i then 1 else 0)+
    (if i+1<q then 1 else 0)+(if i+2<q then 1 else 0))).sum+6=5*q
  simp only [cut]
  repeat' rw [sum_maps]
  have unit : ((List.range q).map (fun _ => 1)).sum=q := by simp [List.map_const',List.sum_replicate_nat]
  rw [unit,(indicators q 1).1,(indicators q 2).1,(indicators q (q-1)).2,(indicators q (q-2)).2]
  omega

/-- The cone branch on either sparse boundary. The graph has exactly
the prescribed degrees, including the entire degree-two population. -/
theorem cone_range_planaric {a t j : Nat} (us : List Nat) (hq : 2≤us.length)
    (hm : ∀d∈us,5≤d) (vol : a+us.sum+2*j=4*(us.length+1)+2*t)
    (lo : t+5≤a+j) (up : a≤us.length+t) :
    Planaric (List.replicate t 2 ++ a::us) := by
  let q := us.length
  let G := squareCone q
  have tgt (i : Fin us.length) : G.degree i.succ≤us[i] := by
    have h := hm us[i] (List.getElem_mem i.isLt)
    rw [show G.degree i.succ=_ from square_path_degree q i]
    unfold base
    repeat' split
    all_goals omega
  obtain ⟨m,hs,hp⟩ := expand_spokes us G (square_cone_planar q) (square_spoke q) tgt
  have e := base_sum q hq
  have g : G.degree 0=q := square_hub_degree q
  rw [g] at hp
  let l := a+j-(t+5)
  have num : m+2*l=a-q := by
    change m+((List.finRange q).map (fun i => (squareCone q).degree i.succ)).sum=us.sum at hs
    dsimp [q] at *; dsimp [l]; omega
  have aeq : q+m+2*l=a := by
    change m+((List.finRange q).map (fun i => (squareCone q).degree i.succ)).sum=us.sum at hs
    dsimp [q] at *; dsimp [l]; omega
  have p := planaric_hub_loops hp l
  rw [aeq] at p
  have cat (i j : Nat) : List.replicate i 2 ++ List.replicate j 2=List.replicate (i+j) 2 := by
    apply List.eq_replicate_iff.mpr; simp
  rw [← List.append_assoc,cat] at p
  have p' := (planaric_perm List.perm_middle).mpr p
  have mpos : ∃x∈(List.replicate (2*l+m) 2 ++ a::us), 0<x :=
    ⟨a,List.mem_append_right _ (by simp),by dsimp [q] at aeq; omega⟩
  have extra := planaric_add_twos p' mpos (t-(2*l+m))
  rw [← List.append_assoc,cat] at extra
  have tEq : t-(2*l+m)+(2*l+m)=t := by dsimp [q] at num; omega
  rwa [tEq] at extra

end SparseBoundary.Fan
