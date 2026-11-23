import DiskFullerene.ConstructionDarts
import DiskFullerene.ConstructionSimple
import DiskFullerene.Reindex

namespace DiskFullerene.PrimalSplice

private theorem primalBounds {u v : Nat} (h : primalEdge n u v) :
    primalVertex n u ∧ primalVertex n v := by
  cases h with
  | left a b _ => exact ⟨.inl a,.inl b⟩
  | right a b _ => exact ⟨.inr a,.inr b⟩
  | bridge i => exact ⟨.inl ((leftArm n).portsValid _),.inr ((rightArm n).portsValid _)⟩
  | back i => exact ⟨.inr ((rightArm n).portsValid _),.inl ((leftArm n).portsValid _)⟩

private theorem wordSize (n : Nat) {w : Word} (h : w∈(primalWords n).1::(primalWords n).2) :
    3≤w.length := by
  obtain a|b := List.mem_cons.mp h
  · rw [a,(primalFaceSizes n).1]; omega
  · obtain s|s := (primalFaceSizes n).2.2.2 w b <;> omega

private theorem primalLoopless (n v : Nat) (e : primalEdge n v v) : False := by
  obtain ⟨w,mem,h⟩ := List.mem_flatMap.mp (((primalCoverage n).edges v v).mpr e)
  have nd := primalFacesSimple n w mem
  have len := wordSize n mem
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp h
  rw [Dual.sides_size] at hi
  rw [Dual.side_at w i hi] at eq
  have same := nd.getElem_inj.mp ((congrArg Prod.fst eq).trans (congrArg Prod.snd eq).symm)
  unfold Dual.next at same; split at same <;> omega

private theorem faceVertices {w : Word} (h : w∈(primalWords n).1 :: (primalWords n).2) :
    ∀ v ∈ w, primalVertex n v := by
  intro v hv
  have fst : (sides w).map Prod.fst = w := by
    cases w with
    | nil => rfl
    | cons a as => exact List.map_fst_zip (by simp)
  rw [←fst] at hv
  obtain ⟨⟨a,b⟩,m,rfl⟩ := List.mem_map.mp hv
  exact (primalBounds (((primalCoverage n).edges a b).mp (List.mem_flatMap.mpr ⟨_,h,m⟩))).1

private theorem innerCount (n : Nat) : (primalWords n).2.length = n+24 := by
  have split (ws : List Word) (h : ∀ w∈ws, w.length=5 ∨ w.length=6) :
      ws.length=(ws.map List.length).count 5 + (ws.map List.length).count 6 := by
    induction ws with
    | nil => rfl
    | cons x xs ih =>
      have sum := ih (fun w hw => h w (by simp [hw]))
      rcases h x (by simp) with a|a <;> simp [a] <;> omega
  have ⟨_,a,b,c⟩ := primalFaceSizes n
  have sum := split _ c
  omega

/-- The upper bound on the *original* cubic map class. All admissibility
fields, including its spherical rotation and three-connectivity, are proved. -/
theorem upperBound (h : Nat) (hh : 12≤h) :
    ∃ M, IsDiskFullerene M h ∧ M.hexagons=6 ∧ M.pentagons=h+6 ∧ M.ord=2*h+22 := by
  obtain ⟨n,rfl⟩ : ∃ n, h=n+12 := ⟨h-12,by omega⟩
  let o := (primalWords n).1
  let fs := (primalWords n).2
  have graph : Reindex.SparseGraph (primalVertex n) (primalEdge n) := by
    refine ⟨primalCubic n,?_,primalLoopless n,fun e => primalBounds e,primalConnected n⟩
    intro x y e
    cases e with
    | left hu hv a => exact .left hv hu ((leftArm n).symm a)
    | right hu hv a => exact .right hv hu ((rightArm n).symm a)
    | bridge i => exact .back i
    | back i => exact .bridge i
  have coverage := primalCoverage n
  have fac : Reindex.SparseFaces (primalVertex n) (primalEdge n) o fs :=
    ⟨fun w mem => ⟨primalFacesSimple n w mem,wordSize n mem,faceVertices mem⟩,coverage.unique,coverage.edges⟩
  obtain ⟨oLen,_,six,polys⟩ := primalFaceSizes n
  have ord := primalOrder n
  have count : fs.length=n+24 := innerCount n
  obtain ⟨M,hm,order,_,_,hex⟩ := Reindex.realize (primalVertices n) graph fac
    (by omega) (by omega) oLen polys
  exact ⟨M,hm,hex.trans six,(eulerCounts hm).1,order.trans ord⟩

end DiskFullerene.PrimalSplice
