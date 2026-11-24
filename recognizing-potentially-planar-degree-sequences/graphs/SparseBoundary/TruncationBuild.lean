import SparseBoundary.GraphUnion
import SparseBoundary.Truncation

namespace SparseBoundary.Truncation
open Graph

private def cutRel (H : Graph (n+1)) (port : Fin 3→Fin n) : Fin (3+n)→Fin (3+n)→Bool :=
  Fin.addCases (fun s => Fin.addCases (fun t => s != t) (fun x => x==port s))
    (fun x => Fin.addCases (fun s => x==port s) (fun y => H.adj x.succ y.succ))

private def cut (H : Graph (n+1)) (port : Fin 3→Fin n) := ofRelation (cutRel H port)

private theorem cut_adj (H : Graph (n+1)) (port : Fin 3→Fin n) (x y : Fin (3+n)) :
    (cut H port).adj x y=cutRel H port x y := by
  apply adj_ofRelation
  · intro u v
    refine Fin.addCases ?_ ?_ u <;> intro i <;> refine Fin.addCases ?_ ?_ v <;> intro j <;>
      simp [cutRel,H.adj_comm,bne_comm]
  · intro u
    refine Fin.addCases ?_ ?_ u <;> intro i <;> simp [cutRel]

/-- A constructive cubic truncation, including all labelled degrees. The first
vertex is replaced by a triangle with one of its three old edges at each corner. -/
theorem build (H : Graph (n+1)) (deg : H.degree 0=3) :
    ∃ G : Graph (3+n), Nonempty (Shape H G) ∧ (∀ s : Fin 3,G.degree (s.castAdd n)=3) ∧
      ∀ x : Fin n,G.degree (x.natAdd 3)=H.degree x.succ := by
  let nbr := (List.finRange n).filter (fun x => H.adj 0 x.succ)
  have len : nbr.length=3 := by
    simpa [degree,List.finRange_succ,List.filter_map,Function.comp_def,nbr] using deg
  let port (s : Fin 3) := nbr.get (Fin.cast len.symm s)
  have list_eq : (List.finRange 3).map port=nbr := by
    apply List.ext_getElem
    · simp [len]
    · intro i hi hj; simp [port]
  have nod : nbr.Nodup := List.Pairwise.filter _ (List.nodup_finRange _)
  have spoke (s : Fin 3) : H.adj 0 (port s).succ=true := (List.mem_filter.mp
    (show port s∈nbr from List.get_mem ..)).2
  refine ⟨cut H port,⟨⟨port,spoke,?_,?_⟩⟩,?_,?_⟩
  · intro x y; simp [cut_adj,cutRel]
  · intro s x; simp [cut_adj,cutRel]
  · intro s
    have two : ((List.finRange 3).filter (fun t => s != t)).length=2 := by decide +revert
    have one : ((List.finRange n).filter (fun x => x==port s)).length=1 := by
      simp [List.filter_beq,List.nodup_iff_count_of_mem.mp (List.nodup_finRange n) _ (List.mem_finRange _)]
    unfold degree
    rw [union_range 3 n]
    simp [List.filter_append,List.filter_map,Function.comp_def,cut_adj,cutRel,two,one]
  · intro x
    have split : ((List.finRange 3).filter (fun s => x==port s)).length=nbr.count x := by
      have h := congrArg (fun ys : List (Fin n) => (ys.filter (fun y => y==x)).length) list_eq
      simpa [List.filter_map,Function.comp_def,List.filter_beq,Bool.beq_comm (a:=x)] using h
    have cnt : nbr.count x=(H.adj x.succ 0).toNat := by
      by_cases m : x∈nbr
      · have h := (List.mem_filter.mp m).2
        simp [List.nodup_iff_count_of_mem.mp nod _ m,H.adj_comm x.succ 0,h]
      · have h : H.adj 0 x.succ=false := by simpa [nbr,List.mem_finRange] using m
        simp [List.count_eq_zero.mpr m,H.adj_comm x.succ 0,h]
    unfold degree
    rw [union_range 3 n,List.finRange_succ (n:=n)]
    simp only [List.filter_append,List.filter_map,List.length_append,List.length_map,Function.comp_def,
      cut_adj,cutRel,Fin.addCases_left,Fin.addCases_right,split,cnt]
    cases e : H.adj x.succ 0 <;> simp [e,List.filter_map,Function.comp_def,Nat.add_comm]

/-- Truncation of a degree-three entry preserves planar realizability. -/
theorem truncate_profile {d : List Nat} (hp : Planaric (3::d)) :
    Planaric (3::3::3::d) := by
  obtain ⟨H,r,ph⟩ := hp
  obtain ⟨G,⟨S⟩,corners,outer⟩ := build H (r 0)
  have pl := Graph.planaric_profile (planar S ph)
  have row : List.ofFn G.degree=3::3::3::d := by
    rw [List.ofFn_add]
    have first : List.ofFn (fun i : Fin 3 => G.degree (i.castAdd d.length))=[3,3,3] := by
      simp only [corners]; rfl
    have last : List.ofFn (fun i : Fin d.length => G.degree (i.natAdd 3))=d := by
      apply List.ext_getElem
      · simp
      · intro i hi hj
        simp only [List.getElem_ofFn]
        exact (outer ⟨i,hj⟩).trans (r (Fin.succ ⟨i,hj⟩))
    change (List.ofFn (fun i : Fin 3 => G.degree (i.castAdd d.length))) ++ _= _
    rw [first,last]
    rfl
  rwa [row] at pl

end SparseBoundary.Truncation
