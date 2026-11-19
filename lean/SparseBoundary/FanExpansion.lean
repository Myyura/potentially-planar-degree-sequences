import SparseBoundary.GraphSubdivision
import SparseBoundary.FanPlanar

namespace SparseBoundary.Fan

open Graph

/-- One positive weight increment on an existing support edge inserts a
new degree-two vertex, keeping the old direct edge. -/
private def copyRel (G : Graph n) (a b : Fin n) : Fin (n+1) → Fin (n+1) → Bool :=
  let endp := fun i => i == a || i == b
  Fin.cases (Fin.cases false endp) (fun i => Fin.cases (endp i) (G.adj i))

def copyEdge (G : Graph n) (a b : Fin n) : Graph (n+1) :=
  ofRelation (copyRel G a b)

private theorem copy_adj (G : Graph n) (a b : Fin n) (i j : Fin (n+1)) :
    (copyEdge G a b).adj i j=copyRel G a b i j := by
  apply adj_ofRelation
  · refine Fin.cases ?_ (fun i => ?_)
    · exact Fin.cases rfl (fun _ => rfl)
    · exact Fin.cases rfl (fun j => G.adj_comm i j)
  · exact Fin.cases rfl (fun i => G.adj_self i)

@[simp] theorem copy_old_edge (G : Graph n) (a b i j : Fin n) :
    (copyEdge G a b).adj i.succ j.succ = G.adj i j := by simp [copy_adj,copyRel]

theorem copy_planar {G : Graph n} (h : G.Planar) {a b : Fin n} (he : G.adj a b=true) :
    (copyEdge G a b).Planar := by
  apply degree_two_extension h a b he (by simp)
  refine Fin.cases (by simp) (fun i => ?_)
  simp [copy_adj,copyRel]

private theorem count_two (a b : Fin n) (hne : a≠b) :
    ((List.finRange n).filter (fun i => i==a || i==b)).length=2 := by
  have partition (xs : List (Fin n)) :
      (xs.filter (fun i => i==a || i==b)).length=xs.count a + xs.count b := by
    induction xs with
    | nil => simp
    | cons v xs ih =>
      by_cases va : v=a <;> by_cases vb : v=b <;> simp_all [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rw [partition, (List.nodup_finRange n).count_of_mem (List.mem_finRange a),
    (List.nodup_finRange n).count_of_mem (List.mem_finRange b)]

theorem copy_new_degree {G : Graph n} {a b : Fin n} (he : G.adj a b=true) :
    (copyEdge G a b).degree 0=2 := by
  have hne : a≠b := by rintro rfl; simp at he
  simpa [degree,List.finRange_succ,List.filter_map,Function.comp_def,copy_adj,copyRel] using count_two a b hne

def hit (v : Fin n) (p : Fin n × Fin n) : Nat := if v=p.1 ∨ v=p.2 then 1 else 0

theorem copy_old_degree (G : Graph n) (a b i : Fin n) :
    (copyEdge G a b).degree i.succ=G.degree i+hit i (a,b) := by
  simp only [degree,List.finRange_succ,List.filter_cons,List.filter_map]
  rw [show (copyEdge G a b).adj i.succ ∘ Fin.succ=G.adj i from
    funext (fun j => copy_old_edge ..)]
  simp [hit,copy_adj,copyRel]; split <;> simp_all

/-- Every list entry represents one extra copy. Repetitions need no special
handling; every copy receives its own new vertex. -/
def incidents (v : Fin n) (es : List (Fin n × Fin n)) : Nat := (es.map (hit v)).sum

private def shift (e : Fin n × Fin n) : Fin (n+1) × Fin (n+1) := (e.1.succ,e.2.succ)

@[simp] private theorem shifted_zero (es : List (Fin n × Fin n)) :
    incidents 0 (es.map shift)=0 := by
  induction es with
  | nil => simp [incidents]
  | cons e es ih =>
    change hit 0 (shift e)+incidents 0 (es.map shift)=0
    rw [ih]; simp [hit,shift,Fin.ne_of_lt (Fin.succ_pos _)]

@[simp] private theorem shifted_succ (es : List (Fin n × Fin n)) (v : Fin n) :
    incidents v.succ (es.map shift)=incidents v es := by
  induction es with
  | nil => simp [incidents]
  | cons e es ih =>
    change hit v.succ (shift e)+incidents v.succ (es.map shift) =
      hit v e+incidents v es
    simp [ih,shift,hit]

private theorem planaric_of_map {G : Graph n} (h : G.Planar) :
    Planaric ((List.finRange n).map G.degree) := by
  have lift {ds : List Nat} {m : Nat} (hn : ds.length=m)
      (hp : ∃ H : Graph m, H.Planar ∧ ∀ i : Fin m, H.degree i=ds[i.val]'(by omega)) :
      Planaric ds := by subst m; obtain ⟨H,hp,hr⟩ := hp; exact ⟨H,hr,hp⟩
  apply lift (m:=n) (by simp)
  exact ⟨G,h,by simp⟩

/-- Expanding any loop-free planar support with *arbitrary integer edge
multiplicities* as one direct edge and one length-two path per additional
copy gives an actual planar realization of the indicated profile. -/
theorem expand {n : Nat} (G : Graph n) (hp : G.Planar) (es : List (Fin n × Fin n))
    (ok : ∀ e ∈ es, G.adj e.1 e.2=true) :
    Planaric (List.replicate es.length 2 ++ (List.finRange n).map
      (fun v => G.degree v + incidents v es)) := by
  match es with
  | [] => simpa [incidents] using planaric_of_map hp
  | (a,b)::es =>
    let H := copyEdge G a b
    have he := ok (a,b) (by simp)
    have hps := copy_planar hp he
    have usable : ∀ e ∈ es.map shift, H.adj e.1 e.2=true := by
      intro e h
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp h
      simpa [shift,H] using ok x (by simp [hx])
    have ih := expand H hps (es.map shift) usable
    have hh : (List.finRange (n+1)).map (fun v => H.degree v+incidents v (es.map shift)) =
        2 :: (List.finRange n).map (fun v => G.degree v + incidents v ((a,b)::es)) := by
      rw [List.finRange_succ,List.map_cons,List.map_map]
      congr 1
      · simp [H,copy_new_degree he]
      · apply List.map_congr_left
        intro v _
        change H.degree v.succ+incidents v.succ (es.map shift)=G.degree v + (hit v (a,b)+incidents v es)
        rw [shifted_succ,show H.degree v.succ=_ from copy_old_degree G a b v]; omega
    rw [hh,List.length_map] at ih
    rw [List.length_cons,List.replicate_succ']
    simpa [List.append_assoc] using ih
termination_by es.length

end SparseBoundary.Fan
