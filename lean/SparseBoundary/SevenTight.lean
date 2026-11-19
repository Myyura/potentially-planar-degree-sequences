import SparseBoundary.MinorGroups
import SparseBoundary.GraphWeighted
import SparseBoundary.GraphPerm

namespace SparseBoundary.SevenTight
open Graph MinorSearch

def realization : Graph 7 := ⟨1298174⟩
private def initial : Nat := 0xfffffefffeeefeffffefeeefffeffff6
private def catalog : Array (Option Nat) := ((List.range 128).map fun m =>
  if initial.testBit m then some (
    ((List.finRange 7).filter (fun v => m.testBit v.val)).foldl
      (fun s v => s ||| neigh realization v) 0)
  else none).toArray
private def table := makeTable 7 catalog initial

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private theorem cover_ok : covers realization catalog = true := by decide +kernel
private theorem table_ok : validTable catalog initial table = true := by decide +kernel

theorem planar : realization.Planar :=
  planar_of_groups realization catalog initial table cover_ok table_ok
    (by decide +kernel) (by decide +kernel)

private def cycle : List (Fin 7 × Fin 7) :=
  [(0,2),(2,3),(3,1),(1,4),(4,5),(5,6),(6,0)]

private def baseEdges : Fin 7 → List (Fin 7 × Fin 7)
  | 0 => [(0,6),(2,3),(4,5)]
  | 1 => [(0,6),(1,2),(2,3),(4,5)]
  | 2 => [(0,6),(1,4),(4,5),(2,3),(2,3)]
  | 3 => [(0,6),(1,6),(2,3),(2,3),(4,5),(4,5)]
  | 4 => [(0,6),(0,6),(2,3),(2,3),(1,4),(1,5),(4,5)]
  | 5 => [(0,6),(0,6),(2,3),(2,3),(2,3),(1,4),(1,5),(4,5)]
  | 6 => [(0,6),(0,6),(4,5),(4,5),(2,3),(2,3),(2,3),(1,4),(1,5)]

private def targets : Fin 7 → List Nat
  | 0 => [6,5,5,5,5,5,5]
  | 1 => [6,6,6,5,5,5,5]
  | 2 => [6,6,6,6,6,5,5]
  | 3 => [6,6,6,6,6,6,6]
  | 4 => [7,7,6,6,6,6,6]
  | 5 => [7,7,7,7,6,6,6]
  | 6 => [7,7,7,7,7,7,6]

private theorem base_targets : ∀ s, List.ofFn (fun i =>
    realization.degree i + increments (baseEdges s) i) = targets s := by decide +kernel

private def copies (s : Fin 7) : Nat → List (Fin 7 × Fin 7)
  | 0 => baseEdges s
  | k+1 => cycle ++ copies s k

private theorem copies_valid (s : Fin 7) (k : Nat) :
    ∀ e ∈ copies s k, realization.adj e.1 e.2 = true := by
  have h : ∀ s, ∀ e ∈ baseEdges s, realization.adj e.1 e.2 = true := by decide +kernel
  have c : ∀ e ∈ cycle, realization.adj e.1 e.2 = true := by decide +kernel
  induction k with
  | zero => exact h s
  | succ k ih => intro e he; rcases List.mem_append.mp he with q|q
                 · exact c e q
                 · exact ih e q

private theorem copies_degree (s : Fin 7) (k : Nat) (i : Fin 7) :
    increments (copies s k) i = increments (baseEdges s) i + 2*k := by
  have hc : ∀ i : Fin 7, increments cycle i = 2 := by decide
  induction k with
  | zero => simp [copies]
  | succ k ih =>
    change increments (cycle ++ copies s k) i = _
    rw [show increments (cycle ++ copies s k) i = increments cycle i + increments (copies s k) i
      from List.countP_append, hc i,ih]; omega

private theorem copies_length (s : Fin 7) (k : Nat) :
    (copies s k).length = (baseEdges s).length + 7*k := by
  induction k with
  | zero => simp [copies]
  | succ k ih => simp [copies,cycle,ih]; omega

private theorem shifted (s : Fin 7) (k : Nat) :
    Planaric ((targets s).map (fun x => x+2*k) ++
      List.replicate ((baseEdges s).length+7*k+1) 2) := by
  have p := expanded_planaric planar (copies s k) (copies_valid s k)
  have h : List.ofFn (fun i => realization.degree i + increments (copies s k) i) =
      (targets s).map (fun x => x+2*k) := by
    rw [←base_targets,List.map_ofFn]
    simp [Function.comp_def,copies_degree,Nat.add_assoc]
  rw [h,copies_length] at p
  have pos : ∃ x ∈ (targets s).map (fun z => z+2*k), 0<x := by
    have h0 : ∀ s, ∃ x ∈ targets s, 0<x := by decide
    obtain ⟨x,hx,hx'⟩ := h0 s
    exact ⟨_,List.mem_map.mpr ⟨x,hx,rfl⟩,by omega⟩
  have q := planaric_add_two p (by obtain ⟨x,hx,hh⟩ := pos
                                   exact ⟨x,List.mem_append_right _ hx,hh⟩)
  apply (planaric_perm List.perm_append_comm).mp
  simpa [List.replicate_succ,List.cons_append] using q

/-- Every seven-entry core of spread at most one and minimum at least
    five admits the upper-boundary realization. -/
theorem near_regular (a b c d e f g t : Nat) (h1 : b≤a) (h2 : c≤b)
    (h3 : d≤c) (h4 : e≤d) (h5 : f≤e) (h6 : g≤f) (lo : 5≤g)
    (spread : a≤g+1) (sum : a+b+c+d+e+f+g=28+2*t) :
    Planaric ([a,b,c,d,e,f,g] ++ List.replicate t 2) := by
  let k := (g-5)/2
  have gp : g=5+2*k ∨ g=6+2*k := by dsimp [k]; omega
  by_cases eqa : a=g
  · have values : a=6+2*k ∧ b=6+2*k ∧ c=6+2*k ∧ d=6+2*k ∧ e=6+2*k ∧ f=6+2*k ∧ g=6+2*k ∧ t=6+7*k+1 := by
      have total : 7*g+0=28+2*t := by omega
      rcases gp with q|q <;> omega
    obtain ⟨A,B,C,D,E,F,G,T⟩ := values
    rw [A,B,C,D,E,F,G,T]
    exact shifted 3 k
  by_cases eqb : b=g
  · have values : a=6+2*k ∧ b=5+2*k ∧ c=5+2*k ∧ d=5+2*k ∧ e=5+2*k ∧ f=5+2*k ∧ g=5+2*k ∧ t=3+7*k+1 := by
      have total : 7*g+1=28+2*t := by omega
      rcases gp with q|q <;> omega
    obtain ⟨A,B,C,D,E,F,G,T⟩ := values
    rw [A,B,C,D,E,F,G,T]
    exact shifted 0 k
  by_cases eqc : c=g
  · have values : a=7+2*k ∧ b=7+2*k ∧ c=6+2*k ∧ d=6+2*k ∧ e=6+2*k ∧ f=6+2*k ∧ g=6+2*k ∧ t=7+7*k+1 := by
      have total : 7*g+2=28+2*t := by omega
      rcases gp with q|q <;> omega
    obtain ⟨A,B,C,D,E,F,G,T⟩ := values
    rw [A,B,C,D,E,F,G,T]
    exact shifted 4 k
  by_cases eqd : d=g
  · have values : a=6+2*k ∧ b=6+2*k ∧ c=6+2*k ∧ d=5+2*k ∧ e=5+2*k ∧ f=5+2*k ∧ g=5+2*k ∧ t=4+7*k+1 := by
      have total : 7*g+3=28+2*t := by omega
      rcases gp with q|q <;> omega
    obtain ⟨A,B,C,D,E,F,G,T⟩ := values
    rw [A,B,C,D,E,F,G,T]
    exact shifted 1 k
  by_cases eqe : e=g
  · have values : a=7+2*k ∧ b=7+2*k ∧ c=7+2*k ∧ d=7+2*k ∧ e=6+2*k ∧ f=6+2*k ∧ g=6+2*k ∧ t=8+7*k+1 := by
      have total : 7*g+4=28+2*t := by omega
      rcases gp with q|q <;> omega
    obtain ⟨A,B,C,D,E,F,G,T⟩ := values
    rw [A,B,C,D,E,F,G,T]
    exact shifted 5 k
  by_cases eqf : f=g
  · have values : a=6+2*k ∧ b=6+2*k ∧ c=6+2*k ∧ d=6+2*k ∧ e=6+2*k ∧ f=5+2*k ∧ g=5+2*k ∧ t=5+7*k+1 := by
      have total : 7*g+5=28+2*t := by omega
      rcases gp with q|q <;> omega
    obtain ⟨A,B,C,D,E,F,G,T⟩ := values
    rw [A,B,C,D,E,F,G,T]
    exact shifted 2 k
  have values : a=7+2*k ∧ b=7+2*k ∧ c=7+2*k ∧ d=7+2*k ∧ e=7+2*k ∧ f=7+2*k ∧ g=6+2*k ∧ t=9+7*k+1 := by
    have total : 7*g+6=28+2*t := by omega
    rcases gp with q|q <;> omega
  obtain ⟨A,B,C,D,E,F,G,T⟩ := values
  rw [A,B,C,D,E,F,G,T]
  exact shifted 6 k

end SparseBoundary.SevenTight
