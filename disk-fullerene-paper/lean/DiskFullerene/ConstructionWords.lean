import DiskFullerene.ConstructionPrimal

namespace DiskFullerene.PrimalSplice

abbrev Word := List Nat

/-- Three open facial paths have ordered endpoints p₀→p₁, p₁→p₂ and
p₂→p₀. All other facial words are closed. Vertex labels are those of
the explicit primal vertex sums. -/
structure OpenPatch where
  closed : List Word
  w : Word
  x : Word
  y : Word

private def capClosed : List Word :=
  [[0,4,3,2,1],[0,5,10,15,9,4],[0,1,6,11,5],[1,2,7,12,6],
   [2,3,8,13,7],[3,4,9,14,8],[6,12,18,17,11],[7,13,19,18,12],
   [8,14,20,19,13],[9,15,21,20,14]]

def leftPatch : OpenPatch :=
  ⟨capClosed.map List.reverse,[21,20,19,18,17],[17,11,5,10],[10,15,21]⟩

def rightPatch : OpenPatch :=
  ⟨capClosed,[17,18,19,20,21],[21,15,10],[10,5,11,17]⟩

def OpenPatch.raise (p : OpenPatch) (m : Nat) : OpenPatch :=
  ⟨(p.closed.map (List.map (m+·))),p.w.map (m+·),p.x.map (m+·),p.y.map (m+·)⟩

/-- P and S are the cone and strip triangles, respectively. Reverse the
orientation of the whole open patch to keep the port convention for the
next step. -/
def OpenPatch.step (p : OpenPatch) (m : Nat) : OpenPatch :=
  let P := m+2
  let S := m+3
  ⟨((p.x ++ [S,P]) :: p.closed).map List.reverse,
    (p.w ++ [P]).reverse, (S :: p.y).reverse, [S,P]⟩

def openWords : Nat → OpenPatch
  | 0 => leftPatch
  | k+1 => (openWords k).step (22+4*k)

def OpenPatch.join (l r : OpenPatch) : Word × List Word :=
  (l.w ++ r.w.reverse, (l.x ++ r.x.reverse) :: (l.y ++ r.y.reverse) ::
    l.closed ++ r.closed.map List.reverse)

def primalWords (n : Nat) := (openWords (n+2)).join (rightPatch.raise (22+4*(n+2)))

private theorem lengths (k : Nat) :
    (openWords k).w.length = k+5 ∧
    (openWords k).x.length=(if k<2 then 4 else 3) ∧
    (openWords k).y.length=(if k=0 then 3 else 2) := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [openWords,OpenPatch.step,List.length_reverse,List.length_append,List.length_cons,
      List.length_nil, Nat.zero_add,ih.1,ih.2.2]
    repeat' first | omega | split | constructor

private theorem closedLengths (k : Nat) :
    ((openWords k).closed.map List.length).count 6 = 1+min k 2 ∧
    ((openWords k).closed.map List.length).count 5 = 9+(k-2) ∧
    ∀ w ∈ (openWords k).closed, w.length=5 ∨ w.length=6 := by
  induction k with
  | zero =>
    constructor
    · decide
    constructor
    · decide
    · have test : leftPatch.closed.all (fun w => w.length==5 || w.length==6) := by decide
      simpa [List.all_eq_true,openWords] using test
  | succ k ih =>
    have hx := (lengths k).2.1
    simp only [openWords,OpenPatch.step,List.map_cons,List.map_map,List.length_reverse,
      Function.comp_def,List.count_cons,List.length_cons,List.length_nil,List.length_append,
      List.mem_cons,List.mem_map] at *
    refine ⟨?_,?_,?_⟩
    · by_cases h : k<2 <;> simp [h,hx,ih.1] <;> omega
    · by_cases h : k<2 <;> simp [h,hx,ih.2.1] <;> omega
    · rintro w (rfl|⟨v,hv,rfl⟩)
      · simp [hx] <;> omega
      · simpa using ih.2.2 v hv

/-- Exact face-size inventory of the fully explicit primal face words,
computed for the entire infinite strip, including k=2. -/
theorem primalFaceSizes (n : Nat) :
    (primalWords n).1.length = n+12 ∧
    ((primalWords n).2.map List.length).count 5 = n+18 ∧
    ((primalWords n).2.map List.length).count 6 = 6 ∧
    ∀ w ∈ (primalWords n).2, w.length=5 ∨ w.length=6 := by
  obtain ⟨lw,lx,ly⟩ := lengths (n+2)
  obtain ⟨s,f,cl⟩ := closedLengths (n+2)
  have rx : rightPatch.x.length=3 := rfl
  have ry : rightPatch.y.length=4 := rfl
  have rwlen : rightPatch.w.length=5 := rfl
  have r5 : (rightPatch.closed.map List.length).count 5=9 := by decide
  have r6 : (rightPatch.closed.map List.length).count 6=1 := by decide
  have rv : rightPatch.closed.all (fun w => w.length==5 || w.length==6) := by decide
  have rightAll : ∀ w ∈ rightPatch.closed, w.length=5 ∨ w.length=6 := by simpa [List.all_eq_true] using rv
  simp at lx ly s f
  have lx3 : (openWords (n+2)).x.length=3 := by simpa [show ¬n+2<2 by omega] using lx
  simp only [primalWords,OpenPatch.join,OpenPatch.raise,List.length_append,List.length_reverse,
    List.length_map,List.map_cons,List.map_append,List.map_map,Function.comp_def,List.count_cons,
    List.count_append,lw,lx3,ly,rx,ry,rwlen,r5,r6,s,f,List.mem_cons,List.mem_append,List.mem_map]
  refine ⟨trivial,by simp <;> omega,by simp <;> omega,?_⟩
  rintro w ((rfl|rfl|inL)|inR)
  · simp [lx3,rx]
  · simp [ly,ry]
  · exact cl w inL
  · obtain ⟨b,hb,rfl⟩ := inR
    simpa using rightAll _ hb

end DiskFullerene.PrimalSplice
