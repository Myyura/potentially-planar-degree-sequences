import DiskFullerene.FanLoads
import DiskFullerene.GluingIso

namespace DiskFullerene.EndFans
open Dual EndEuler EndLabels Separation

inductive BoundaryLabel where
  | corner (i : I)
  | middle
  deriving DecidableEq, Repr

namespace BoundaryLabel

def advance (k : I) : BoundaryLabel → BoundaryLabel
  | .corner i => if i=k then .middle else .corner (after i)
  | .middle => .corner (after k)

def retreat (k : I) : BoundaryLabel → BoundaryLabel
  | .corner i => if before i=k then .middle else .corner (before i)
  | .middle => .corner k

def neighbor (k : I) (a b : BoundaryLabel) := b=advance k a ∨ b=retreat k a

instance (k : I) (a b : BoundaryLabel) : Decidable (neighbor k a b) := by unfold neighbor; infer_instance

theorem cycle (k : I) (a : BoundaryLabel) : advance k (retreat k a)=a ∧ retreat k (advance k a)=a ∧ advance k a≠retreat k a := by
  cases a <;> decide +revert

theorem symm (k : I) (a b : BoundaryLabel) : neighbor k a b ↔ neighbor k b a := by
  cases a <;> cases b <;> decide +revert

end BoundaryLabel

inductive Node where
  | center
  | rim (i : I)
  | outside (x : BoundaryLabel)
  deriving DecidableEq, Repr

/-- The active wheel and boundary labels used in the finite cap table. -/
def code (k : I) : Node→Nat
  | .center => 0
  | .rim i => CapRing.rim i
  | .outside (.corner i) => CapRing.corner i
  | .outside .middle => CapRing.midpoint k

def armContains (k i : I) (v : BoundaryLabel) : Prop :=
  v=.corner i ∨ v=.corner (after i) ∨ v=.middle ∧ i=k
instance (k i : I) (v : BoundaryLabel) : Decidable (armContains k i v) := by unfold armContains; infer_instance

def nodeEdge (k : I) : Node→Node→Bool
  | .rim i,.rim j => decide (j=before i ∨ j=after i)
  | .rim _,.center | .center,.rim _ => true
  | .rim i,.outside v | .outside v,.rim i => decide (armContains k i v)
  | .outside a,.outside b => decide (BoundaryLabel.neighbor k a b)
  | _,_ => false

theorem edges_in_table (k : I) (a b : Node) : nodeEdge k a b = CapRing.adjacent (CapRing.singletonPattern k) (code k a) (code k b) := by
  set_option maxRecDepth 16384 in
  set_option maxHeartbeats 0 in
  cases a with
  | center => cases b with | center => decide +revert | rim j => decide +revert | outside b => cases b <;> decide +revert
  | rim i => cases b with | center => decide +revert | rim j => decide +revert | outside b => cases b <;> decide +revert
  | outside a =>
    cases b with
    | center => cases a <;> decide +revert
    | rim j => cases a <;> decide +revert
    | outside b => cases a <;> cases b <;> decide +revert

namespace Cap
variable {M : MapData} {G : IsDiskFullerene M h} {d : EndPiece M G}

def outer (C : Cap d) : BoundaryLabel→Face M
  | .corner i => C.junction i
  | .middle => C.middle

def real (C : Cap d) : Node→Face M
  | .center => C.W.center
  | .rim i => C.W.rim i
  | .outside a => C.outer a

theorem outer_boundary (C : Cap d) (a : BoundaryLabel) : IsBoundary G (C.outer a) := by
  cases a with
  | corner i => exact C.junction_boundary i
  | middle => exact C.boundary (i:=C.index) (v:=C.middle) (by simp [Arc.word,C.split])

theorem outer_injective (C : Cap d) (hh : 3≤h) (a b : BoundaryLabel) (e : C.outer a=C.outer b) : a=b := by
  cases a with
  | corner i => cases b with
    | corner j => exact congrArg BoundaryLabel.corner (C.distinct_corners hh i j e)
    | middle => exact False.elim (C.mid_ne_corner hh C.split i e.symm)
  | middle => cases b with
    | corner j => exact False.elim (C.mid_ne_corner hh C.split j e)
    | middle => rfl

theorem real_injective (C : Cap d) (hh : 3≤h) (a b : Node) (e : C.real a=C.real b) : a=b := by
  have diff (q : Face M) (iq : sectorCore d.seam d.side q=true) (j) : q≠C.outer j := fun eq=>
    (mem_diskInterior G _).mp (core_disk iq) |>.2 (eq ▸ C.outer_boundary j)
  have ctr (j) := diff C.W.center ((C.W.chosen _).mpr (.inl rfl)) j
  have rim (i j) := diff _ (C.rim_in i) j
  cases a <;> cases b <;> simp only [real] at e <;> first | rfl | exact congrArg Node.rim (C.W.rim_injective _ _ e) | exact congrArg Node.outside (C.outer_injective hh _ _ e) | grind [Wheel.apart]

theorem arm_row (C : Cap d) (hh : 3≤h) (i : I) (a : BoundaryLabel) :
    C.outer a∈(C.fans.arc i).word ↔ armContains C.index i a := by
  rw [C.rim_arc hh i]
  change C.outer a∈(C.outer (.corner i)::(if i=C.index then [C.outer .middle] else [])++[C.outer (.corner (after i))]) ↔ _
  have inj (x y : BoundaryLabel) : C.outer x=C.outer y ↔ x=y := ⟨C.outer_injective hh x y,fun eq=>eq ▸ rfl⟩
  split <;> simp_all [armContains] <;> grind

theorem first_arc (C : Cap d) (hh : 3≤h) (a : BoundaryLabel) : ∃ i : I,
    (C.outer a,C.outer (BoundaryLabel.advance C.index a))∈sides (dualRow G (C.W.rim i)) := by
  cases a with
  | corner i =>
    refine ⟨i,(C.fans.corners i).mem_iff.mp ?_⟩; rw [C.rim_arc hh i]; by_cases eq : i=C.index <;> simp [BoundaryLabel.advance,outer,eq,sides]
  | middle => refine ⟨C.index,(C.fans.corners C.index).mem_iff.mp ?_⟩; rw [C.rim_arc hh]; simp [BoundaryLabel.advance,outer,sides]

theorem adj_or_seam (C : Cap d) (hh : 3≤h) (a : BoundaryLabel) :
    OnCycle (dualRow G (apex M)) (C.outer a) (C.outer (BoundaryLabel.advance C.index a)) ∨
    ((C.outer a=atSide G (apex M) d.i ∧ C.outer (BoundaryLabel.advance C.index a)=atSide G (apex M) d.j) ∨
     (C.outer a=atSide G (apex M) d.j ∧ C.outer (BoundaryLabel.advance C.index a)=atSide G (apex M) d.i)) := by
  obtain ⟨i,edge⟩ := C.first_arc hh a
  obtain ⟨k,v,ac,en,mem,_⟩ := cornerEdge G edge
  have pick := core_corner_selected d.seam (C.rim_in i) v mem
  have side : vertexSide d.seam d.side (primal G k).1=true ∨ vertexSide d.seam d.side (primal G k).2=true := by rcases en with eq|eq; exact .inl (eq ▸ pick); exact .inr (eq ▸ pick)
  rcases d.terminal.seam_or_cycle hh d.seam d.side (C.outer_boundary _) (C.outer_boundary _) ac side with yes|ke
  · exact .inl yes
  · subst k; right; rcases ac with p|p <;> rcases d.seam.middle with q|q <;> have both:=Prod.mk.inj (p.symm.trans q) <;> grind

end Cap
end DiskFullerene.EndFans
