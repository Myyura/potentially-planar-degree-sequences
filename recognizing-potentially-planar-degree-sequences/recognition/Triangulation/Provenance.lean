import Triangulation.Stacking
import Triangulation.Tetrahedron

namespace Recognition
open Rigidity

/-- Constructible from the tetrahedral sphere by finitely many rounds of
stellar subdivision of distinct triangular faces. -/
inductive StackedMap : {V : Type} → Map V → Prop where
  | tetra : StackedMap Tetrahedron.map
  | subdivide {V : Type} {M : Map V} (prior : StackedMap M) (fill : Stacking.Choice V) :
      StackedMap (Stacking.stack M fill)

end Recognition
