import SeparatorInput
import GeneratorCost

/-! The raw boundary codebook is indexed by the order alone. The DP later takes
its product with the counters and residual multisets of the particular input. -/
namespace Recognition.CatalogueResult
open PlanarDegrees.Frontier PlanarDegrees.FrontierStep PlanarDegrees.Topology
open Recognition.Outline Recognition.Overlay Recognition.OverlayCoverage Recognition.BoundaryState

def generate (n : Nat) := GeneratorCost.bitWords (cutoff n)

theorem records (n : Nat) :
    (generate n).1.length + 1 = 2 ^ (cutoff n + 1) ∧
    (generate n).2 ≤ 8 * (cutoff n + 1) * (generate n).1.length := by
  simp only [generate, GeneratorCost.bitWords_eq]
  exact ⟨word_count _, GeneratorCost.bitWords_cost _⟩

theorem covers (sep : SeparatorInput.WeightedPlanarSeparator)
    (C : ClosedTrace v f) (terminal : (f + 1) + 4 = 2 * (v + 1)) :
    ∃ order : List Face, order.Perm (List.ofFn C.faces) ∧
      ∀ read rest, order = read ++ rest →
        ∃ ledger : Inventory, replay (read.flatMap Face.sides) = some ledger ∧
          ∃ bits ∈ (generate (v + 1)).1, Covered read ledger bits := by
  have weighted := SeparatorInput.host sep C terminal
    (fun x => cost (simpleDegree C.ledger.sealed x)) (fun x _ => by
      simp [cost])
  obtain ⟨order, perm, all⟩ := bounded_codes_permuted C terminal C.ledger.sealed
    (fun i _ h _ => ShortBoundary.seen C i h) (ShortBoundary.hostMass C terminal) weighted
  refine ⟨order, perm, ?_⟩
  intro read rest cut
  obtain ⟨s, ok, bits, cov, short, weight⟩ := all read rest cut read (.refl _)
  refine ⟨s, ok, bits, ?_, cov⟩
  rw [generate, GeneratorCost.bitWords_eq]
  exact (words_spec _ _).mpr (length_cut _ _ _ short weight)

end Recognition.CatalogueResult
