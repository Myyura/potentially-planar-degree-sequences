import DiskFullerene.SixBits
import Lean
open Lean Elab Command
namespace DiskFullerene.SixTable
set_option maxRecDepth 65536
set_option maxHeartbeats 0
/-- Keep kernel reductions independent and bounded: each theorem checks precisely
256 graphs. `Fin.cases` assembles these proofs without trusting the generator. -/
elab "verify_six_test_range " blocks:num : command => do
  let n := blocks.getNat
  let mut term ← `(fun j : Fin 0 => False.elim (by have h := j.isLt; omega))
  for k in (List.range n).reverse do
    let name := mkIdent (Name.mkSimple s!"checkedMasks{k}")
    let value := quote k
    elabCommand (← `(private theorem $name : ∀ i : Fin 256, test ⟨256*$value+i.val,by omega⟩=true := by decide +kernel))
    term ← `(Fin.cases $name $term)
  let assembled := mkIdent (Name.mkSimple "allBlocks")
  elabCommand (← `(private theorem $assembled : ∀ k : Fin $blocks, ∀ i : Fin 256, test ⟨256*k.val+i.val,by omega⟩=true := $term))
verify_six_test_range 128

theorem complete (G : SixGraph) : test G = true := by
  obtain ⟨n,h⟩ := G
  have t := allBlocks ⟨n/256,by omega⟩ ⟨n%256,by omega⟩
  have eq : (⟨n,h⟩ : SixGraph)=⟨256*(n/256)+n%256,by omega⟩ := Fin.ext (show n=256*(n/256)+n%256 by omega)
  rw [eq]; exact t

end DiskFullerene.SixTable
