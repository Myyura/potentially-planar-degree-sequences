import Mathlib.Data.List.Basic

/-!
# Unary-encoded numbers

The representation of unary-encoded numbers, fixed by the design record
`materials/unary-design-2026-07-21.md`: unary `n` is a **list of length `n`**
(element type `Bool`, entries ignored), decoded by `unaryVal := List.length`.

This costs nothing: `Ty.size` (`Cert/Language.lean`) charges a list by its
length plus element content, so a list of length `n` is a unary numeral in the
*existing* size model — no second size function, no engine change, no new case
in the blanket theorem `Code.cost_size_le_polyBound`. The bit-charged model
*is* the unary model on lengths.

The standing engine rule "no `range : nat → list nat` primitive, ever" is
exactly the binary/unary boundary: a program may never materialize a length
from a binary value. Unary values are built structurally from input lists —
which is what a strongly-polynomial reduction does anyway: its numbers are
polynomial in the *count* of input objects, and counts are lengths.

The program-level surface — `Ty.unary`, the `unary*` combinators, and their
`unaryVal`-phrased eval lemmas — lives in `Numbers/Unary/Code.lean`.
-/

namespace Hardness
namespace Cert

/-- The value of a unary-encoded number: the length of the list. Total and
junk-tolerant: any list of booleans decodes, its entries ignored — the
decode-totality convention of the library, applied to numbers. -/
def unaryVal (u : List Bool) : ℕ := u.length

@[simp] theorem unaryVal_nil : unaryVal [] = 0 := rfl

@[simp] theorem unaryVal_replicate (n : ℕ) (b : Bool) :
    unaryVal (List.replicate n b) = n := List.length_replicate

theorem unaryVal_append (u v : List Bool) :
    unaryVal (u ++ v) = unaryVal u + unaryVal v := List.length_append

end Cert
end Hardness
