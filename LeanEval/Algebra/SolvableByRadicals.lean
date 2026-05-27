import Mathlib
import EvalTools.Markers

namespace LeanEval
namespace Algebra

/-!
# Solvable extensions ↔ solvable groups (the missing converse in Abel–Ruffini)

§58 of Knill's *Some Fundamental Theorems in Mathematics* (additional
statement). For a characteristic-zero field `F` and a nonzero polynomial
`p ∈ F[X]`, the polynomial is **solvable by radicals** — every root of
`p` in the algebraic closure `AlgebraicClosure F` lies in
`solvableByRad F (AlgebraicClosure F)` — if and only if its Galois group
`p.Gal` is solvable. The algebraic closure is the natural ambient field:
it contains all roots of `p` and all roots of unity needed for Kummer
theory, so the right-hand side of the iff does not depend on choosing an
extension large enough.

Mathlib has the `←` direction. `isSolvable_gal_of_irreducible` and
`isSolvable_gal_minpoly` in `Mathlib/FieldTheory/AbelRuffini.lean` give:
if a root of `p` lies in `solvableByRad F E` (in any ambient extension
`E`), then its minimal-polynomial Galois group is solvable. The file
header docstring explicitly states "this file proves **one direction**
of the Abel–Ruffini theorem". The `→` direction — solvable Galois group
implies all roots lie in `solvableByRad` — is the Kummer-theory content
(`solvableByRad_of_isSolvable_minpoly` / `isSolvableByRad_of_isCyclic`)
and is not in mathlib (verified against v4.30.0-rc1, with no open
`solvableByRad` / `AbelRuffini` / `kummer` PR targeting the converse as
of 2026-05-27). No irreducibility hypothesis is assumed here: this is the
polynomial-level statement, which over the algebraic closure unfolds via
the splitting tower into the irreducible-factor statement that mathlib
half-proves.

An earlier formulation ranged over an arbitrary ambient field `E`. That
form was disproved by Aristotle and Codex with the witness
`p = X⁵ − 4X + 2` over `F = E = ℚ` — the LHS held vacuously (`p` has no
rational roots) while `p.Gal ≅ S₅` is unsolvable. The fix is the
algebraic closure on the LHS, which contains all roots and thereby
restores the intended iff.
-/

open Polynomial IntermediateField

/-- **Solvable extensions ↔ solvable groups** (full iff). For a field
`F` of characteristic zero and a nonzero `p : F[X]`, every root of `p`
in `AlgebraicClosure F` lies in `solvableByRad F (AlgebraicClosure F)`
iff `p.Gal` is solvable. -/
@[eval_problem]
theorem solvable_iff_solvableByRad (F : Type*) [Field F] [CharZero F]
    (p : F[X]) (_hp : p ≠ 0) :
    (∀ x : AlgebraicClosure F, aeval x p = 0 →
        x ∈ solvableByRad F (AlgebraicClosure F)) ↔ IsSolvable p.Gal := by
  sorry

end Algebra
end LeanEval
