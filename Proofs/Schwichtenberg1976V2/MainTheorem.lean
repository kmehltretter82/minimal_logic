import Proofs.Schwichtenberg1976V2.Necessity

/-!
# Schwichtenberg's definability theorem (pp. 113–114)

A numerical function is λ-definable over `ν = (0 → 0) → (0 → 0)` iff it is an extended
polynomial, iff it is a piecewise polynomial. The proof is constructive: it depends only on
`propext` and `Quot.sound`.
-/

namespace Schwichtenberg1976V2.Proofs

open Schwichtenberg1976V2

/-- **Main goal** (`definable_iff_extended_polynomial`, pp. 113–114). -/
theorem definable_iff_extended_polynomial
    (k : Nat) (f : (Fin k → Nat) → Nat) :
    (IsPiecewisePolynomial k f ↔ IsExtendedPolyInd f) ∧
    (IsLambdaDefinable k f ↔ IsExtendedPolyInd f) ∧
    (IsLambdaDefinable k f ↔ IsPiecewisePolynomial k f) :=
  ⟨piecewise_iff_extended f,
    ⟨fun h => piecewise_extended (necessity h), sufficiency⟩,
    ⟨necessity, fun h => sufficiency (piecewise_extended h)⟩⟩

end Schwichtenberg1976V2.Proofs
