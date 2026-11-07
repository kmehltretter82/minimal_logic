import Definitions.Def_Schwichtenberg1976V2_Lambda

namespace Schwichtenberg1976V2

/-- **Schwichtenberg's Definability Theorem** (pp. 113–114):
A `k`-ary numerical function `f : (Fin k → Nat) → Nat` is λ-definable over the Church
numeral type `ν = (0 → 0) → (0 → 0)` in the simply typed λ-calculus if and only if
`f` is an extended polynomial (`IsExtendedPolyInd f`), and if and only if `f` is definable
from polynomials by case distinction on the vanishing or non-vanishing of its arguments
(`IsPiecewisePolynomial k f`). -/
theorem definable_iff_extended_polynomial
    (k : Nat) (f : (Fin k → Nat) → Nat) :
    (IsPiecewisePolynomial k f ↔ IsExtendedPolyInd f) ∧
    (IsLambdaDefinable k f ↔ IsExtendedPolyInd f) ∧
    (IsLambdaDefinable k f ↔ IsPiecewisePolynomial k f) := by
  sorry

end Schwichtenberg1976V2
