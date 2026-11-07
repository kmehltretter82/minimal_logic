import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Theorem 4.5 (`R`-Elimination)** (Section 4, p. 24):
Let `t` be an `RS`-term of safe or ground type `τ`. Then there exists a univariate polynomial
`q_t : Nat → Nat` (`IsUnivariatePoly q_t`) such that for every environment `n⃗; x⃗` of closed
ground-type `R`-free `RS`-terms (`IsClosedGroundRFreeRSEnv env`) with `FV(t[n⃗/x⃗])` all safe,
there exists an `R`-free `RS`-term `rf_t` equivalent to `t[n⃗/x⃗]` (with `FV(rf_t) ⊆ FV(t[n⃗/x⃗])`
and `|rf_t| ≤ q_t(∑ |nᵢ|)`) such that if `τ` is ground and `t[n⃗/x⃗]` is closed, `rf_t`
normalizes via `NFEval` in at most `2 · q_t(∑ |nᵢ|)` steps using at most `q_t(∑ |nᵢ|)` registers. -/
theorem theorem_4_5
    (t : Term) (τ : Ty)
    (ht : IsRSTerm t)
    (hτ : HasType t τ)
    (hSafeOrGround : τ.isSafe = true ∨ τ.isGround = true) :
    ∃ q_t : Nat → Nat,
      IsUnivariatePoly q_t ∧
      ∀ env : List (Var × Term),
        IsClosedGroundRFreeRSEnv env →
        (∀ v ∈ freeVars (substEnv t env), v.ty.isSafe = true) →
        ∃ rf_t : Term,
          IsRSTerm rf_t ∧
          isRFree rf_t = true ∧
          HasType rf_t τ ∧
          TermEquiv rf_t (substEnv t env) ∧
          (∀ v ∈ freeVars rf_t, v ∈ freeVars (substEnv t env)) ∧
          termLength rf_t ≤ q_t (sumEnvTermLength env) := by
  sorry

end BNS2000
