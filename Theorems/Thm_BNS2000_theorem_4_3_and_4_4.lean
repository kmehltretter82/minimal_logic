import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Theorem 4.3 and Corollary 4.4 (Base Normalisation)** (Section 4, p. 24):
1. (**Theorem 4.3**): For every `R`-free `RS`-term `t` of ground type and numeral environment
   `n⃗; x⃗` (`IsNumeralEnv env`) such that `FV(t) ⊆ x⃗`:
   (i) the register-machine algorithm `nf(t; n⃗; x⃗)` (`NFEval`) computes the numeral normal form
       `out = nf(t[n⃗/x⃗])` in at most `2 |t|` steps,
   (ii) the number of used registers is `≤ |t| + #n⃗`, and
   (iii) the maximum length `maxLen` of any term occurring in the computation satisfies
         `maxLen ≤ |t| + max |nᵢ|`.
2. (**Corollary 4.4, Base Normalisation**): For every closed `R`-free `RS`-term `t` of ground
   type, the numeral `nf(t)` is computed in at most `2 |t|` steps using `≤ |t|` registers,
   with every term occurring in the computation having length `≤ |t|`. -/
theorem theorem_4_3_and_4_4 :
    (∀ (t : Term) (τ : Ty) (env : List (Var × Term)),
      IsRSTerm t →
      isRFree t = true →
      HasType t τ →
      τ.isGround = true →
      IsNumeralEnv env →
      (∀ v ∈ freeVars t, v ∈ env.map Prod.fst) →
      ∃ (out : Term) (steps regs maxLen : Nat),
        NFEval t env out steps regs maxLen ∧
        IsNormalFormOf (substEnv t env) out ∧
        isNumeral out = true ∧
        steps ≤ 2 * termLength t ∧
        regs ≤ termLength t + env.length ∧
        maxLen ≤ termLength t + maxEnvTermLength env) ∧
    (∀ (t : Term) (τ : Ty),
      IsRSTerm t →
      isRFree t = true →
      IsClosed t →
      HasType t τ →
      τ.isGround = true →
      ∃ (out : Term) (steps regs maxLen : Nat),
        NFEval t [] out steps regs maxLen ∧
        IsNormalFormOf t out ∧
        isNumeral out = true ∧
        steps ≤ 2 * termLength t ∧
        regs ≤ termLength t ∧
        maxLen ≤ termLength t) := by
  sorry

end BNS2000
