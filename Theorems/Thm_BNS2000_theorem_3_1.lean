import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Theorem 3.1 (Closure under reduction)** (Section 3, p. 21):
Let `r` be an `RA`-term.
(1) If `r → r'`, then `r'` is an `RA`-term.
(2) If `x` is affinable in `r` (with `x` incomplete) and `nf_r` is the normal form `nf(r)`,
    then `x` is affinable in `nf(r)`. -/
theorem theorem_3_1 (r : Term) (hr : IsRATerm r) :
    (∀ r' : Term, Step r r' → IsRATerm r') ∧
    (∀ (x : Var) (nf_r : Term),
      x.ty.isIncomplete = true →
      IsAffinable x r →
      IsNormalFormOf r nf_r →
      IsAffinable x nf_r) := by
  sorry

end BNS2000
