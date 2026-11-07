import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Theorem 5.2** (Section 5, p. 27):
Every function `f(x⃗; y⃗)` in the Bellantoni–Cook safe recursion function algebra `B`
(`f : BCFunc m n`, which characterizes the polynomial-time computable functions) is
denoted by a closed `RA`-term `t_f` of type `!ι → ⋯ → !ι → ι → ⋯ → ι → ι`
(`RADenotesTwoSorted t_f (evalBC f)`). -/
theorem theorem_5_2
    {m n : Nat} (f : BCFunc m n) :
    ∃ t_f : Term, RADenotesTwoSorted t_f (evalBC f) := by
  sorry

end BNS2000
