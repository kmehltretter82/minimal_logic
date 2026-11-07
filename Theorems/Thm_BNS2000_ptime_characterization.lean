import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Characterization of Polynomial-Time Computability by Higher-Type Ramified Affinable Recursion**
(Sections 1 & 5, pp. 18, 26–27):
A numerical function `F : (Fin k → Nat) → Nat` is denoted by a closed `RA`-term `t` of type
`!ι → ⋯ → !ι → ι` if and only if `F` is computable in polynomial time (characterized via the
Bellantoni–Cook safe recursion function algebra `BCFunc k 0` together with a polynomial bound
`p_t` on the normalization complexity of `t (!n₁) ... (!nₖ)`). -/
theorem ptime_characterization
    (k : Nat) (F : (Fin k → Nat) → Nat) :
    (∃ t : Term, RADenotesTwoSorted (m := k) (n := 0) t (fun xs _ => F xs)) ↔
    (∃ f : BCFunc k 0, ∀ xs : Fin k → Nat, F xs = evalBC f xs Fin.elim0) := by
  sorry

end BNS2000
