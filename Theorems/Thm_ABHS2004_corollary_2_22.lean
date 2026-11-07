import Definitions.Def_ABHS2004_TermSystem

namespace ABHS2004

theorem corollary_2_22 {r : Term} {ρ : Ty} (ht : HasType r ρ) :
    (∀ (n : Nat) (r' : Term), RedStepBounded n r r' → theta n r' < theta n r) ∧
    (∀ (k : Nat) (r' : Term), RedSteps k r r' → k ≤ theta (freeVarCount r) r) := by sorry

end ABHS2004
