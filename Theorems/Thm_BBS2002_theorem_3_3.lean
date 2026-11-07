import Definitions.Def_BBS2002_Extraction

namespace BBS2002

/-- Theorem 3.3 (Section 3, p. 9):
Assume that for definite formulas `D⃗` and goal formulas `G⃗` we have
`Z_0 ⊢ D⃗ → ∀y⃗(G⃗ → ⊥) → ⊥`.
Then we also have
`Z^X ⊢ D⃗ → ∀y⃗(G⃗ → X) → X`. -/
theorem theorem_3_3
    (Ds Gs : List Formula) (ys : List Var)
    (hDs : ∀ D ∈ Ds, IsDefiniteFormula D)
    (hGs : ∀ G ∈ Gs, IsGoalFormula G)
    (hZ0 : Provable SysConfig.Z0 (Formula.impMany Ds (goalImpliesBot ys Gs))) :
    Provable SysConfig.ZX (Formula.impMany Ds (goalImpliesX ys Gs)) := by
  sorry

end BBS2002
