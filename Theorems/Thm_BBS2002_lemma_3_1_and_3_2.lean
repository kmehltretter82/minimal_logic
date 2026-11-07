import Definitions.Def_BBS2002_Extraction

namespace BBS2002

/-- Lemma 3.1 (equations (3)–(6), p. 6) and Lemma 3.2 (p. 9):
1. (**Lemma 3.1**) For every definite formula `D` and goal formula `G`:
   - (3) If `D` is relevant, `Z^X ⊢ (¬D → X) → D^X`.
   - (4) `Z^X ⊢ D → D^X`.
   - (5) If `G` is irrelevant, `Z^X ⊢ G^X → G`.
   - (6) `Z^X ⊢ G^X → (G → X) → X`.
2. (**Lemma 3.2**) For every list of goal formulas `G⃗ = G₁, ..., Gₙ`,
   `Z^X ⊢ (G⃗ → X) → G⃗^X → X`. -/
theorem lemma_3_1_and_3_2 :
    (∀ D : Formula,
      IsDefiniteFormula D →
      (isRelevant D = true →
        Provable SysConfig.ZX (.imp (.imp (Formula.neg D) .varX) (substBotWithX D))) ∧
      Provable SysConfig.ZX (.imp D (substBotWithX D))) ∧
    (∀ G : Formula,
      IsGoalFormula G →
      (isIrrelevant G = true →
        Provable SysConfig.ZX (.imp (substBotWithX G) G)) ∧
      Provable SysConfig.ZX (.imp (substBotWithX G) (.imp (.imp G .varX) .varX))) ∧
    (∀ Gs : List Formula,
      (∀ G ∈ Gs, IsGoalFormula G) →
      Provable SysConfig.ZX
        (.imp
          (Formula.impMany Gs .varX)
          (Formula.impMany (Gs.map substBotWithX) .varX))) := by
  sorry

end BBS2002
