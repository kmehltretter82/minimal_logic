import Definitions.Def_BBS2002_Arithmetic

namespace BBS2002

/-- Lemmas 2.1, 2.2 (Stability), and 2.3 (Cases) (Section 2, p. 5):
1. (**Lemma 2.1**) For every well-typed `L[X]`-formula `A`, `Z^X ⊢ A ↔ Z_0^X ⊢ A^F`,
   where `F := atom(false)` and `A^F := A[⊥ := F]`.
2. (**Lemma 2.2, Stability**) For every well-typed `L`-formula `A`, `Z ⊢ ¬¬A → A`.
3. (**Lemma 2.3, Cases**) For every well-typed quantifier-free `L`-formula `C` and every
   well-typed `L[X]`-formula `A`, `Z^X ⊢ (¬C → A) → (C → A) → A`. -/
theorem lemmas_2_1_to_2_3 :
    (∀ A : Formula,
      FormulaWellTyped A →
      (Provable SysConfig.ZX A ↔ Provable SysConfig.ZX0 (substBotWithFalse A))) ∧
    (∀ A : Formula,
      FormulaWellTyped A →
      isLFormula A = true →
      Provable SysConfig.Z (.imp (Formula.dneg A) A)) ∧
    (∀ C A : Formula,
      FormulaWellTyped C →
      isLFormula C = true →
      isQuantifierFree C = true →
      FormulaWellTyped A →
      Provable SysConfig.ZX (.imp (.imp (Formula.neg C) A) (.imp (.imp C A) A))) := by
  sorry

end BBS2002
