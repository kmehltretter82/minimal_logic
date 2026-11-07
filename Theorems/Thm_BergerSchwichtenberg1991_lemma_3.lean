import Definitions.Def_BergerSchwichtenberg1991_Models

namespace BergerSchwichtenberg1991

universe u

theorem lemma_3 (M : PRModel.{u}) (N : EffectiveNumbering)
    (hExtractComb :
      ∀ indextBar : M.Dom (.arr .base (.arr .base .base)),
        ∃ extractBar : M.Dom (.arr (.arr .base .base) .base),
          ∀ a : M.Dom (.arr .base .base),
            M.eqM .base (M.appM extractBar a)
              (M.appM a
                (M.appM
                  (M.appM indextBar (M.appM a (M.nu (N.natOfIdx epsIdx))))
                  (M.appM a (M.nu (N.natOfIdx zeroIdx))))))
    (hStepComb :
      ∀ (abstBar : Ty → M.Dom (.arr .base (.arr .base .base)))
        (funBar appendBar : M.Dom (.arr .base (.arr .base .base)))
        (ρ : Ty) (body : M.Dom .base → M.Dom .base),
        (∀ p₁ p₂ : M.Dom .base, M.eqM .base p₁ p₂ → M.eqM .base (body p₁) (body p₂)) →
        ∃ step : M.Dom (.arr .base .base),
          ∀ p : M.Dom .base,
            M.eqM .base (M.appM step p)
              (M.appM (M.appM (abstBar ρ) p)
                (M.appM (M.appM funBar (body p))
                  (M.appM (M.appM appendBar p) (M.nu (N.natOfIdx zeroIdx)))))) :
    ∃ A : AdmissibleModel.{u},
      A.toLambdaModel = M.toLambdaModel ∧
      A.tyF = .base ∧
      A.tyIdx = .base ∧
      (∀ r : Term, HEq (A.codeTerm r) (M.nu (N.natOfTerm r))) ∧
      (∀ k : Index, HEq (A.codeIdx k) (M.nu (N.natOfIdx k))) := by sorry

end BergerSchwichtenberg1991
