import Definitions.Def_BergerSchwichtenberg1991_Models

namespace BergerSchwichtenberg1991

universe u

theorem completeness_pr_models :
    (∀ (M : PRModel.{u}) (N : EffectiveNumbering)
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
                     (M.appM (M.appM appendBar p) (M.nu (N.natOfIdx zeroIdx))))))
       (hIF :
         ∀ A : AdmissibleModel.{u},
           A.toLambdaModel = M.toLambdaModel →
           Nonempty (InversionFunctionals A)),
      ∃ (A : AdmissibleModel.{u}) (IF : InversionFunctionals A),
        A.toLambdaModel = M.toLambdaModel ∧
        (∀ t : Term, HEq (A.codeTerm t) (M.nu (N.natOfTerm t))) ∧
        (∀ (ρ : Ty) (a : A.Dom ρ),
          A.IsLambdaDefinable ρ a →
          ∃ r : Term,
            HasType r ρ ∧
            IsClosed r ∧
            IsLongBetaNormal ρ r ∧
            A.eqM .base (IF.invCode ρ a) (A.codeTerm r) ∧
            ∀ η : A.Env, A.eqM ρ (A.eval r η ρ) a) ∧
        (∀ (ρ : Ty) (r s : Term),
          HasType r ρ →
          HasType s ρ →
          M.ModelsEq ρ r s →
          BetaEtaEq r s)) := by sorry

end BergerSchwichtenberg1991
