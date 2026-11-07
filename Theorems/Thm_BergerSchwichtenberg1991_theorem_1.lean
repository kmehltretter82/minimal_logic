import Definitions.Def_BergerSchwichtenberg1991_Models

namespace BergerSchwichtenberg1991

universe u

theorem theorem_1 (M : AdmissibleModel.{u}) (IF : InversionFunctionals M) :
    (∀ (ρ : Ty) (a : M.Dom ρ),
      M.IsLambdaDefinable ρ a →
      ∃ t : Term,
        IF.IsPeResult ρ a t ∧
        IsClosed t ∧
        IsLongBetaNormal ρ t ∧
        ∀ η : M.Env, M.eqM ρ (M.eval t η ρ) a) ∧
    (∀ (ρ : Ty) (r rStar : Term) (θ : Substitution),
      HasType r ρ →
      HasType rStar ρ →
      IsLongBetaNormal ρ rStar →
      BetaEtaEq r rStar →
      IsWellTypedSubst θ →
      IF.IsPeResult ρ (M.eval r (IF.etaSubst θ) ρ) (EXTRACT (EMB (applySubst θ rStar))) ∧
      AlphaEq (EXTRACT (EMB (applySubst θ rStar))) (applySubst θ rStar)) ∧
    (∀ (ρ : Ty) (r s : Term),
      HasType r ρ →
      HasType s ρ →
      M.ModelsEq ρ r s →
      BetaEtaEq r s) := by sorry

end BergerSchwichtenberg1991
