import Definitions.Def_BergerSchwichtenberg1991_Models

namespace BergerSchwichtenberg1991

universe u

theorem lemma_5 (M : AdmissibleModel.{u}) (IF : InversionFunctionals M)
    {ρ : Ty} {r : Term} (θ : Substitution)
    (ht : HasType r ρ)
    (hnorm : IsLongBetaNormal ρ r)
    (hθ : IsWellTypedSubst θ) :
    M.eqM M.tyF
      (M.appM (IF.Phi ρ) (M.eval r (IF.etaSubst θ) ρ))
      (M.appM M.emb (M.codeTerm (applySubst θ r))) ∧
    (∀ hbase : ρ = .base,
      M.eqM .base
        (hbase ▸ M.eval r (IF.etaSubst θ) ρ)
        (M.codeTerm (EXTRACT (EMB (applySubst θ r))))) := by sorry

end BergerSchwichtenberg1991
