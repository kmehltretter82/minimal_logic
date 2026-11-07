import Definitions.Def_BergerSchwichtenberg1991_Models

namespace BergerSchwichtenberg1991

universe u

theorem lemma_4 (M : AdmissibleModel.{u}) :
    (∀ r : Term,
      M.eqM .base (M.f_extract (M.appM M.emb (M.codeTerm r)))
        (M.codeTerm (EXTRACT (EMB r)))) ∧
    (∀ r : Term,
      M.eqM M.tyF (M.appM M.emb (M.f_extract (M.appM M.emb (M.codeTerm r))))
        (M.appM M.emb (M.codeTerm r))) ∧
    (∀ r s : Term,
      M.eqM M.tyF
        (M.f_app (M.appM M.emb (M.codeTerm r)) (M.appM M.emb (M.codeTerm s)))
        (M.appM M.emb (M.codeTerm (.app r s)))) ∧
    (∀ (a : M.Dom (.arr M.tyIdx .base)) (r : Term),
      (∀ k : Index, M.eqM .base (M.appM a (M.codeIdx k)) (M.codeTerm (EMB r k))) →
      M.eqM M.tyF (M.fam a) (M.appM M.emb (M.codeTerm r))) := by sorry

end BergerSchwichtenberg1991
