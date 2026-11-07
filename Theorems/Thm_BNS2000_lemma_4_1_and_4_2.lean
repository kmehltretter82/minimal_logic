import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Lemma 4.1 and Lemma 4.2 (Sharing)** (Section 4, p. 22):
1. (**Lemma 4.1**): Let `t` be a well-typed ground-type term whose free variables are of
   ground type. Then in the normal form `nf(t)` of `t`, all occurring variables (free or bound)
   are safe or ground (`AllVarsSafeOrGround nf_t`).
2. (**Lemma 4.2, Sharing**): Let `t` be a well-typed term such that for every subterm `λx. s`
   with `x` higher-type incomplete, the variable `x` is affinable in `s`
   (`SatisfiesDirectAffinability t`). Then by repeated ground-type `β_ι`-expansions
   `r[a/y^τ] ↦ (λy^τ. r) a` one can construct a term `t_β` (`BetaIotaExpandsTo t t_β`,
   hence `ReducesTo t_β t`) such that for every subterm `λx. s` in `t_β` with `x` higher-type
   incomplete, `FO(x, s) ≤ 1` (`HasLinearHigherIncompleteBinders t_β`). -/
theorem lemma_4_1_and_4_2 :
    (∀ (t nf_t : Term) (τ : Ty),
      HasType t τ →
      τ.isGround = true →
      (∀ v ∈ freeVars t, v.ty.isGround = true) →
      IsNormalFormOf t nf_t →
      AllVarsSafeOrGround nf_t) ∧
    (∀ (t : Term) (τ : Ty),
      HasType t τ →
      SatisfiesDirectAffinability t →
      ∃ t_β : Term,
        HasType t_β τ ∧
        (SatisfiesR t → SatisfiesR t_β) ∧
        BetaIotaExpandsTo t t_β ∧
        ReducesTo t_β t ∧
        HasLinearHigherIncompleteBinders t_β) := by
  sorry

end BNS2000
