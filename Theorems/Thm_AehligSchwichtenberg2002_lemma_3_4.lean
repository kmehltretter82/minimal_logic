import Definitions.Def_AehligSchwichtenberg2002_Syntax

namespace AehligSchwichtenberg2002

theorem lemma_3_4 {Γ₁ Γ₁' Γ₂ Γ : Context} {x : Var} {t s : Term} {τ : Ty}
    (hu₁ : IsCtxUnion Γ₁ [x] Γ₁')
    (ht : HasType Γ₁' t τ)
    (hs : HasType Γ₂ s x.ty)
    (hdj : IsDisjointCtxUnion Γ₁ Γ₂ Γ) :
    HasType Γ (substTerm t x s) τ := by sorry

end AehligSchwichtenberg2002
