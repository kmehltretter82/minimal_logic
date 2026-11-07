import Definitions.Def_AehligSchwichtenberg2002_Bounds

namespace AehligSchwichtenberg2002

theorem lemma_4_7 {Γ₁ Γ₂ : Context} {t s : Term} {τ ρ : Ty} (x : Var)
    (ht : HasType Γ₁ t τ)
    (hs : HasType Γ₂ s ρ)
    (hdj : DisjointCtx Γ₁ Γ₂) :
    PolyLe (theta (substTerm t x s)) (fun m => theta t m + theta s m) := by sorry

end AehligSchwichtenberg2002
