import Definitions.Def_AehligSchwichtenberg2002_Syntax

namespace AehligSchwichtenberg2002

theorem lemma_3_5 {Γ : Context} {t t' : Term} {τ : Ty}
    (ht : HasType Γ t τ) (hred : RedStep t t') :
    HasType Γ t' τ := by sorry

end AehligSchwichtenberg2002
