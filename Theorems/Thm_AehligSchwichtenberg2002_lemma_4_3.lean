import Definitions.Def_AehligSchwichtenberg2002_Bounds

namespace AehligSchwichtenberg2002

theorem lemma_4_3 {Γ : Context} {t : Term}
    (ht : HasType Γ t .diamond) :
    Γ ≠ [] ∧ freeVars t ≠ [] := by sorry

end AehligSchwichtenberg2002
