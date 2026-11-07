import Definitions.Def_AehligSchwichtenberg2002_Bounds

namespace AehligSchwichtenberg2002

theorem theorem_4_8 {Γ : Context} {t : Term} {τ : Ty}
    (ht : HasType Γ t τ) :
    (∀ (N : Nat) (t' : Term),
      freeVarCard t ≤ N → RedStep t t' → stepMeasure t' N < stepMeasure t N) ∧
    (∀ (k : Nat) (t' : Term),
      RedSteps k t t' → k ≤ stepMeasure t (freeVarCard t)) := by sorry

end AehligSchwichtenberg2002
