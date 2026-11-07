import Definitions.Def_AehligSchwichtenberg2002_Syntax

namespace AehligSchwichtenberg2002

theorem proposition_3_6 {Γ : Context} {t : Term}
    (hac : ∀ v ∈ Γ, v.ty = .diamond) (hnorm : IsNormal t) :
    (∀ τ : Ty, HasType Γ t (.list τ) → IsListTerm t) ∧
    (HasType Γ t .bool → t = .const .tt ∨ t = .const .ff) ∧
    (HasType Γ t .diamond → ∃ x : Var, x.ty = .diamond ∧ t = .var x) := by sorry

end AehligSchwichtenberg2002
