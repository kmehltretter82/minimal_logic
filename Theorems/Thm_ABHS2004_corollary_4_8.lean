import Definitions.Def_ABHS2004_Realizability

namespace ABHS2004

theorem corollary_4_8 :
    ¬ ClosedProvable (.imp Formula.bot Formula.lozenge) ∧
    ¬ ClosedProvable (.imp Formula.lozenge (.tensor Formula.lozenge Formula.lozenge)) ∧
    ¬ (∀ A B C : Formula,
        ClosedProvable (.imp (.imp A (.imp B C)) (.imp (.conj A B) C))) := by sorry

end ABHS2004
