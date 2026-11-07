import Definitions.Def_ABHS2004_TermSystem

namespace ABHS2004

theorem lemma_2_11 {r s : Term} {ρ : Ty}
    (ht : HasType r ρ) (hred : RedStep r s) :
    HasType s ρ ∧ ∀ v ∈ freeVarOccurrences s, v ∈ freeVarOccurrences r := by sorry

end ABHS2004
