import Definitions.Def_ABHS2004_TermSystem

namespace ABHS2004

theorem proposition_2_13 {w : Term} {τ : Ty}
    (ht : HasType w τ) (hac : IsAlmostClosed w) (hnorm : IsNormal w) :
    HasCanonicalNormalForm τ w := by sorry

end ABHS2004
