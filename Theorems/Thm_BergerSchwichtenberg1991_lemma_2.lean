import Definitions.Def_BergerSchwichtenberg1991_Syntax

namespace BergerSchwichtenberg1991

theorem lemma_2 :
    (∀ r s : Term, AlphaEq r s ↔ EMB r = EMB s) ∧
    (∀ r : Term, AlphaEq (EXTRACT (EMB r)) r) ∧
    (∀ (r : Term) (k : Index), EMB (EMB r k) k = EMB r k) := by sorry

end BergerSchwichtenberg1991
