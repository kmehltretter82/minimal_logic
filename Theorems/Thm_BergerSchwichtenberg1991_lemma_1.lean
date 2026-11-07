import Definitions.Def_BergerSchwichtenberg1991_Syntax

namespace BergerSchwichtenberg1991

theorem lemma_1 (k : Index) :
    (∀ r s : Term, AlphaEq r s → alphaRename k r = alphaRename k s) ∧
    (∀ r : Term, (∀ m ∈ freeIndices r, ¬ IsPrefixOf k m) → AlphaEq (alphaRename k r) r) := by sorry

end BergerSchwichtenberg1991
