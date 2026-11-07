import Definitions.Def_ABHS2004_Realizability

namespace ABHS2004

theorem theorem_4_7 {Δ Γ : ProofContext} {M : ProofTerm} {A : Formula}
    (hd : Derives Δ Γ M A)
    (hfresh : FreshRealizerVars Δ Γ M A) :
    WeaklyTyped (extractProof M) (tau A) ∧
    (∀ v ∈ freeVarOccurrences (extractProof M),
      v ∈ extractCtx Δ ∨ v ∈ extractCtx Γ) ∧
    HasType (extractCleaned M) (tauClean A) ∧
    (∀ v ∈ freeVarOccurrences (extractCleaned M),
      v ∈ extractCleanCtx Γ) := by sorry

end ABHS2004
