import Definitions.Def_ABHS2004_Realizability

namespace ABHS2004

theorem theorem_4_9 {Δ Γ : ProofContext} {M : ProofTerm} {A : Formula}
    (hd : Derives Δ Γ M A)
    (hfresh : FreshRealizerVars Δ Γ M A) :
    Provable (mrContext (Δ ++ Γ)) [] (mr (extractProof M) A) := by sorry

end ABHS2004
