import Definitions.Def_ABHS2004_Realizability

namespace ABHS2004.Audit

def badAx : CoreAxiom := .ax16 .diamond (.var ⟨0, .diamond⟩) (.var ⟨0, .diamond⟩)

theorem badAx_valid : badAx.IsValid := by
  exact ⟨WeaklyTyped.var _, WeaklyTyped.var _⟩

theorem badAx_derivable : Derives [] [] (.ax badAx) badAx.formula := by
  apply Derives.axiomRule
  · simp [DisjointProofCtx]
  · exact badAx_valid

theorem badAx_fresh : FreshRealizerVars [] [] (.ax badAx) badAx.formula := by
  simp [FreshRealizerVars, allAssumpVars]

theorem badAx_extraction_not_typed :
    ¬ WeaklyTyped (extractProof (.ax badAx)) (tau badAx.formula) := by
  intro h
  change WeaklyTyped (.lam ⟨0, .diamond⟩ (.var ⟨0, .diamond⟩))
    (.lolli .unit (.lolli .diamond .diamond)) at h
  cases h

#print axioms badAx_extraction_not_typed
#print axioms badAx_derivable
#print axioms badAx_fresh

/-- All four conjuncts of the uploaded Theorem 4.7, with its exact hypotheses. -/
def Submitted4_7 : Prop :=
  ∀ {Δ Γ : ProofContext} {M : ProofTerm} {A : Formula}
    (hd : Derives Δ Γ M A)
    (hfresh : FreshRealizerVars Δ Γ M A),
    WeaklyTyped (extractProof M) (tau A) ∧
    (∀ v ∈ freeVarOccurrences (extractProof M),
      v ∈ extractCtx Δ ∨ v ∈ extractCtx Γ) ∧
    HasType (extractCleaned M) (tauClean A) ∧
    (∀ v ∈ freeVarOccurrences (extractCleaned M),
      v ∈ extractCleanCtx Γ)

theorem refute_submitted_4_7 : ¬ Submitted4_7 := by
  intro h
  exact badAx_extraction_not_typed (h badAx_derivable badAx_fresh).1

#print axioms refute_submitted_4_7

end ABHS2004.Audit
