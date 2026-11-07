import Definitions.Def_BBS2002_V2_Realizability

namespace BBS2002.V2

theorem theorem_4_1
    (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (M : ProofTerm) (B : Formula)
    (hDeriv : Derivable SysConfig.ZX M B)
    (hAdm : AdmissibleForExtraction ν dummy M) :
    ∃ r : Realizer (tau ν B),
      r.toOption = extractProgram ν dummy M B ∧
      r.Typed ∧
      ∃ N : ProofTerm,
        Derivable SysConfig.Z N (mrFormula ν comp B r) ∧
        ∀ v ∈ freeAssumpVars N,
          ∃ u ∈ freeAssumpVars M,
            v.formula = mrFormula ν comp u.formula (assumpRealizer ν u) := by
  sorry

end BBS2002.V2
