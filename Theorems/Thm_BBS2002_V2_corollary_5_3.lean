import Definitions.Def_BBS2002_V2_Realizability

namespace BBS2002.V2

/-- Classical extraction for definite assumptions and one goal formula. The object terms
realizing the formulas are independent of `M`; a proof may retain free object parameters,
but must have no free assumption variables. -/
theorem corollary_5_3
    (Ds : List Formula) (G : Formula) (y : Var) (dummy : Term)
    (hDs : ∀ D ∈ Ds, IsDefiniteFormula D)
    (hG : IsGoalFormula G)
    (hyDs : ∀ D ∈ Ds, y ∉ freeVarsFormula D)
    (hDummyTy : HasType dummy y.ty)
    (hDummyClosed : IsClosedTerm dummy) :
    ∃ (ts : (j : Fin Ds.length) → Realizer (tau y.ty (substBotWithX (Ds.get j))))
      (s : Term),
      (∀ j, (ts j).Typed) ∧
      (∀ j, ∀ t₀ ∈ (ts j).toOption, ∀ x ∈ freeVars t₀, x ∈ freeVarsFormula (Ds.get j)) ∧
      HasType s
        (.arr y.ty (match tau y.ty (substBotWithX G) with
          | none => y.ty
          | some ρ => .arr ρ y.ty)) ∧
      (∀ x ∈ freeVars s, x ∈ freeVarsFormula G ∧ x ≠ y) ∧
      (∀ M : ProofTerm,
        Derivable SysConfig.Z0 M (Formula.impMany Ds (goalImpliesBot [y] [G])) →
        freeAssumpVars M = [] →
        AdmissibleForExtraction y.ty dummy (substBotProof M) →
        ∃ p : Term,
          extractRaw y.ty dummy (substBotProof M) = some p ∧
          let output := .app (applyOptTerms p (List.ofFn (fun j ↦ (ts j).toOption))) s
          HasType output y.ty ∧
          Provable SysConfig.Z (Formula.impMany Ds (substFormula G y output))) := by
  sorry

end BBS2002.V2
