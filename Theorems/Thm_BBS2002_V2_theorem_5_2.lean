import Definitions.Def_BBS2002_V2_Realizability

namespace BBS2002.V2

/-- The realizers for a definite formula and a goal formula retain only their formulas'
free object parameters. The comprehension term is arbitrary; its free parameters need not
be disjoint from the free parameters of either formula. -/
theorem theorem_5_2
    (ν : Ty) (dummy : Term)
    (hDummyTy : HasType dummy ν)
    (hDummyClosed : IsClosedTerm dummy)
    (D G : Formula)
    (hD : IsDefiniteFormula D)
    (hG : IsGoalFormula G) :
    (∃ t : Realizer (tau ν (substBotWithX D)),
      t.Typed ∧
      (∀ t₀ ∈ t.toOption, ∀ x ∈ freeVars t₀, x ∈ freeVarsFormula D) ∧
      ∀ comp : CompTerm ν,
        Provable SysConfig.Z (.imp D (mrFormula ν comp (substBotWithX D) t))) ∧
    (∃ s : Term,
      HasType s
        (match tau ν (substBotWithX G) with
         | none => .arr ν ν
         | some ρ => .arr ρ (.arr ν ν)) ∧
      (∀ x ∈ freeVars s, x ∈ freeVarsFormula G) ∧
      ∀ (comp : CompTerm ν) (w : Option Var) (v : Var),
        v.ty = ν →
        (hw : w.map Var.ty = tau ν (substBotWithX G)) →
        (∀ wVar ∈ w,
          wVar ≠ v ∧
          wVar ∉ freeVarsFormula G ∧
          (wVar = comp.var ∨ wVar ∉ freeVarsFormula comp.body)) →
        v ∉ freeVarsFormula G →
        (v = comp.var ∨ v ∉ freeVarsFormula comp.body) →
        Provable SysConfig.Z
          (.imp
            (mrFormula ν comp (substBotWithX G)
              (Realizer.ofOption (w.map Term.var)
                (by simpa only [Option.isSome_map] using congrArg Option.isSome hw)))
            (.imp
              (.imp G (comp.apply (.var v)))
              (comp.apply (applyGoalRealizer s w (.var v)))))) := by
  sorry

end BBS2002.V2
