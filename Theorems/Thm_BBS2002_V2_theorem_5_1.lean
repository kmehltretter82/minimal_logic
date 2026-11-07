import Definitions.Def_BBS2002_V2_Realizability

namespace BBS2002.V2

theorem theorem_5_1
    (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (Ds Gs : List Formula) (ys : List Var)
    (ts : (j : Fin Ds.length) → Realizer (tau ν (substBotWithX (Ds.get j))))
    (ws : Fin Gs.length → Option Var) (ss : Fin Gs.length → Term)
    (vs : Fin Gs.length → Var) (r : Term) (M : ProofTerm)
    (hDs : ∀ D ∈ Ds, FormulaWellTyped D ∧ isLFormula D = true)
    (hGs : ∀ G ∈ Gs, FormulaWellTyped G ∧ isLFormula G = true)
    (htsTy : ∀ j, (ts j).Typed)
    (hwsTy : ∀ i, (ws i).map Var.ty = tau ν (substBotWithX (Gs.get i)))
    (hvsTy : ∀ i, (vs i).ty = ν)
    (hssTy : ∀ i,
      HasType (ss i)
        (match tau ν (substBotWithX (Gs.get i)) with
         | none => .arr ν ν
         | some ρ => .arr ρ (.arr ν ν)))
    (hrTy : HasType r (Ty.arrMany (ys.map Var.ty) ν))
    (hBindersFresh :
      let wVars := (List.ofFn ws).filterMap id
      let vVars := List.ofFn vs
      (ys ++ wVars ++ vVars).Nodup ∧
      (∀ y ∈ ys, ∀ D ∈ Ds, y ∉ freeVarsFormula D) ∧
      (∀ z ∈ wVars ++ vVars, ∀ i, z ∉ freeVars (ss i)) ∧
      (∀ z ∈ ys ++ wVars, z ∉ freeVars r) ∧
      (∀ z ∈ wVars ++ vVars, ∀ D ∈ Ds, z ∉ freeVarsFormula D) ∧
      (∀ z ∈ wVars ++ vVars, ∀ G ∈ Gs, z ∉ freeVarsFormula G) ∧
      (∀ z ∈ ys ++ wVars ++ vVars,
        z = comp.var ∨ z ∉ freeVarsFormula comp.body))
    (h7 : ∀ j,
      Provable SysConfig.Z
        (Formula.impMany Ds (mrFormula ν comp (substBotWithX (Ds.get j)) (ts j))))
    (h8 : ∀ i,
      Provable SysConfig.Z
        (Formula.impMany Ds
          (.imp
            (mrFormula ν comp (substBotWithX (Gs.get i))
              (Realizer.ofOption ((ws i).map Term.var)
                (by simpa only [Option.isSome_map] using congrArg Option.isSome (hwsTy i))))
            (.imp
              (.imp (Gs.get i) (comp.apply (.var (vs i))))
              (comp.apply (applyGoalRealizer (ss i) (ws i) (.var (vs i))))))))
    (h9 : Provable SysConfig.Z
      (Formula.impMany Ds
        (Formula.allMany ys
          (Formula.impMany Gs (comp.apply (Term.appMany r (ys.map Term.var)))))))
    (hM : Derivable SysConfig.Z0 M (Formula.impMany Ds (goalImpliesBot ys Gs)))
    (hMClosed : freeAssumpVars M = [])
    (hMAdm : AdmissibleForExtraction ν dummy (substBotProof M)) :
    let s := buildGoalCombinatorTerm ys (List.ofFn ws) (List.ofFn ss) r
    ∃ p : Term,
      extractRaw ν dummy (substBotProof M) = some p ∧
      HasType (.app (applyOptTerms p (List.ofFn fun j => (ts j).toOption)) s) ν ∧
      Provable SysConfig.Z
        (Formula.impMany Ds
          (comp.apply (.app (applyOptTerms p (List.ofFn fun j => (ts j).toOption)) s))) := by
  sorry

end BBS2002.V2
