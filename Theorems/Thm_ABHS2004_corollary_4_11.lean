import Definitions.Def_ABHS2004_Realizability

namespace ABHS2004

theorem corollary_4_11 {Δ Γ : ProofContext} {M : ProofTerm}
    {xs : List Var} {y : Var} {A : Formula}
    (hdata_xs : ∀ x ∈ xs, IsDataType x.ty ∧ cleanTy x.ty = x.ty ∧ x.ty ≠ .unit)
    (hdata_y : IsDataType y.ty ∧ cleanTy y.ty = y.ty ∧ y.ty ≠ .unit)
    (hnodup : (xs ++ [y]).Nodup)
    (hA : IsExistAndDisjFree A)
    (hac : IsAlmostClosedDerivation Δ Γ)
    (hd : Derives Δ Γ M
      (Formula.allRel xs (.ex y (.tensor (.existPred y.ty (.var y)) A))))
    (hfresh : FreshRealizerVars Δ Γ M
      (Formula.allRel xs (.ex y (.tensor (.existPred y.ty (.var y)) A)))) :
    ∃ (B : Nat → Nat) (k : Nat),
      BoundedByPolyOfDegree B (Nat.max (iterNesting (extractCleaned M)) 1) ∧
      ∀ ws : List Term,
        ValidDataInputs (extractCleaned M) (xs.map Var.ty) ws →
        ∃ (steps : Nat) (w : Term),
          RedSteps steps (Term.appMany (extractCleaned M) ws) w ∧
          IsDataObject y.ty w ∧
          steps ≤ B (totalTermLength ws) ∧
          termLength w ≤ totalTermLength ws + k ∧
          freeVarCount w ≤ totalFreeVarCount ws + k ∧
          Provable (mrContext (Δ ++ Γ)) []
            (substFormula (substFormulaMany A (xs.zip ws)) y w) := by sorry

end ABHS2004
