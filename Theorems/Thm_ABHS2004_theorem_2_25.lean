import Definitions.Def_ABHS2004_TermSystem

namespace ABHS2004

theorem theorem_2_25 {τs : List Ty} {τ : Ty} {r : Term}
    (hdata_in : ∀ σ ∈ τs, IsDataType σ)
    (hdata_out : IsDataType τ)
    (ht : HasType r (Ty.lolliMany τs τ))
    (hac : IsAlmostClosed r) :
    ∃ (B : Nat → Nat) (k : Nat),
      BoundedByPolyOfDegree B (Nat.max (iterNesting r) 1) ∧
      ∀ ws : List Term,
        ValidDataInputs r τs ws →
        ∃ (steps : Nat) (w : Term),
          RedSteps steps (Term.appMany r ws) w ∧
          IsDataObject τ w ∧
          steps ≤ B (totalTermLength ws) ∧
          termLength w ≤ totalTermLength ws + k ∧
          freeVarCount w ≤ totalFreeVarCount ws + k := by sorry

end ABHS2004
