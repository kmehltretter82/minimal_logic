import Definitions.Def_ABHS2004_Realizability

namespace ArithmeticCleaningAudit
open ABHS2004

def d : Var := ⟨10, .diamond⟩
def u : Var := ⟨11, .unit⟩
def a : Var := ⟨12, Ty.nat⟩
def step : Term := .lam d (.lam u (.lam a (.var a)))
def iteration : Term := .iter (.const (.nil .unit)) step

theorem iteration_typed : HasType iteration (.lolli Ty.nat Ty.nat) := by
  exact .iter (.const (.nil .unit)) (.lam d (.lam u (.lam a (.var a)))) (by rfl)

theorem iteration_closed : IsClosed iteration := by rfl

theorem cleaned_step_loses_element_argument :
    cleanTerm step = .lam d (.lam a (.var a)) := by decide

theorem infer_of_weak {r : Term} {τ : Ty} (h : WeaklyTyped r τ) :
    inferType r = some τ := by
  induction h with
  | var => rfl
  | const => rfl
  | lam x h ih => simp [inferType, ih]
  | app h₁ h₂ ih₁ ih₂ => simp [inferType, ih₁]
  | iter h₁ h₂ ih₁ ih₂ => simp [inferType, ih₂]

theorem cleaned_iteration_untypable :
    ∀ τ, ¬ WeaklyTyped (cleanTerm iteration) τ := by
  intro τ h
  have hbad : inferType (cleanTerm iteration) = none := by decide
  have hgood := infer_of_weak h
  rw [hbad] at hgood
  contradiction

-- This certifies the cleaning utility defect independently of the separate
-- axiom-16 disproof of the submitted Theorem 4.7.
#print axioms iteration_typed
#print axioms iteration_closed
#print axioms cleaned_step_loses_element_argument
#print axioms cleaned_iteration_untypable
end ArithmeticCleaningAudit
