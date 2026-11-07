import Definitions.Def_Schwichtenberg1976V2_Lambda

namespace Schwichtenberg1976V2.RegressionAudit

def x : Var := ⟨2, .zero⟩
def y : Var := ⟨3, .zero⟩
def constantX : Term := .lam y (.var x)
def identity : Term := .lam y (.var y)

theorem composition_preserves_first_argument_free_var :
    freeVars (compTerm .zero constantX identity) = [x] := by decide

theorem composition_preserves_second_argument_free_var :
    freeVars (compTerm .zero identity constantX) = [x] := by decide

def zeroVar : Var := ⟨0, .zero⟩
def constantZeroVar : Term := .lam y (.var zeroVar)

theorem iteration_preserves_free_var :
    freeVars (iterTerm constantZeroVar 0 1) = [zeroVar] := by decide

theorem zero_iteration_is_closed :
    freeVars (iterTerm constantZeroVar 0 0) = [] := by decide

theorem bound_only_collision_retains_candidate :
    freshVarFor .zero 2 (.lam x (.var x)) = x := by decide

theorem same_id_different_type_retains_candidate :
    freshVarFor .zero 2 (.var ⟨2, Ty.endo⟩) = x := by decide

-- Literal copies of the previous raw constructors, for preservation evidence.
def oldCompTerm (τ : Ty) (t s : Term) (xId : Nat := 2) : Term :=
  let x : Var := ⟨xId, τ⟩
  .lam x (.app t (.app s (.var x)))

def oldIterTerm (α : Term) (xId : Nat := 0) (n : Nat) : Term :=
  let x : Var := ⟨xId, .zero⟩
  .lam x (iterApp α (.var x) n)

def oldAddComb : Term :=
  let F : Var := ⟨3, Ty.nu⟩
  let G : Var := ⟨4, Ty.nu⟩
  let α : Var := ⟨1, Ty.endo⟩
  .lam F (.lam G (.lam α (oldCompTerm .zero
    (.app (.var F) (.var α)) (.app (.var G) (.var α)) 0)))

def oldMulComb : Term :=
  let F : Var := ⟨3, Ty.nu⟩
  let G : Var := ⟨4, Ty.nu⟩
  .lam F (.lam G (oldCompTerm Ty.endo (.var F) (.var G) 1))

def oldConstComb (k : Nat) : Term :=
  let F : Var := ⟨3, Ty.nu⟩
  let α : Var := ⟨1, Ty.endo⟩
  .lam F (.lam α (oldIterTerm (.var α) 0 k))

theorem addComb_syntax_preserved : addComb = oldAddComb := rfl
theorem mulComb_syntax_preserved : mulComb = oldMulComb := rfl
theorem constComb_syntax_preserved (k : Nat) : constComb k = oldConstComb k := rfl

#print axioms composition_preserves_first_argument_free_var
#print axioms composition_preserves_second_argument_free_var
#print axioms iteration_preserves_free_var
#print axioms zero_iteration_is_closed
#print axioms bound_only_collision_retains_candidate
#print axioms same_id_different_type_retains_candidate
#print axioms addComb_syntax_preserved
#print axioms mulComb_syntax_preserved
#print axioms constComb_syntax_preserved
end Schwichtenberg1976V2.RegressionAudit
