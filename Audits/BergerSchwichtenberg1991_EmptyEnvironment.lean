import Definitions.Def_BergerSchwichtenberg1991_Models

namespace BergerSchwichtenberg1991.Audit

def ShallowDom : Ty → Type
  | .base => Nat
  | .arr .base σ => Nat → ShallowDom σ
  | .arr (.arr _ _) _ => Empty

theorem noShallowEnv (η : ∀ x : Var, ShallowDom x.ty) : False :=
  (η ⟨.named 0, .arr (.arr .base .base) .base⟩).elim

def shallowApp {ρ σ : Ty} (f : ShallowDom (.arr ρ σ)) (a : ShallowDom ρ) : ShallowDom σ :=
  match ρ with
  | .base => f a
  | .arr _ _ => f.elim

def shallowModel : LambdaModel where
  Dom := ShallowDom
  appM := shallowApp
  eqM := fun _ a b => a = b
  eqM_refl := fun _ _ => rfl
  eqM_symm := by intros; subst_vars; rfl
  eqM_trans := by intros; subst_vars; rfl
  appM_congr := by intros; subst_vars; rfl
  extensional := by
    intro ρ σ f f' h
    cases ρ with
    | base => exact funext h
    | arr _ _ => exact f.elim
  eval := fun _ η _ => (noShallowEnv η).elim
  eval_var := by intros; rename_i η; exact (noShallowEnv η).elim
  eval_app := by intros; rename_i η _ _; exact (noShallowEnv η).elim
  eval_lam := by intros; rename_i η _ _; exact (noShallowEnv η).elim
  eval_congr_env := by intros; rename_i η _ _ _; exact (noShallowEnv η).elim
  eval_alpha := by intros; rename_i η _ _; exact (noShallowEnv η).elim

def shallowPR : PRModel where
  toLambdaModel := shallowModel
  nu := id
  nu_inj := fun _ _ h => h
  reprUnary := fun f _ => ⟨f, fun _ => rfl⟩
  reprBinary := fun f _ => ⟨f, fun _ _ => rfl⟩

theorem shallowPR_has_no_environment : ¬ Nonempty shallowPR.Env := by
  rintro ⟨η⟩
  exact noShallowEnv η

theorem shallowPR_models_every_equation (ρ : Ty) (r s : Term) :
    shallowPR.ModelsEq ρ r s := by
  intro η
  exact (noShallowEnv η).elim

#print axioms shallowPR_has_no_environment
#print axioms shallowPR_models_every_equation
end BergerSchwichtenberg1991.Audit
