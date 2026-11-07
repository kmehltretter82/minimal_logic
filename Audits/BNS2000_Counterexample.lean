import Definitions.Def_BNS2000_Terms

namespace BNS2000.Audit

/-- Remove ordinary application arguments, but retain κ eliminations. -/
def appHead : Term → Term
  | .app r _ => appHead r
  | t => t

theorem appHead_appMany (t : Term) (rs : List Term) :
    appHead (Term.appMany t rs) = appHead t := by
  induction rs generalizing t <;> simp_all [Term.appMany, appHead]

/-- Remove κ eliminations. -/
def kappaHead : Term → Term
  | .kappa r => kappaHead r
  | t => t

theorem kappaHead_repeat (t : Term) (k : Nat) :
    kappaHead (kappaRepeat k t) = kappaHead t := by
  induction k <;> simp_all [kappaRepeat, kappaHead]

theorem appHead_kappa_var (x : Var) (k : Nat) :
    appHead (kappaRepeat k (.var x)) = kappaRepeat k (.var x) := by
  cases k <;> rfl

def bad : Term := .kappa (.kappa (.bang (.bang (.const .zero))))

/-- Every evaluation rule requires one of these shapes after stripping term arguments.
This is a necessary condition only, extracted directly from the constructors. -/
def HasSupportedHead (t : Term) : Prop :=
  (∃ x : Var, kappaHead (appHead t) = .var x) ∨
  (∃ s : Term, appHead t = .kappa (.bang s)) ∨
  (∃ c : Const, appHead t = .const c) ∨
  (∃ s : Term, appHead t = .bang s) ∨
  (∃ x : Var, ∃ s : Term, appHead t = .lam x s)

theorem eval_supported {t out : Term} {env : List (Var × Term)} {st gr ml : Nat}
    (h : NFEval t env out st gr ml) : HasSupportedHead t := by
  cases h <;> simp [HasSupportedHead, appHead_appMany, appHead_kappa_var, kappaHead_repeat, appHead, kappaHead]

theorem bad_no_eval (out : Term) (env : List (Var × Term)) (st gr ml : Nat) :
    ¬ NFEval bad env out st gr ml := by
  intro h
  have := eval_supported h
  simp [HasSupportedHead, bad, appHead, kappaHead] at this

/-- Explicitly enumerate all subterms; this avoids testing a finite selection of paths. -/
def subterms : Term → List Term
  | .var x => [.var x]
  | .const c => [.const c]
  | .lam x r => .lam x r :: subterms r
  | .app r s => .app r s :: (subterms r ++ subterms s)
  | .bang r => .bang r :: subterms r
  | .kappa r => .kappa r :: subterms r

theorem subterm_mem {u t : Term} (h : IsSubterm u t) : u ∈ subterms t := by
  rcases h with ⟨p, hp⟩
  induction t generalizing p with
  | var x => cases p <;> simp_all [subtermAt, subterms]
  | const c => cases p <;> simp_all [subtermAt, subterms]
  | lam x r ih | bang r ih | kappa r ih =>
    cases p with
    | nil => simp_all [subtermAt, subterms]
    | cons i p =>
      cases i <;> simp_all [subtermAt, subterms]
      exact Or.inr (ih p hp)
  | app r s ihr ihs =>
    cases p with
    | nil => simp_all [subtermAt, subterms]
    | cons i p =>
      cases i with
      | zero =>
        simp_all [subtermAt, subterms]
        exact Or.inr (Or.inl (ihr p hp))
      | succ i =>
        cases i <;> simp_all [subtermAt, subterms]
        exact Or.inr (Or.inr (ihs p hp))

theorem bad_typed : HasType bad .iota :=
  HasType.kappa (HasType.kappa (HasType.bang (HasType.bang (HasType.const .zero rfl))))

theorem bad_R : SatisfiesR bad := by
  intro u hu _ v hv
  have hmem := subterm_mem hu
  simp [subterms, bad] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;>
    simp [freeVars, freeVarOccurrences] at hv

theorem bad_no_lam (x : Var) (s : Term) : ¬ IsSubterm (.lam x s) bad := by
  intro h
  have hmem := subterm_mem h
  simp [subterms, bad] at hmem

theorem bad_RS : IsRSTerm bad := by
  refine ⟨⟨⟨.iota, bad_typed⟩, bad_R, ?_⟩, ?_, ?_⟩
  · intro x s h
    exact (bad_no_lam x s h).elim
  · simp [AllVarsSafeOrGround, allVars, bad]
  · constructor
    · simp [bad, freeVars, freeVarOccurrences]
    · intro x s h
      exact (bad_no_lam x s h).elim

/-- Exact submitted statement, repeated without importing its open axiom. -/
def Submitted4_3and4_4 : Prop :=

    (∀ (t : Term) (τ : Ty) (env : List (Var × Term)),
      IsRSTerm t →
      isRFree t = true →
      HasType t τ →
      τ.isGround = true →
      IsNumeralEnv env →
      (∀ v ∈ freeVars t, v ∈ env.map Prod.fst) →
      ∃ (out : Term) (steps regs maxLen : Nat),
        NFEval t env out steps regs maxLen ∧
        IsNormalFormOf (substEnv t env) out ∧
        isNumeral out = true ∧
        steps ≤ 2 * termLength t ∧
        regs ≤ termLength t + env.length ∧
        maxLen ≤ termLength t + maxEnvTermLength env) ∧
    (∀ (t : Term) (τ : Ty),
      IsRSTerm t →
      isRFree t = true →
      IsClosed t →
      HasType t τ →
      τ.isGround = true →
      ∃ (out : Term) (steps regs maxLen : Nat),
        NFEval t [] out steps regs maxLen ∧
        IsNormalFormOf t out ∧
        isNumeral out = true ∧
        steps ≤ 2 * termLength t ∧
        regs ≤ termLength t ∧
        maxLen ≤ termLength t) 

theorem refute_submitted_4_3_and_4_4 : ¬ Submitted4_3and4_4 := by
  intro h
  obtain ⟨out, st, gr, ml, heval, _⟩ := h.2 bad .iota bad_RS rfl rfl bad_typed rfl
  exact bad_no_eval out [] st gr ml heval

#print axioms refute_submitted_4_3_and_4_4

/-- The witness really does normalize in two ordinary contextual steps. -/
theorem bad_reduces_zero : ReducesTo bad (.const .zero) :=
  .step (.kappa (.conv (.bangKappa (.bang (.const .zero)))))
    (.step (.conv (.bangKappa (.const .zero))) (.refl _))

/-- A second issue: raw named normal forms are not unique (alpha conversion is absent). -/
def vx : Var := ⟨1, .iota⟩
def vy : Var := ⟨0, .iota⟩
def vz : Var := ⟨10, .iota⟩
def inner : Term := .app (.lam vz (.var vy)) (.const .zero)
def alphaSource : Term := .app (.lam vx (.lam vy (.var vx))) inner
def nfOuterFirst : Term := .lam ⟨11, .iota⟩ (.var vy)
def nfInnerFirst : Term := .lam ⟨2, .iota⟩ (.var vy)

theorem inner_step : Step inner (.var vy) := by
  simpa [inner, substTerm, vy, vz] using Step.conv (ConvStep.beta vz (.var vy) (.const .zero))

theorem alpha_outer_first : ReducesTo alphaSource nfOuterFirst := by
  apply ReducesTo.step (Step.conv (ConvStep.beta vx (.lam vy (.var vx)) inner))
  simp [substTerm, renameFreeVar, freeVarOccurrences, maxVarId, inner, vx, vy, vz]
  exact .step (.lam ⟨11, .iota⟩ inner_step) (.refl _)

theorem alpha_inner_first : ReducesTo alphaSource nfInnerFirst := by
  apply ReducesTo.step (Step.appRight inner_step)
  apply ReducesTo.step (Step.conv (ConvStep.beta vx (.lam vy (.var vx)) (.var vy)))
  simpa [substTerm, renameFreeVar, freeVarOccurrences, maxVarId, nfInnerFirst, vx, vy] using
    ReducesTo.refl nfInnerFirst

theorem normal_lam_var (a b : Var) : IsNormal (.lam a (.var b)) := by
  rintro ⟨u, h⟩
  cases h with
  | conv hc => cases hc
  | lam _ hs => cases hs with
    | conv hc => cases hc

theorem alphaSource_typed : HasType alphaSource (.arr .iota .iota) :=
  .app (.lam vx (.lam vy (.var vx)))
    (.app (.lam vz (.var vy)) (.const .zero rfl))

theorem two_distinct_normal_forms :
    HasType alphaSource (.arr .iota .iota) ∧
    IsNormalFormOf alphaSource nfOuterFirst ∧
    IsNormalFormOf alphaSource nfInnerFirst ∧
    nfOuterFirst ≠ nfInnerFirst := by
  exact ⟨alphaSource_typed, ⟨alpha_outer_first, normal_lam_var _ _⟩,
    ⟨alpha_inner_first, normal_lam_var _ _⟩, by decide⟩

theorem normal_reduces_eq {t u : Term} (hn : IsNormal t) (hr : ReducesTo t u) : t = u := by
  cases hr with
  | refl => rfl
  | step hs _ => exact (hn ⟨_, hs⟩).elim

theorem different_normal_forms_not_equivalent : ¬ TermEquiv nfOuterFirst nfInnerFirst := by
  rintro ⟨u, ho, hi⟩
  have heq := (normal_reduces_eq (normal_lam_var _ _) ho.1).trans
    (normal_reduces_eq (normal_lam_var _ _) hi.1).symm
  exact two_distinct_normal_forms.2.2.2 heq

theorem equivalence_not_transitive :
    ∃ a b c : Term, TermEquiv a b ∧ TermEquiv b c ∧ ¬ TermEquiv a c := by
  refine ⟨nfOuterFirst, alphaSource, nfInnerFirst, ?_, ?_, different_normal_forms_not_equivalent⟩
  · exact ⟨nfOuterFirst, ⟨.refl _, normal_lam_var _ _⟩,
      ⟨alpha_outer_first, normal_lam_var _ _⟩⟩
  · exact ⟨nfInnerFirst, ⟨alpha_inner_first, normal_lam_var _ _⟩,
      ⟨.refl _, normal_lam_var _ _⟩⟩

#print axioms two_distinct_normal_forms
#print axioms equivalence_not_transitive

end BNS2000.Audit
