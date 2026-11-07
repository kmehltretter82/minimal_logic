import Definitions.Def_AehligSchwichtenberg2002_Syntax

/-!
# `substTerm` can make the two binders of a tensor elimination equal

`substTerm` renames a binder `v` that is free in the substituted term `s`. The new name is
chosen above the identifiers of the binder's body, of `s` and of `x`, but not above the
enclosing binders. In a tensor elimination `t (λa. λb. r)` with `a` unused in `r`, the
renamed `b` can therefore become `a`. The result `t (λa. λa. r')` cannot be typed, because
the rule `(⊗⁻)` requires distinct binders.

Concretely, with `a = ⟨10, B⟩`, `b = ⟨0, B⟩`, `x = ⟨9, B⟩`, `p = ⟨20, B ⊗ B⟩`:

* `t := p (λa. λb. b)` is typed in `{p, x}`, and `s := b` is typed in `{b}` with type `x.ty`;
* `substTerm t x s = p (λa. λa. a)`, which has no type in any context.

This refutes the published `lemma_3_4` (substitution) and `lemma_3_5` (subject reduction):
the β-redex `(λx. t) b` is typed in `{p, b}` and reduces to the untypable term.
-/

namespace AehligSchwichtenberg2002.Audit

open AehligSchwichtenberg2002

def a : Var := ⟨10, .bool⟩
def b : Var := ⟨0, .bool⟩
def x : Var := ⟨9, .bool⟩
def p : Var := ⟨20, .tensor .bool .bool⟩

def t : Term := .app (.var p) (.lam a (.lam b (.var b)))
def s : Term := .var b
def clash : Term := .app (.var p) (.lam a (.lam a (.var a)))

/-- The substitution renames `b` to `⟨10, B⟩ = a`. -/
theorem subst_eq : substTerm t x s = clash := by
  simp (config := { decide := true }) [t, s, clash, a, b, x, p, substTerm, renameFreeVar,
    freeVarOccurrences, maxVarId]

/-- The result of the substitution has no type in any context. -/
theorem clash_untypable (Γ : Context) (τ : Ty) : ¬ HasType Γ clash τ := by
  intro h
  unfold clash at h
  cases h with
  | app _ hp _ => cases hp
  | tensorElim _ _ hne _ _ _ _ => exact hne rfl

theorem t_typed : HasType [p, x] t .bool := by
  refine .tensorElim (Γ₁ := [p, x]) (Γ₂ := []) (Γ₂' := [a, b]) a b (by decide)
    ⟨fun v h => by simp at h, fun v => by simp⟩
    ⟨fun v _ h => by simp at h, fun v => by simp⟩
    (.var p (Γ := [x]) ⟨fun v h1 h2 => by simp at h1 h2; subst h1; simp [x, p] at h2,
      fun v => by simp [or_comm]⟩)
    (.var b (Γ := [a]) ⟨fun v h1 h2 => by simp at h1 h2; subst h1; simp [a, b] at h2,
      fun v => by simp⟩)

theorem s_typed : HasType [b] s x.ty :=
  .var b (Γ := []) ⟨fun v h => by simp at h, fun v => by simp⟩

/-- The published Lemma 3.4 (substitution) is false. -/
theorem lemma_3_4_false :
    ¬ ∀ {Γ₁ Γ₁' Γ₂ Γ : Context} {x : Var} {t s : Term} {τ : Ty},
      IsCtxUnion Γ₁ [x] Γ₁' → HasType Γ₁' t τ → HasType Γ₂ s x.ty →
      IsDisjointCtxUnion Γ₁ Γ₂ Γ → HasType Γ (substTerm t x s) τ := by
  intro h
  have := h (Γ₁ := [p]) (Γ₁' := [p, x]) (Γ₂ := [b]) (Γ := [p, b])
    (fun v => by simp) t_typed s_typed
    ⟨fun v h1 h2 => by simp at h1 h2; subst h1; simp [p, b] at h2, fun v => by simp⟩
  rw [subst_eq] at this
  exact clash_untypable _ _ this

/-- The published Lemma 3.5 (subject reduction) is false. -/
theorem lemma_3_5_false :
    ¬ ∀ {Γ : Context} {t t' : Term} {τ : Ty},
      HasType Γ t τ → RedStep t t' → HasType Γ t' τ := by
  intro h
  have hredex : HasType [p, b] (.app (.lam x t) s) .bool :=
    .app (Γ₁ := [p]) (Γ₂ := [b])
      ⟨fun v h1 h2 => by simp at h1 h2; subst h1; simp [p, b] at h2, fun v => by simp⟩
      (.lam x (Γ' := [p, x]) (fun v => by simp) t_typed) s_typed
  have := h hredex (.conv (.beta x t s))
  rw [subst_eq] at this
  exact clash_untypable _ _ this

end AehligSchwichtenberg2002.Audit
