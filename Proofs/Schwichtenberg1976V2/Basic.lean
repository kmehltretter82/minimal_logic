import Definitions.Def_Schwichtenberg1976V2_Lambda

/-!
# Basic facts about the Schwichtenberg 1976 (V2) λ-calculus

Free variables, β-normality, and inversion and uniqueness of typing.
-/

namespace Schwichtenberg1976V2.Proofs

open Schwichtenberg1976V2

/-! ## Constructive list facts

Core's `List.eq_nil_iff_forall_not_mem` is proved classically, so we use our own version. -/

theorem eq_nil_of_forall_not_mem {α : Type} {l : List α} (h : ∀ x, x ∉ l) : l = [] := by
  cases l with
  | nil => rfl
  | cons a l => exact absurd (List.mem_cons_self ..) (h a)

/-- Every term is an abstraction or is not, decided by its head constructor. -/
theorem lam_or_not (s : Term) : (∃ x c, s = .lam x c) ∨ (∀ x c, s ≠ .lam x c) := by
  cases s with
  | lam x c => exact Or.inl ⟨x, c, rfl⟩
  | var v => exact Or.inr fun _ _ h => Term.noConfusion h
  | app p q => exact Or.inr fun _ _ h => Term.noConfusion h

/-! ## Free variables -/

theorem mem_eraseDupsBy_loop (v : Var) (as : List Var) :
    ∀ acc : List Var, v ∈ List.eraseDupsBy.loop (· == ·) as acc ↔ v ∈ as ∨ v ∈ acc := by
  induction as with
  | nil =>
      intro acc
      simp [List.eraseDupsBy.loop]
  | cons a as ih =>
      intro acc
      rw [List.eraseDupsBy.loop]
      cases h : acc.any (fun x => a == x)
      · rw [ih (a :: acc), List.mem_cons, List.mem_cons]
        exact ⟨
          fun
            | Or.inl h1 => Or.inl (Or.inr h1)
            | Or.inr (Or.inl h2) => Or.inl (Or.inl h2)
            | Or.inr (Or.inr h3) => Or.inr h3,
          fun
            | Or.inl (Or.inl h1) => Or.inr (Or.inl h1)
            | Or.inl (Or.inr h2) => Or.inl h2
            | Or.inr h3 => Or.inr (Or.inr h3)⟩
      · rw [ih acc, List.mem_cons]
        simp only [List.any_eq_true, beq_iff_eq] at h
        rcases h with ⟨x, hx, rfl⟩
        exact ⟨
          fun
            | Or.inl h1 => Or.inl (Or.inr h1)
            | Or.inr h2 => Or.inr h2,
          fun
            | Or.inl (Or.inl rfl) => Or.inr hx
            | Or.inl (Or.inr h1) => Or.inl h1
            | Or.inr h2 => Or.inr h2⟩

/-- Membership in `freeVars t` is membership in `freeVarOccurrences t`. -/
theorem mem_freeVars_iff (t : Term) (v : Var) :
    v ∈ freeVars t ↔ v ∈ freeVarOccurrences t := by
  unfold freeVars List.eraseDups List.eraseDupsBy
  rw [mem_eraseDupsBy_loop]
  simp

@[simp] theorem mem_fvo_var (x v : Var) :
    v ∈ freeVarOccurrences (.var x) ↔ v = x := by
  simp [freeVarOccurrences]

@[simp] theorem mem_fvo_app (t s : Term) (v : Var) :
    v ∈ freeVarOccurrences (.app t s) ↔
      v ∈ freeVarOccurrences t ∨ v ∈ freeVarOccurrences s := by
  simp [freeVarOccurrences]

@[simp] theorem mem_fvo_lam (x : Var) (t : Term) (v : Var) :
    v ∈ freeVarOccurrences (.lam x t) ↔ v ∈ freeVarOccurrences t ∧ v ≠ x := by
  simp [freeVarOccurrences]

/-- Every free variable identifier is bounded by the maximum identifier of the term. -/
theorem freeVar_id_le_maxVarId (t : Term) (v : Var)
    (h : v ∈ freeVarOccurrences t) : v.id ≤ maxVarId t := by
  induction t with
  | var x =>
      simp [freeVarOccurrences, maxVarId] at h ⊢
      subst h
      exact Nat.le_refl _
  | app r s ihr ihs =>
      simp [freeVarOccurrences, maxVarId, Nat.max_def] at h ⊢
      rcases h with hr | hs
      · have := ihr hr; split <;> omega
      · have := ihs hs; split <;> omega
  | lam x r ih =>
      simp [freeVarOccurrences, maxVarId, Nat.max_def] at h ⊢
      have := ih h.1; split <;> omega

/-! ## β-normal forms -/

theorem isBetaNormal_app {a b : Term} (h : IsBetaNormal (.app a b)) :
    (∀ x c, a ≠ .lam x c) ∧ IsBetaNormal a ∧ IsBetaNormal b := by
  unfold IsBetaNormal at *
  cases a with
  | lam x c => simp [hasBetaRedex] at h
  | var v =>
      simp only [hasBetaRedex, Bool.false_or] at h
      exact ⟨fun _ _ hc => Term.noConfusion hc, rfl, h⟩
  | app p q =>
      simp only [hasBetaRedex, Bool.or_eq_false_iff] at h
      exact ⟨fun _ _ hc => Term.noConfusion hc, by simpa [hasBetaRedex] using h.1, h.2⟩

theorem isBetaNormal_lam {x : Var} {b : Term} (h : IsBetaNormal (.lam x b)) :
    IsBetaNormal b := by
  unfold IsBetaNormal at *
  simpa [hasBetaRedex] using h

/-! ## Typing -/

theorem hasType_var_inv {x : Var} {τ : Ty} (h : HasType (.var x) τ) : τ = x.ty := by
  cases h; rfl

theorem hasType_app_inv {t s : Term} {τ : Ty} (h : HasType (.app t s) τ) :
    ∃ σ, HasType t (.arr σ τ) ∧ HasType s σ := by
  cases h with
  | app ht hs => exact ⟨_, ht, hs⟩

theorem hasType_lam_inv {x : Var} {b : Term} {τ : Ty} (h : HasType (.lam x b) τ) :
    ∃ ρ, τ = .arr x.ty ρ ∧ HasType b ρ := by
  cases h with
  | lam _ hb => exact ⟨_, rfl, hb⟩

/-- Types are unique: the calculus is Church-style. -/
theorem hasType_unique {t : Term} {τ τ' : Ty} (h : HasType t τ) (h' : HasType t τ') :
    τ = τ' := by
  induction h generalizing τ' with
  | var x => exact (hasType_var_inv h').symm
  | app ht hs iht ihs =>
      obtain ⟨σ', ht', hs'⟩ := hasType_app_inv h'
      have := iht ht'
      injection this
  | lam x hb ih =>
      obtain ⟨ρ', rfl, hb'⟩ := hasType_lam_inv h'
      rw [ih hb']

/-! ## The type-`0 → 0` grammar -/

theorem chain_ty {Fs : List Var} {α z : Var} {t : Term}
    (h : IsBasicType00Chain Fs α z t) : z.ty = .zero := by
  induction t generalizing z with
  | var v =>
      cases h with
      | base _ hz => exact hz
  | app a b _ ihb =>
      cases h with
      | step _ hb => exact ihb hb
  | lam x b _ => cases h

theorem basic_of_type00_not_lam {Fs : List Var} {α : Var} {t : Term}
    (h : IsType00Subterm Fs α t) (hnl : ∀ x c, t ≠ .lam x c) : IsBasicType00 Fs α t := by
  cases h with
  | basic hb => exact hb
  | chainLam y z _ _ _ => exact absurd rfl (hnl y _)

end Schwichtenberg1976V2.Proofs
