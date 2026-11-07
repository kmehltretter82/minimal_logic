import Definitions.Def_AehligSchwichtenberg2002_Bounds

/-!
# Basic facts for Aehlig–Schwichtenberg (2002)

Free variables, contexts, and the fact that a typed term's free variables lie in its
context. Everything here is constructive.
-/

namespace AehligSchwichtenberg2002.Proofs

open AehligSchwichtenberg2002

/-! ## Lists -/

theorem eq_nil_of_forall_not_mem {α : Type} {l : List α} (h : ∀ x, x ∉ l) : l = [] := by
  cases l with
  | nil => rfl
  | cons a l => exact absurd (List.mem_cons_self ..) (h a)

theorem mem_eraseDupsBy_loop (v : Var) (as : List Var) :
    ∀ acc : List Var, v ∈ List.eraseDupsBy.loop (· == ·) as acc ↔ v ∈ as ∨ v ∈ acc := by
  induction as with
  | nil => intro acc; simp [List.eraseDupsBy.loop]
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

/-! ## Free variables of each term former -/

@[simp] theorem mem_fvo_var (x v : Var) : v ∈ freeVarOccurrences (.var x) ↔ v = x := by
  simp [freeVarOccurrences]

@[simp] theorem fvo_const (c : Constructor) : freeVarOccurrences (.const c) = [] := rfl

@[simp] theorem mem_fvo_lam (x : Var) (t : Term) (v : Var) :
    v ∈ freeVarOccurrences (.lam x t) ↔ v ∈ freeVarOccurrences t ∧ v ≠ x := by
  simp [freeVarOccurrences]

@[simp] theorem mem_fvo_pair (t s : Term) (v : Var) :
    v ∈ freeVarOccurrences (.pair t s) ↔
      v ∈ freeVarOccurrences t ∨ v ∈ freeVarOccurrences s := by
  simp [freeVarOccurrences]

@[simp] theorem mem_fvo_app (t s : Term) (v : Var) :
    v ∈ freeVarOccurrences (.app t s) ↔
      v ∈ freeVarOccurrences t ∨ v ∈ freeVarOccurrences s := by
  simp [freeVarOccurrences]

@[simp] theorem mem_fvo_brace (t : Term) (v : Var) :
    v ∈ freeVarOccurrences (.brace t) ↔ v ∈ freeVarOccurrences t := by
  simp [freeVarOccurrences]

/-! ## Typed terms have their free variables in the context -/

theorem fvo_subset_ctx {Γ : Context} {t : Term} {τ : Ty} (h : HasType Γ t τ) :
    ∀ v ∈ freeVarOccurrences t, v ∈ Γ := by
  induction h with
  | var x hu =>
      intro v hv
      rw [mem_fvo_var] at hv
      subst hv
      exact (hu.2 v).2 (Or.inr (List.mem_singleton_self v))
  | const => intro v hv; simp at hv
  | lam x hu _ ih =>
      intro v hv
      rw [mem_fvo_lam] at hv
      rcases (hu v).1 (ih v hv.1) with h | h
      · exact h
      · exact absurd (List.mem_singleton.1 h) hv.2
  | app hu _ _ ih1 ih2 =>
      intro v hv
      rcases (mem_fvo_app _ _ _).1 hv with h | h
      · exact (hu.2 v).2 (Or.inl (ih1 v h))
      · exact (hu.2 v).2 (Or.inr (ih2 v h))
  | pair _ _ ih1 ih2 =>
      intro v hv
      rcases (mem_fvo_pair _ _ _).1 hv with h | h
      · exact ih1 v h
      · exact ih2 v h
  | projLeft _ ih =>
      intro v hv
      rcases (mem_fvo_app _ _ _).1 hv with h | h
      · exact ih v h
      · simp at h
  | projRight _ ih =>
      intro v hv
      rcases (mem_fvo_app _ _ _).1 hv with h | h
      · exact ih v h
      · simp at h
  | boolElim hu _ _ _ ih1 ih2 ih3 =>
      intro v hv
      rcases (mem_fvo_app _ _ _).1 hv with h | h
      · exact (hu.2 v).2 (Or.inl (ih1 v h))
      · rcases (mem_fvo_pair _ _ _).1 h with h | h
        · exact (hu.2 v).2 (Or.inr (ih2 v h))
        · exact (hu.2 v).2 (Or.inr (ih3 v h))
  | tensorElim x y _ hu₂ hu _ _ ih1 ih2 =>
      intro v hv
      rcases (mem_fvo_app _ _ _).1 hv with h | h
      · exact (hu.2 v).2 (Or.inl (ih1 v h))
      · simp only [mem_fvo_lam] at h
        obtain ⟨⟨hs, hvy⟩, hvx⟩ := h
        rcases (hu₂.2 v).1 (ih2 v hs) with h' | h'
        · exact (hu.2 v).2 (Or.inr h')
        · simp at h'
          rcases h' with h' | h'
          · exact absurd h' hvx
          · exact absurd h' hvy
  | listElim _ _ ih1 ih2 =>
      intro v hv
      rcases (mem_fvo_app _ _ _).1 hv with h | h
      · exact ih1 v h
      · rw [mem_fvo_brace] at h
        exact absurd (ih2 v h) (List.not_mem_nil)

end AehligSchwichtenberg2002.Proofs
