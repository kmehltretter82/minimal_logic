import Proofs.AehligSchwichtenberg2002.Basic

/-!
# Lemma 4.3: every term of type `⋄` has a free variable (p. 10)

Read each type as "inhabited" or "uninhabited": `⋄` is uninhabited, `B` and `L(τ)` are
inhabited (by `tt` and `nil`), `τ ⊸ ρ` is inhabited unless `τ` is inhabited and `ρ` is not,
and products are inhabited if both components are. Every typing rule is sound for this
reading: if all free variables of a typed term have inhabited types, then so does the term.
Hence a term of type `⋄` has a free variable of uninhabited type.

The paper proves the lemma by induction on length with a reduction argument. This semantic
proof needs no reduction.
-/

namespace AehligSchwichtenberg2002.Proofs

open AehligSchwichtenberg2002

/-- Inhabitation of a type, read as a Boolean. -/
def inhab : Ty → Bool
  | .diamond => false
  | .bool => true
  | .lolli a b => !inhab a || inhab b
  | .tensor a b => inhab a && inhab b
  | .prod a b => inhab a && inhab b
  | .list _ => true

theorem inhab_constructor (c : Constructor) : inhab c.ty = true := by
  cases c with
  | tt => rfl
  | ff => rfl
  | nil τ => rfl
  | cons τ => simp [Constructor.ty, inhab]
  | tensorPair τ ρ =>
      simp only [Constructor.ty, inhab]
      cases inhab τ <;> cases inhab ρ <;> rfl

/-- Soundness of typing for the inhabitation reading. -/
theorem inhab_sound {Γ : Context} {t : Term} {τ : Ty} (h : HasType Γ t τ) :
    (∀ v ∈ freeVarOccurrences t, inhab v.ty = true) → inhab τ = true := by
  induction h with
  | var x _ => intro hv; exact hv x (by simp)
  | const _ c => intro _; exact inhab_constructor c
  | lam x _ _ ih =>
      intro hv
      simp only [inhab]
      cases hx : inhab x.ty with
      | false => rfl
      | true =>
          simp only [Bool.not_true, Bool.false_or]
          apply ih
          intro v hvt
          by_cases hvx : v = x
          · subst hvx; exact hx
          · exact hv v ((mem_fvo_lam _ _ _).2 ⟨hvt, hvx⟩)
  | app _ _ _ ih1 ih2 =>
      intro hv
      have h1 := ih1 (fun v h => hv v ((mem_fvo_app _ _ _).2 (Or.inl h)))
      have h2 := ih2 (fun v h => hv v ((mem_fvo_app _ _ _).2 (Or.inr h)))
      simp only [inhab, h2, Bool.not_true, Bool.false_or] at h1
      exact h1
  | pair _ _ ih1 ih2 =>
      intro hv
      simp only [inhab]
      rw [ih1 (fun v h => hv v ((mem_fvo_pair _ _ _).2 (Or.inl h))),
        ih2 (fun v h => hv v ((mem_fvo_pair _ _ _).2 (Or.inr h)))]
      rfl
  | projLeft _ ih =>
      intro hv
      have := ih (fun v h => hv v ((mem_fvo_app _ _ _).2 (Or.inl h)))
      simp only [inhab, Bool.and_eq_true] at this
      exact this.1
  | projRight _ ih =>
      intro hv
      have := ih (fun v h => hv v ((mem_fvo_app _ _ _).2 (Or.inl h)))
      simp only [inhab, Bool.and_eq_true] at this
      exact this.2
  | boolElim _ _ _ _ _ ih2 _ =>
      intro hv
      exact ih2 (fun v h => hv v ((mem_fvo_app _ _ _).2 (Or.inr ((mem_fvo_pair _ _ _).2
        (Or.inl h)))))
  | tensorElim x y _ _ _ _ _ ih1 ih2 =>
      intro hv
      have h1 := ih1 (fun v h => hv v ((mem_fvo_app _ _ _).2 (Or.inl h)))
      simp only [inhab, Bool.and_eq_true] at h1
      apply ih2
      intro v hvs
      by_cases hvx : v = x
      · subst hvx; exact h1.1
      · by_cases hvy : v = y
        · subst hvy; exact h1.2
        · exact hv v ((mem_fvo_app _ _ _).2 (Or.inr (by simp [hvs, hvx, hvy])))
  | listElim _ _ _ _ =>
      intro _
      simp only [inhab]
      cases inhab _ <;> rfl

/-- **Lemma 4.3.** Every term of type `⋄` has a free variable; in particular its context is
not empty. -/
theorem lemma_4_3 {Γ : Context} {t : Term}
    (ht : HasType Γ t .diamond) :
    Γ ≠ [] ∧ freeVars t ≠ [] := by
  have hfv : freeVarOccurrences t ≠ [] := by
    intro h
    have := inhab_sound ht (by rw [h]; intro v hv; simp at hv)
    simp [inhab] at this
  obtain ⟨v, hv⟩ : ∃ v, v ∈ freeVarOccurrences t := by
    cases h : freeVarOccurrences t with
    | nil => exact absurd h hfv
    | cons v _ => exact ⟨v, by simp⟩
  refine ⟨fun hΓ => ?_, fun hfv' => ?_⟩
  · have := fvo_subset_ctx ht v hv
    rw [hΓ] at this
    simp at this
  · have := (mem_freeVars_iff t v).2 hv
    rw [hfv'] at this
    simp at this

/-- A sharper form used later: some free variable of a `⋄`-term has an uninhabited type. -/
theorem diamond_has_free_var {Γ : Context} {t : Term} (ht : HasType Γ t .diamond) :
    ∃ v ∈ freeVarOccurrences t, True := by
  cases h : freeVarOccurrences t with
  | nil =>
      have := inhab_sound ht (by rw [h]; intro v hv; simp at hv)
      simp [inhab] at this
  | cons v _ => exact ⟨v, by simp, trivial⟩

end AehligSchwichtenberg2002.Proofs
