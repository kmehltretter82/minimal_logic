import Proofs.Schwichtenberg1976V2.Basic

/-!
# Extended polynomials are the piecewise polynomials (p. 114)

`f` is an extended polynomial iff, for every zero/non-zero pattern `σ` of the arguments, `f`
agrees on that pattern with a polynomial.

* (⇒) On a fixed pattern, a polynomial is either always `0` or never `0`, so a conditional
  `d(f, g, h)` always selects the same branch. Composition is closed because polynomials are
  closed under substitution.
* (⇐) `f(v) = Σ_σ χ_σ(v) · P_σ(v)`, where the indicator `χ_σ` is a product of `sg(vᵢ)` and
  `s̄g(vᵢ)`, both of which are conditionals.

Everything is constructive.
-/

namespace Schwichtenberg1976V2.Proofs

open Schwichtenberg1976V2

/-- `v` has the zero/non-zero pattern `σ`. -/
def Matches {k : Nat} (σ : Fin k → Bool) (v : Fin k → Nat) : Prop :=
  ∀ i : Fin k, (v i != 0) = σ i

/-- The pattern of `v`. -/
def patternOf {k : Nat} (v : Fin k → Nat) : Fin k → Bool := fun i => v i != 0

theorem matches_patternOf {k : Nat} (v : Fin k → Nat) : Matches (patternOf v) v :=
  fun _ => rfl

/-! ## Polynomials -/

/-- On a fixed pattern a polynomial is identically `0` or nowhere `0`. -/
theorem poly_dichotomy {k : Nat} {P : (Fin k → Nat) → Nat} (hP : IsPolynomial P)
    (σ : Fin k → Bool) :
    (∀ v, Matches σ v → P v = 0) ∨ (∀ v, Matches σ v → P v ≠ 0) := by
  induction hP with
  | const c =>
      cases c with
      | zero => exact Or.inl fun _ _ => rfl
      | succ c => exact Or.inr fun _ _ => Nat.succ_ne_zero c
  | proj i =>
      cases hσ : σ i with
      | false =>
          refine Or.inl fun v hv => ?_
          have := hv i
          rw [hσ] at this
          simpa using this
      | true =>
          refine Or.inr fun v hv => ?_
          have := hv i
          rw [hσ] at this
          simpa using this
  | add _ _ ihP ihQ =>
      rcases ihP with hP | hP
      · rcases ihQ with hQ | hQ
        · exact Or.inl fun v hv => by dsimp only; rw [hP v hv, hQ v hv]
        · exact Or.inr fun v hv => by dsimp only; have := hQ v hv; omega
      · exact Or.inr fun v hv => by dsimp only; have := hP v hv; omega
  | mul _ _ ihP ihQ =>
      rcases ihP with hP | hP
      · exact Or.inl fun v hv => by dsimp only; rw [hP v hv, Nat.zero_mul]
      · rcases ihQ with hQ | hQ
        · exact Or.inl fun v hv => by dsimp only; rw [hQ v hv, Nat.mul_zero]
        · exact Or.inr fun v hv => Nat.mul_ne_zero (hP v hv) (hQ v hv)

/-- Polynomials are closed under substitution of polynomials. -/
theorem poly_comp {k m : Nat} {Q : (Fin m → Nat) → Nat} (hQ : IsPolynomial Q)
    {Ps : Fin m → (Fin k → Nat) → Nat} (hPs : ∀ j, IsPolynomial (Ps j)) :
    IsPolynomial (fun v => Q (fun j => Ps j v)) := by
  induction hQ with
  | const c => exact .const c
  | proj j => exact hPs j
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mul _ _ ih1 ih2 => exact .mul ih1 ih2

theorem poly_extended {k : Nat} {P : (Fin k → Nat) → Nat} (hP : IsPolynomial P) :
    IsExtendedPolyInd P := by
  induction hP with
  | const c => exact .const c
  | proj i => exact .proj i
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mul _ _ ih1 ih2 => exact .mul ih1 ih2

/-! ## (⇒) Extended polynomials are piecewise polynomials -/

/-- Finite choice, by induction on `m`. -/
theorem fin_choice' {β : Type} {m : Nat} {R : Fin m → β → Prop}
    (h : ∀ j, ∃ b, R j b) : ∃ bs : Fin m → β, ∀ j, R j (bs j) := by
  induction m with
  | zero => exact ⟨fun j => j.elim0, fun j => j.elim0⟩
  | succ m ih =>
      obtain ⟨P0, h0⟩ := h 0
      obtain ⟨Ps', hPs'⟩ := ih (R := fun j => R j.succ) (fun j => h j.succ)
      exact ⟨Fin.cases P0 Ps', fun j => Fin.cases h0 hPs' j⟩

theorem extended_piecewise {k : Nat} {f : (Fin k → Nat) → Nat} (hf : IsExtendedPolyInd f) :
    IsPiecewisePolynomial k f := by
  induction hf with
  | const c => exact fun _ => ⟨_, .const c, fun _ _ => rfl⟩
  | proj i => exact fun _ => ⟨_, .proj i, fun _ _ => rfl⟩
  | add _ _ ihf ihg =>
      intro σ
      obtain ⟨P, hP, hfP⟩ := ihf σ
      obtain ⟨Q, hQ, hgQ⟩ := ihg σ
      exact ⟨_, .add hP hQ, fun v hv => by simp only [hfP v hv, hgQ v hv]⟩
  | mul _ _ ihf ihg =>
      intro σ
      obtain ⟨P, hP, hfP⟩ := ihf σ
      obtain ⟨Q, hQ, hgQ⟩ := ihg σ
      exact ⟨_, .mul hP hQ, fun v hv => by simp only [hfP v hv, hgQ v hv]⟩
  | cond _ _ _ ihf ihg ihh =>
      intro σ
      obtain ⟨P, hP, hfP⟩ := ihf σ
      obtain ⟨Q, hQ, hgQ⟩ := ihg σ
      obtain ⟨R, hR, hhR⟩ := ihh σ
      rcases poly_dichotomy hR σ with h0 | h0
      · refine ⟨P, hP, fun v hv => ?_⟩
        show condNat _ _ _ = _
        rw [hhR v hv, h0 v hv, hfP v hv]
        rfl
      · refine ⟨Q, hQ, fun v hv => ?_⟩
        have hne := h0 v hv
        show condNat _ _ _ = _
        rw [hhR v hv, hgQ v hv]
        cases hR : R v with
        | zero => exact absurd hR hne
        | succ n => rfl
  | @comp k m g hs _ _ ihg ihhs =>
      intro σ
      obtain ⟨Ps, hPs⟩ := fin_choice' (fun j => ihhs j σ)
      -- on the pattern `σ` each inner polynomial is always zero or never zero
      have hj : ∀ j, ∃ b : Bool, ∀ v, Matches σ v → (Ps j v != 0) = b := by
        intro j
        rcases poly_dichotomy (hPs j).1 σ with h | h
        · exact ⟨false, fun v hv => by rw [h v hv]; rfl⟩
        · refine ⟨true, fun v hv => ?_⟩
          have hne := h v hv
          cases hP : Ps j v with
          | zero => exact absurd hP hne
          | succ n => rfl
      obtain ⟨ρ, hρ⟩ := fin_choice' hj
      obtain ⟨Q, hQ, hgQ⟩ := ihg ρ
      refine ⟨fun v => Q (fun j => Ps j v), poly_comp hQ fun j => (hPs j).1, fun v hv => ?_⟩
      have hinner : (fun j => hs j v) = (fun j => Ps j v) := funext fun j => (hPs j).2 v hv
      have hmatch : Matches ρ (fun j => Ps j v) := fun j => hρ j v hv
      show g (fun j => hs j v) = Q (fun j => Ps j v)
      rw [hinner, hgQ _ hmatch]

/-! ## (⇐) Piecewise polynomials are extended polynomials

Free the argument positions one at a time. If `f` is an extended polynomial `E₀` wherever
`vⱼ = 0` and `E₁` wherever `vⱼ ≠ 0` (with the other positions constrained as before), then
`f = d(E₀, E₁, vⱼ)` there. -/

/-- `v` agrees with the pattern `σ` at the positions `≥ j`. -/
def MatchesFrom {k : Nat} (j : Nat) (σ : Fin k → Bool) (v : Fin k → Nat) : Prop :=
  ∀ i : Fin k, j ≤ i.val → (v i != 0) = σ i

theorem piecewise_cascade {k : Nat} {f : (Fin k → Nat) → Nat} (hf : IsPiecewisePolynomial k f) :
    ∀ j : Nat, ∀ σ : Fin k → Bool,
      ∃ E : (Fin k → Nat) → Nat, IsExtendedPolyInd E ∧ ∀ v, MatchesFrom j σ v → f v = E v := by
  intro j
  induction j with
  | zero =>
      intro σ
      obtain ⟨P, hP, hfP⟩ := hf σ
      exact ⟨P, poly_extended hP, fun v hv => hfP v fun i => hv i (Nat.zero_le _)⟩
  | succ j ih =>
      intro σ
      by_cases hj : j < k
      · let upd (b : Bool) : Fin k → Bool := fun i => if i.val = j then b else σ i
        obtain ⟨E₀, hE₀, hf₀⟩ := ih (upd false)
        obtain ⟨E₁, hE₁, hf₁⟩ := ih (upd true)
        refine ⟨fun v => condNat (E₀ v) (E₁ v) (v ⟨j, hj⟩), .cond hE₀ hE₁ (.proj ⟨j, hj⟩),
          fun v hv => ?_⟩
        have hrest : ∀ b, (v ⟨j, hj⟩ != 0) = b → MatchesFrom j (upd b) v := by
          intro b hb i hi
          by_cases hij : i.val = j
          · have : i = ⟨j, hj⟩ := Fin.ext hij
            subst this
            simp only [upd, if_pos rfl]
            exact hb
          · simp only [upd, if_neg hij]
            exact hv i (by omega)
        show f v = condNat (E₀ v) (E₁ v) (v ⟨j, hj⟩)
        cases h : v ⟨j, hj⟩ with
        | zero =>
            rw [hf₀ v (hrest false (by rw [h]; rfl))]
            rfl
        | succ n =>
            rw [hf₁ v (hrest true (by rw [h]; rfl))]
            rfl
      · obtain ⟨E, hE, hfE⟩ := ih σ
        exact ⟨E, hE, fun v hv => hfE v fun i hi => hv i (by have := i.isLt; omega)⟩

theorem piecewise_extended {k : Nat} {f : (Fin k → Nat) → Nat}
    (hf : IsPiecewisePolynomial k f) : IsExtendedPolyInd f := by
  obtain ⟨E, hE, hfE⟩ := piecewise_cascade hf k (fun _ => false)
  have : f = E := funext fun v => hfE v fun i hi => absurd i.isLt (by omega)
  exact this ▸ hE

theorem piecewise_iff_extended {k : Nat} (f : (Fin k → Nat) → Nat) :
    IsPiecewisePolynomial k f ↔ IsExtendedPolyInd f :=
  ⟨piecewise_extended, extended_piecewise⟩

end Schwichtenberg1976V2.Proofs
