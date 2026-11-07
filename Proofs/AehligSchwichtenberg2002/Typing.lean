import Proofs.AehligSchwichtenberg2002.Basic

/-!
# Structural facts about affine typing

* **Context transfer**: a typed term can be retyped in any context containing its free
  variables. This covers both weakening and strengthening.
* **Linearity**: the two sides of a multiplicative rule have disjoint free variables.
* **Uniqueness of types**: variables and constructors carry their types.
-/

namespace AehligSchwichtenberg2002.Proofs

open AehligSchwichtenberg2002

/-- `Δ` contains every free variable of `t`. -/
def Covers (Δ : Context) (t : Term) : Prop := ∀ v ∈ freeVarOccurrences t, v ∈ Δ

/-- Split `Δ` into the part outside `S` and the part inside `S`. -/
theorem split_ctx (Δ : Context) (S : List Var) :
    IsDisjointCtxUnion (Δ.filter (fun v => decide (v ∉ S))) (Δ.filter (fun v => decide (v ∈ S))) Δ := by
  refine ⟨fun v h1 h2 => ?_, fun v => ?_⟩
  · simp only [List.mem_filter, decide_eq_true_eq] at h1 h2
    exact h1.2 h2.2
  · simp only [List.mem_filter, decide_eq_true_eq]
    by_cases h : v ∈ S
    · exact ⟨fun hv => Or.inr ⟨hv, h⟩, fun hv => hv.elim (fun h' => h'.1) (fun h' => h'.1)⟩
    · exact ⟨fun hv => Or.inl ⟨hv, h⟩, fun hv => hv.elim (fun h' => h'.1) (fun h' => h'.1)⟩

theorem mem_filter_not {Δ S : List Var} {v : Var} :
    v ∈ Δ.filter (fun w => decide (w ∉ S)) ↔ v ∈ Δ ∧ v ∉ S := by
  simp

theorem mem_filter_in {Δ S : List Var} {v : Var} :
    v ∈ Δ.filter (fun w => decide (w ∈ S)) ↔ v ∈ Δ ∧ v ∈ S := by
  simp

/-- Free variables of the two parts of a multiplicative rule are disjoint. -/
theorem disjoint_fv {Γ₁ Γ₂ Γ : Context} {t s : Term} {τ ρ : Ty}
    (hu : IsDisjointCtxUnion Γ₁ Γ₂ Γ) (ht : HasType Γ₁ t τ) (hs : HasType Γ₂ s ρ) :
    ∀ v ∈ freeVarOccurrences t, v ∉ freeVarOccurrences s :=
  fun v h1 h2 => hu.1 v (fvo_subset_ctx ht v h1) (fvo_subset_ctx hs v h2)

/-- **Context transfer.** -/
theorem transfer {Γ : Context} {t : Term} {τ : Ty} (h : HasType Γ t τ) :
    ∀ Δ : Context, Covers Δ t → HasType Δ t τ := by
  induction h with
  | var x _ =>
      intro Δ hΔ
      have hx : x ∈ Δ := hΔ x (by simp)
      refine .var x (Γ := Δ.filter (fun v => decide (v ∉ [x]))) ⟨fun v h1 h2 => ?_, fun v => ?_⟩
      · rw [mem_filter_not] at h1; exact h1.2 h2
      · rw [mem_filter_not]
        by_cases hv : v = x
        · subst hv; simp [hx]
        · simp [hv]
  | const _ c => intro Δ _; exact .const Δ c
  | @lam Γ₀ Γ' x t ρ _ _ ih =>
      intro Δ hΔ
      refine .lam x (Γ' := x :: Δ) (fun v => by simp [or_comm]) (ih _ fun v hv => ?_)
      by_cases hvx : v = x
      · subst hvx; simp
      · exact List.mem_cons_of_mem _ (hΔ v (by simp [hv, hvx]))
  | @app Γ₁ Γ₂ Γ₀ t s τ ρ hu ht hs ih1 ih2 =>
      intro Δ hΔ
      have hd := disjoint_fv hu ht hs
      refine .app (split_ctx Δ (freeVarOccurrences s)) (ih1 _ fun v hv => ?_) (ih2 _ fun v hv => ?_)
      · exact mem_filter_not.2 ⟨hΔ v (by simp [hv]), hd v hv⟩
      · exact mem_filter_in.2 ⟨hΔ v (by simp [hv]), hv⟩
  | pair _ _ ih1 ih2 =>
      intro Δ hΔ
      exact .pair (ih1 _ fun v hv => hΔ v (by simp [hv])) (ih2 _ fun v hv => hΔ v (by simp [hv]))
  | projLeft _ ih => intro Δ hΔ; exact .projLeft (ih _ fun v hv => hΔ v (by simp [hv]))
  | projRight _ ih => intro Δ hΔ; exact .projRight (ih _ fun v hv => hΔ v (by simp [hv]))
  | @boolElim Γ₁ Γ₂ Γ₀ t s r τ hu ht hs hr ih1 ih2 ih3 =>
      intro Δ hΔ
      have hdt : ∀ v ∈ freeVarOccurrences t, v ∉ freeVarOccurrences (.pair s r) := by
        intro v h1 h2
        rcases (mem_fvo_pair _ _ _).1 h2 with h2 | h2
        · exact disjoint_fv hu ht hs v h1 h2
        · exact disjoint_fv hu ht hr v h1 h2
      refine .boolElim (split_ctx Δ (freeVarOccurrences (.pair s r)))
        (ih1 _ fun v hv => ?_) (ih2 _ fun v hv => ?_) (ih3 _ fun v hv => ?_)
      · exact mem_filter_not.2 ⟨hΔ v (by simp [hv]), hdt v hv⟩
      · exact mem_filter_in.2 ⟨hΔ v (by simp [hv]), by simp [hv]⟩
      · exact mem_filter_in.2 ⟨hΔ v (by simp [hv]), by simp [hv]⟩
  | @tensorElim Γ₁ Γ₂ Γ₂' Γ₀ t s x y σ hxy hu₂ hu ht hs ih1 ih2 =>
      intro Δ hΔ
      let S := freeVarOccurrences (.lam x (.lam y s))
      let Δ₂ := Δ.filter (fun v => decide (v ∈ S))
      have hS : ∀ v, v ∈ S ↔ v ∈ freeVarOccurrences s ∧ v ≠ y ∧ v ≠ x := by
        intro v; simp [S, and_assoc]
      have hdt : ∀ v ∈ freeVarOccurrences t, v ∉ S := by
        intro v h1 h2
        obtain ⟨h2, hvy, hvx⟩ := (hS v).1 h2
        rcases (hu₂.2 v).1 (fvo_subset_ctx hs v h2) with h | h
        · exact hu.1 v (fvo_subset_ctx ht v h1) h
        · simp at h; rcases h with h | h
          · exact hvx h
          · exact hvy h
      refine .tensorElim x y (Γ₂ := Δ₂) (Γ₂' := Δ₂ ++ [x, y]) hxy ⟨fun v h1 h2 => ?_, fun v => ?_⟩
        (split_ctx Δ S) (ih1 _ fun v hv => ?_) (ih2 _ fun v hv => ?_)
      · obtain ⟨_, hvS⟩ := mem_filter_in.1 h1
        obtain ⟨_, hvy, hvx⟩ := (hS v).1 hvS
        simp at h2; rcases h2 with h2 | h2
        · exact hvx h2
        · exact hvy h2
      · simp
      · exact mem_filter_not.2 ⟨hΔ v (by simp [hv]), hdt v hv⟩
      · by_cases hvx : v = x
        · subst hvx; simp
        · by_cases hvy : v = y
          · subst hvy; simp
          · refine List.mem_append_left _ (mem_filter_in.2 ⟨hΔ v ?_, (hS v).2 ⟨hv, hvy, hvx⟩⟩)
            simp [hv, hvx, hvy]
  | listElim _ hs ih1 _ =>
      intro Δ hΔ
      exact .listElim (ih1 _ fun v hv => hΔ v (by simp [hv])) hs

/-- A typed term is typed in its own free-variable list. -/
theorem typed_in_fv {Γ : Context} {t : Term} {τ : Ty} (h : HasType Γ t τ) :
    HasType (freeVarOccurrences t) t τ :=
  transfer h _ fun _ hv => hv

end AehligSchwichtenberg2002.Proofs
