import Proofs.Schwichtenberg1976V2.Semantics
import Proofs.Schwichtenberg1976V2.Sufficiency
import Proofs.Schwichtenberg1976V2.Piecewise

/-!
# λ-definable functions are piecewise polynomials

Fix a zero/non-zero pattern `σ`. Values are taken as *families*: they depend on the input
`v` (with pattern `σ`) and on the values `ζ j` of formal variables of type `0`. A Kripke
logical relation `Rel n τ` (where the world `n` means "formal variables `< n` are in
scope") says at base type that a family has the form `P(v) + ζ j` or `P(v)` for a
polynomial `P`.

The probe with a fresh formal variable shows that a related family of type `0 → 0` is a
translation `x ↦ Q(v) + x` or a constant. Iterating a translation `vᵢ` times gives a
polynomial again, and iterating a constant gives the same constant when `vᵢ ≠ 0` (fixed by
`σ`). So the numerals `v̄ᵢ` are related, and by the fundamental lemma so is every closed term.
Soundness of reduction then turns "`t` defines `f`" into "`f` is that polynomial on `σ`".

No normalization or confluence theorem is needed, and everything is constructive.
-/

namespace Schwichtenberg1976V2.Proofs

open Schwichtenberg1976V2

/-! ## Iteration -/

def itr (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => f (itr f n x)

theorem itr_translate {f : Nat → Nat} {q : Nat} (hf : ∀ x, f x = q + x) :
    ∀ n y, itr f n y = n * q + y
  | 0, y => by simp [itr]
  | n + 1, y => by rw [itr, hf, itr_translate hf n y, Nat.succ_mul]; omega

theorem itr_const {f : Nat → Nat} {c : Nat} (hf : ∀ x, f x = c) (n y : Nat) :
    itr f (n + 1) y = c := hf _

theorem itr_succ_zero : ∀ n, itr Nat.succ n 0 = n
  | 0 => rfl
  | n + 1 => by rw [itr, itr_succ_zero n]

/-- The semantic Church numeral. -/
def churchSem (n : Nat) : Sem Ty.nu := fun g x => itr g n x

/-! ## Families and the Kripke relation -/

section

variable {k : Nat} (σ : Fin k → Bool)

abbrev Inp := {v : Fin k → Nat // Matches σ v}

abbrev Fam (τ : Ty) := (Nat → Nat) → Inp σ → Sem τ

def Indep (n : Nat) {τ : Ty} (a : Fam σ τ) : Prop :=
  ∀ ζ ζ' : Nat → Nat, (∀ j, j < n → ζ j = ζ' j) → ∀ v, a ζ v = a ζ' v

def Rel : Nat → (τ : Ty) → Fam σ τ → Prop
  | n, .zero, a => ∃ P : (Fin k → Nat) → Nat, IsPolynomial P ∧
      ((∃ j, j < n ∧ ∀ ζ v, a ζ v = P v.1 + ζ j) ∨ (∀ ζ v, a ζ v = P v.1))
  | n, .arr A B, g => Indep σ n g ∧
      ∀ m, n ≤ m → ∀ a : Fam σ A, Rel m A a → Rel m B (fun ζ v => g ζ v (a ζ v))

end

variable {k : Nat} {σ : Fin k → Bool}

theorem rel_indep : ∀ {n : Nat} {τ : Ty} {a : Fam σ τ}, Rel σ n τ a → Indep σ n a
  | n, .zero, a, ⟨P, _, h⟩ => by
      intro ζ ζ' hζ v
      rcases h with ⟨j, hj, h⟩ | h
      · rw [h, h, hζ j hj]
      · rw [h, h]
  | _, .arr _ _, _, h => h.1

theorem rel_mono : ∀ {n m : Nat} {τ : Ty} {a : Fam σ τ}, n ≤ m → Rel σ n τ a → Rel σ m τ a
  | n, m, .zero, a, hnm, ⟨P, hP, h⟩ => by
      refine ⟨P, hP, ?_⟩
      rcases h with ⟨j, hj, h⟩ | h
      · exact Or.inl ⟨j, by omega, h⟩
      · exact Or.inr h
  | n, m, .arr _ _, g, hnm, ⟨hind, hg⟩ =>
      ⟨fun ζ ζ' hζ v => hind ζ ζ' (fun j hj => hζ j (by omega)) v,
        fun m' hm' a ha => hg m' (by omega) a ha⟩

theorem rel_default : ∀ (n : Nat) (τ : Ty), Rel σ n τ (fun _ _ => Sem.default τ)
  | n, .zero => ⟨fun _ => 0, .const 0, Or.inr fun _ _ => rfl⟩
  | n, .arr _ B => ⟨fun _ _ _ _ => rfl, fun m _ _ _ => rel_default m B⟩

/-! ## The fundamental lemma -/

theorem fundamental {t : Term} {τ : Ty} (ht : HasType t τ) :
    ∀ (n : Nat) (γ : ∀ x : Var, Fam σ x.ty), (∀ x, Rel σ n x.ty (γ x)) →
      Rel σ n τ (fun ζ v => evalT τ t (fun x => γ x ζ v)) := by
  induction ht with
  | var x =>
      intro n γ hγ
      have : (fun ζ v => evalT x.ty (.var x) (fun y => γ y ζ v)) = γ x := by
        funext ζ v; exact evalT_var _ _
      rw [this]; exact hγ x
  | @app t s σ' τ ht hs iht ihs =>
      intro n γ hγ
      have : (fun ζ v => evalT τ (.app t s) (fun y => γ y ζ v)) =
          fun ζ v => (evalT (.arr σ' τ) t (fun y => γ y ζ v)) (evalT σ' s (fun y => γ y ζ v)) := by
        funext ζ v; exact evalT_app ht hs _
      rw [this]
      exact (iht n γ hγ).2 n (Nat.le_refl n) _ (ihs n γ hγ)
  | @lam x b τ hb ih =>
      intro n γ hγ
      have : (fun ζ v => evalT (.arr x.ty τ) (.lam x b) (fun y => γ y ζ v)) =
          fun ζ v => fun a => evalT τ b (Env.upd (fun y => γ y ζ v) x a) := by
        funext ζ v; exact evalT_lam hb _
      rw [this]
      refine ⟨?_, fun m hnm a ha => ?_⟩
      · intro ζ ζ' hζ v
        have henv : (fun y => γ y ζ v) = (fun y => γ y ζ' v) := by
          funext y; exact rel_indep (hγ y) ζ ζ' hζ v
        show (fun a => evalT τ b (Env.upd (fun y => γ y ζ v) x a)) =
          (fun a => evalT τ b (Env.upd (fun y => γ y ζ' v) x a))
        rw [henv]
      · let γ' : ∀ y : Var, Fam σ y.ty := fun y ζ v => Env.upd (fun y => γ y ζ v) x (a ζ v) y
        have hγ' : ∀ y, Rel σ m y.ty (γ' y) := by
          intro y
          by_cases hyx : y = x
          · subst hyx
            have : γ' y = a := by funext ζ v; exact Env.upd_same _ _ _
            rw [this]; exact ha
          · have : γ' y = γ y := by funext ζ v; exact Env.upd_other _ _ hyx
            rw [this]; exact rel_mono hnm (hγ y)
        exact ih m γ' hγ'

/-! ## The base families -/

theorem rel_succ (n : Nat) : Rel σ n Ty.endo (fun _ _ => Nat.succ) := by
  refine ⟨fun _ _ _ _ => rfl, fun m _ a ⟨P, hP, h⟩ => ⟨fun v => P v + 1, .add hP (.const 1), ?_⟩⟩
  rcases h with ⟨j, hj, h⟩ | h
  · exact Or.inl ⟨j, hj, fun ζ v => by
      show Nat.succ (a ζ v) = P v.1 + 1 + ζ j; rw [h]; omega⟩
  · exact Or.inr fun ζ v => by show Nat.succ (a ζ v) = P v.1 + 1; rw [h]

/-- A related family of type `0 → 0` is a translation or a constant. -/
theorem char_endo {m : Nat} {g : Fam σ Ty.endo} (hg : Rel σ m Ty.endo g) :
    (∃ Q : (Fin k → Nat) → Nat, IsPolynomial Q ∧ ∀ ζ v x, g ζ v x = Q v.1 + x) ∨
    (∃ c : Fam σ .zero, Rel σ m .zero c ∧ ∀ ζ v x, g ζ v x = c ζ v) := by
  obtain ⟨hind, hg⟩ := hg
  have hprobe : Rel σ (m + 1) .zero (fun ζ _ => ζ m) :=
    ⟨fun _ => 0, .const 0, Or.inl ⟨m, by omega, fun ζ v => by show ζ m = 0 + ζ m; omega⟩⟩
  obtain ⟨P, hP, h⟩ := hg (m + 1) (by omega) _ hprobe
  let upd (ζ : Nat → Nat) (x : Nat) : Nat → Nat := fun j => if j = m then x else ζ j
  have hg_upd : ∀ ζ v x, g ζ v x = g (upd ζ x) v x := by
    intro ζ v x
    rw [hind ζ (upd ζ x) (fun j hj => by simp [upd, Nat.ne_of_lt hj]) v]
  have hval : ∀ ζ v x, g ζ v x = g (upd ζ x) v (upd ζ x m) := by
    intro ζ v x
    rw [hg_upd ζ v x]
    simp [upd]
  have hum : ∀ ζ x, upd ζ x m = x := fun ζ x => if_pos rfl
  rcases h with ⟨j, hj, h⟩ | h
  · by_cases hjm : j = m
    · refine Or.inl ⟨P, hP, fun ζ v x => ?_⟩
      have e : g (upd ζ x) v (upd ζ x m) = P v.1 + upd ζ x j := h (upd ζ x) v
      refine (hval ζ v x).trans (e.trans ?_)
      rw [hjm, hum]
    · refine Or.inr ⟨fun ζ v => P v.1 + ζ j, ⟨P, hP, Or.inl ⟨j, by omega, fun _ _ => rfl⟩⟩,
        fun ζ v x => ?_⟩
      have e : g (upd ζ x) v (upd ζ x m) = P v.1 + upd ζ x j := h (upd ζ x) v
      refine (hval ζ v x).trans (e.trans ?_)
      show P v.1 + (if j = m then x else ζ j) = P v.1 + ζ j
      rw [if_neg hjm]
  · refine Or.inr ⟨fun _ v => P v.1, ⟨P, hP, Or.inr fun _ _ => rfl⟩, fun ζ v x => ?_⟩
    have e : g (upd ζ x) v (upd ζ x m) = P v.1 := h (upd ζ x) v
    exact (hval ζ v x).trans e

theorem rel_numeral (n : Nat) (i : Fin k) :
    Rel σ n Ty.nu (fun _ v => churchSem (v.1 i)) := by
  refine ⟨fun _ _ _ _ => rfl, fun m _ g hg => ⟨?_, fun m' hmm' a ha => ?_⟩⟩
  · intro ζ ζ' hζ v
    show (fun x => itr (g ζ v) (v.1 i) x) = (fun x => itr (g ζ' v) (v.1 i) x)
    rw [rel_indep hg ζ ζ' hζ v]
  · show Rel σ m' .zero (fun ζ v => itr (g ζ v) (v.1 i) (a ζ v))
    obtain ⟨P', hP', ha⟩ := ha
    rcases char_endo hg with ⟨Q, hQ, hgQ⟩ | ⟨c, hc, hgc⟩
    · -- translation: iterating adds `vᵢ · Q(v)`
      refine ⟨fun v => v i * Q v + P' v, .add (.mul (.proj i) hQ) hP', ?_⟩
      rcases ha with ⟨j, hj, ha⟩ | ha
      · refine Or.inl ⟨j, hj, fun ζ v => ?_⟩
        have e : a ζ v = P' v.1 + ζ j := ha ζ v
        show itr (g ζ v) (v.1 i) (a ζ v) = v.1 i * Q v.1 + P' v.1 + ζ j
        refine (itr_translate (hgQ ζ v) _ _).trans ?_
        rw [e]; omega
      · refine Or.inr fun ζ v => ?_
        have e : a ζ v = P' v.1 := ha ζ v
        show itr (g ζ v) (v.1 i) (a ζ v) = v.1 i * Q v.1 + P' v.1
        refine (itr_translate (hgQ ζ v) _ _).trans ?_
        rw [e]
    · -- constant: `σ` fixes whether `vᵢ = 0`
      cases hσ : σ i with
      | false =>
          refine ⟨P', hP', ?_⟩
          have hv0 : ∀ v : Inp σ, v.1 i = 0 := by
            intro v
            have := v.2 i
            rw [hσ] at this
            cases h : v.1 i with
            | zero => rfl
            | succ n => rw [h] at this; exact Bool.noConfusion this
          rcases ha with ⟨j, hj, ha⟩ | ha
          · exact Or.inl ⟨j, hj, fun ζ v =>
              (congrArg (fun n => itr (g ζ v) n (a ζ v)) (hv0 v)).trans (ha ζ v)⟩
          · exact Or.inr fun ζ v =>
              (congrArg (fun n => itr (g ζ v) n (a ζ v)) (hv0 v)).trans (ha ζ v)
      | true =>
          have hv1 : ∀ v : Inp σ, ∃ n, v.1 i = n + 1 := by
            intro v
            have := v.2 i
            rw [hσ] at this
            cases h : v.1 i with
            | zero => rw [h] at this; exact Bool.noConfusion this
            | succ n => exact ⟨n, rfl⟩
          obtain ⟨Pc, hPc, hcf⟩ := rel_mono hmm' hc
          refine ⟨Pc, hPc, ?_⟩
          have hit : ∀ ζ v, itr (g ζ v) (v.1 i) (a ζ v) = c ζ v := by
            intro ζ v
            obtain ⟨n, hn⟩ := hv1 v
            exact (congrArg (fun n => itr (g ζ v) n (a ζ v)) hn).trans
              (itr_const (hgc ζ v) n _)
          rcases hcf with ⟨j, hj, hcf⟩ | hcf
          · exact Or.inl ⟨j, hj, fun ζ v => (hit ζ v).trans (hcf ζ v)⟩
          · exact Or.inr fun ζ v => (hit ζ v).trans (hcf ζ v)

/-! ## Applying a defining term to numerals -/

def applyAll : (k : Nat) → Sem (Ty.nuArity k) → (Fin k → Sem Ty.nu) → Sem Ty.nu
  | 0, f, _ => f
  | k + 1, f, xs => applyAll k (f (xs 0)) (fun i => xs i.succ)

theorem rel_applyAll {n : Nat} :
    ∀ (m : Nat) {F : Fam σ (Ty.nuArity m)} {G : Fin m → Fam σ Ty.nu},
      Rel σ n (Ty.nuArity m) F → (∀ i, Rel σ n Ty.nu (G i)) →
      Rel σ n Ty.nu (fun ζ v => applyAll m (F ζ v) (fun i => G i ζ v))
  | 0, _, _, hF, _ => hF
  | m + 1, F, G, hF, hG =>
      rel_applyAll m (F := fun ζ v => F ζ v (G 0 ζ v)) (G := fun i => G i.succ)
        (hF.2 n (Nat.le_refl n) _ (hG 0)) (fun i => hG i.succ)

theorem evalT_iterApp (ρ : Env) {b : Term} (hb : HasType b .zero) :
    ∀ n, evalT .zero (iterApp (.var numα) b n) ρ = itr (ρ numα) n (evalT .zero b ρ)
  | 0 => rfl
  | n + 1 => by
      have hα : HasType (.var numα) (.arr .zero .zero) := .var numα
      rw [iterApp_succ, evalT_app hα (iterApp_hasType rfl hb n), evalT_iterApp ρ hb n]
      rfl

theorem evalT_numeral (n : Nat) (ρ : Env) : evalT Ty.nu (churchNumeral n) ρ = churchSem n := by
  have hbody : HasType (iterApp (.var numα) (.var numx) n) .zero :=
    iterApp_hasType rfl (.var numx) n
  have hinner : HasType (.lam numx (iterApp (.var numα) (.var numx) n)) Ty.endo :=
    .lam numx hbody
  rw [churchNumeral_eq]
  rw [show evalT Ty.nu (.lam numα (.lam numx (iterApp (.var numα) (.var numx) n))) ρ =
      fun g => evalT Ty.endo (.lam numx (iterApp (.var numα) (.var numx) n)) (ρ.upd numα g)
    from evalT_lam (x := numα) hinner ρ]
  funext g x
  rw [show evalT Ty.endo (.lam numx (iterApp (.var numα) (.var numx) n)) (ρ.upd numα g) =
      fun x => evalT .zero (iterApp (.var numα) (.var numx) n) ((ρ.upd numα g).upd numx x)
    from evalT_lam (x := numx) hbody _]
  show evalT .zero (iterApp (.var numα) (.var numx) n) (((ρ.upd numα g).upd numx x)) =
    itr g n x
  rw [evalT_iterApp _ (.var numx) n]
  have h1 : (ρ.upd numα g).upd numx x numα = g :=
    (Env.upd_other _ _ ne_αx).trans (Env.upd_same _ _ _)
  have h2 : evalT .zero (.var numx) ((ρ.upd numα g).upd numx x) = x :=
    (evalT_var numx _).trans (Env.upd_same _ _ _)
  exact (congrArg (fun f => itr f n (evalT .zero (.var numx) ((ρ.upd numα g).upd numx x)))
    h1).trans (congrArg (fun y => itr g n y) h2)

theorem evalT_appMany_numerals (ρ : Env) :
    ∀ (m : Nat) (t : Term) (v : Fin m → Nat), HasType t (Ty.nuArity m) →
      evalT Ty.nu (Term.appMany t (numeralArgs m v)) ρ =
        applyAll m (evalT (Ty.nuArity m) t ρ) (fun i => churchSem (v i))
  | 0, t, v, _ => rfl
  | m + 1, t, v, ht => by
      have hn := numeral_hasType (v 0)
      show evalT Ty.nu (Term.appMany (.app t (churchNumeral (v 0)))
        (numeralArgs m (fun i => v i.succ))) ρ = _
      rw [evalT_appMany_numerals ρ m _ _ (.app ht hn)]
      show applyAll m (evalT (Ty.nuArity m) (.app t (churchNumeral (v 0))) ρ) _ =
        applyAll m (evalT (Ty.nuArity (m + 1)) t ρ (churchSem (v 0))) _
      rw [evalT_app ht hn, evalT_numeral]
      rfl

/-! ## Necessity -/

theorem necessity {k : Nat} {f : (Fin k → Nat) → Nat} (h : IsLambdaDefinable k f) :
    IsPiecewisePolynomial k f := by
  obtain ⟨t, hty, _, hred⟩ := h
  intro σ
  let ρ0 : Env := fun x => Sem.default x.ty
  -- `f v` is read off the denotation of `t`
  have hval : ∀ v, f v = applyAll k (evalT (Ty.nuArity k) t ρ0) (fun i => churchSem (v i))
      Nat.succ 0 := by
    intro v
    have hT : HasType (Term.appMany t (numeralArgs k v)) Ty.nu := by
      rw [numeralArgs_eq]
      exact appMany_hasType _ (by simpa using hty) (by
        intro a ha
        simp only [List.mem_map] at ha
        obtain ⟨i, _, rfl⟩ := ha
        exact numeral_hasType _)
    have := (reduces_sound (hred v) Ty.nu hT).2 ρ0
    rw [evalT_appMany_numerals ρ0 k t v hty, evalT_numeral] at this
    rw [this]
    exact (itr_succ_zero (f v)).symm
  -- the fundamental lemma for `t`, applied to the numerals, `succ` and a formal variable
  have hF : Rel σ 0 (Ty.nuArity k) (fun _ _ => evalT (Ty.nuArity k) t ρ0) :=
    fundamental hty 0 (fun x _ _ => Sem.default x.ty) (fun x => rel_default 0 x.ty)
  have hH := rel_applyAll k hF (fun i => rel_numeral (σ := σ) 0 i)
  have h1 := hH.2 0 (Nat.le_refl 0) _ (rel_succ 0)
  obtain ⟨P, hP, hform⟩ := h1.2 1 (by omega) (fun ζ _ => ζ 0)
    ⟨fun _ => 0, .const 0, Or.inl ⟨0, by omega, fun ζ v => by show ζ 0 = 0 + ζ 0; omega⟩⟩
  refine ⟨P, hP, fun v hv => ?_⟩
  rw [hval v]
  rcases hform with ⟨j, hj, hform⟩ | hform
  · have := hform (fun _ => 0) ⟨v, hv⟩
    simpa using this
  · exact hform (fun _ => 0) ⟨v, hv⟩

end Schwichtenberg1976V2.Proofs
