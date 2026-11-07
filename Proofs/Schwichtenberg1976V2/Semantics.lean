import Proofs.Schwichtenberg1976V2.Reduction

/-!
# Set-theoretic semantics and soundness of reduction

Types denote sets: `⟦0⟧ = ℕ` and `⟦σ → τ⟧ = ⟦σ⟧ → ⟦τ⟧`. A typed term denotes a function
of the environment. Reduction preserves typing and denotation (`reducesTo_sound`), including
the capture-avoiding renaming inside `substTerm`.

Everything is constructive. The casts between `⟦τ⟧` and `⟦τ'⟧` use decidable equality of
types.
-/

namespace Schwichtenberg1976V2.Proofs

open Schwichtenberg1976V2

/-! ## Denotations -/

def Sem : Ty → Type
  | .zero => Nat
  | .arr a b => Sem a → Sem b

def Sem.default : (τ : Ty) → Sem τ
  | .zero => (0 : Nat)
  | .arr _ b => fun _ => Sem.default b

/-- Environments assign every typed variable a value of its type. -/
def Env : Type := (x : Var) → Sem x.ty

def Env.upd (ρ : Env) (x : Var) (a : Sem x.ty) : Env :=
  fun v => if h : v = x then cast (congrArg (fun y : Var => Sem y.ty) h.symm) a else ρ v

theorem Env.upd_same (ρ : Env) (x : Var) (a : Sem x.ty) : ρ.upd x a x = a := by
  simp [Env.upd]

theorem Env.upd_other (ρ : Env) {x v : Var} (a : Sem x.ty) (h : v ≠ x) : ρ.upd x a v = ρ v := by
  simp [Env.upd, h]

theorem Env.upd_upd_same (ρ : Env) (x : Var) (a b : Sem x.ty) :
    (ρ.upd x a).upd x b = ρ.upd x b := by
  funext v
  by_cases h : v = x
  · subst h; simp [Env.upd]
  · simp [Env.upd, h]

theorem Env.upd_comm (ρ : Env) {x y : Var} (a : Sem x.ty) (b : Sem y.ty) (h : x ≠ y) :
    (ρ.upd x a).upd y b = (ρ.upd y b).upd x a := by
  funext v
  by_cases hx : v = x
  · subst hx; simp [Env.upd, h]
  · by_cases hy : v = y
    · subst hy; simp [Env.upd, hx]
    · simp [Env.upd, hx, hy]

/-- Inferred type of a raw term (meaningful for typed terms). -/
def resTy : Ty → Ty
  | .arr _ b => b
  | .zero => .zero

def tyOf : Term → Ty
  | .var x => x.ty
  | .lam x b => .arr x.ty (tyOf b)
  | .app t _ => resTy (tyOf t)

def applySem : (A S : Ty) → Sem A → Sem S → Sem (resTy A)
  | .arr a b, S, f, x => if h : S = a then f (cast (congrArg Sem h) x) else Sem.default b
  | .zero, _, _, _ => (0 : Nat)

/-- Denotation of a raw term; ill-typed applications get a default value. -/
def eval : (t : Term) → Env → Sem (tyOf t)
  | .var x, ρ => ρ x
  | .lam x b, ρ => fun a => eval b (ρ.upd x a)
  | .app t s, ρ => applySem (tyOf t) (tyOf s) (eval t ρ) (eval s ρ)

theorem tyOf_of_hasType {t : Term} {τ : Ty} (h : HasType t τ) : tyOf t = τ := by
  induction h with
  | var x => rfl
  | app _ _ iht ihs => simp [tyOf, iht, resTy]
  | lam x _ ih => simp [tyOf, ih]

/-- Denotation at a prescribed type. -/
def evalT (τ : Ty) (t : Term) (ρ : Env) : Sem τ :=
  if h : tyOf t = τ then cast (congrArg Sem h) (eval t ρ) else Sem.default τ

theorem evalT_var (x : Var) (ρ : Env) : evalT x.ty (.var x) ρ = ρ x := by
  unfold evalT
  split
  · rfl
  · rename_i h; exact absurd rfl h

theorem cast_lam_aux {A B τ : Ty} (h : B = τ) (f : Sem A → Sem B) :
    cast (congrArg Sem (congrArg (Ty.arr A) h)) f = fun a => cast (congrArg Sem h) (f a) := by
  subst h; rfl

theorem evalT_lam {x : Var} {b : Term} {τ : Ty} (hb : HasType b τ) (ρ : Env) :
    evalT (.arr x.ty τ) (.lam x b) ρ = fun a => evalT τ b (ρ.upd x a) := by
  have h := tyOf_of_hasType hb
  have h' : tyOf (.lam x b) = .arr x.ty τ := by simp [tyOf, h]
  simp only [evalT, dif_pos h', dif_pos h]
  exact cast_lam_aux h _

theorem applySem_arr (S τ : Ty) (f : Sem S → Sem τ) (x : Sem S) :
    applySem (.arr S τ) S f x = f x := by
  show (if h : S = S then f (cast (congrArg Sem h) x) else Sem.default τ) = f x
  rw [dif_pos rfl]
  rfl

theorem cast_app_aux {A S σ τ : Ty} (hA : A = .arr σ τ) (hS : S = σ) (f : Sem A) (x : Sem S)
    (hR : resTy A = τ) :
    cast (congrArg Sem hR) (applySem A S f x) =
      (cast (congrArg Sem hA) f : Sem σ → Sem τ) (cast (congrArg Sem hS) x) := by
  subst hA; subst hS
  exact applySem_arr S τ f x

theorem evalT_app {t s : Term} {σ τ : Ty} (ht : HasType t (.arr σ τ)) (hs : HasType s σ)
    (ρ : Env) :
    evalT τ (.app t s) ρ = (evalT (.arr σ τ) t ρ) (evalT σ s ρ) := by
  have h1 := tyOf_of_hasType ht
  have h2 := tyOf_of_hasType hs
  have h' : tyOf (.app t s) = τ := by simp [tyOf, h1, resTy]
  simp only [evalT, dif_pos h', dif_pos h1, dif_pos h2]
  exact cast_app_aux h1 h2 _ _ h'

/-! ## Coincidence: only free variables matter -/

theorem eval_coincide :
    ∀ (t : Term) (ρ ρ' : Env), (∀ v ∈ freeVarOccurrences t, ρ v = ρ' v) → eval t ρ = eval t ρ'
  | .var x, ρ, ρ', h => h x (by simp)
  | .app t s, ρ, ρ', h => by
      simp only [eval]
      rw [eval_coincide t ρ ρ' (fun v hv => h v (by simp [hv])),
        eval_coincide s ρ ρ' (fun v hv => h v (by simp [hv]))]
  | .lam x b, ρ, ρ', h => by
      simp only [eval]
      funext a
      apply eval_coincide b
      intro v hv
      by_cases hvx : v = x
      · subst hvx; rw [Env.upd_same, Env.upd_same]
      · rw [Env.upd_other _ _ hvx, Env.upd_other _ _ hvx]
        exact h v (by simp [hv, hvx])

theorem evalT_coincide (τ : Ty) (t : Term) {ρ ρ' : Env}
    (h : ∀ v ∈ freeVarOccurrences t, ρ v = ρ' v) : evalT τ t ρ = evalT τ t ρ' := by
  simp only [evalT, eval_coincide t ρ ρ' h]

/-! ## Renaming -/

theorem renameFreeVar_self (x : Var) : ∀ t : Term, renameFreeVar t x x = t
  | .var v => by simp only [renameFreeVar]; split <;> simp_all
  | .app r s => by simp [renameFreeVar, renameFreeVar_self x r, renameFreeVar_self x s]
  | .lam v b => by simp only [renameFreeVar]; split <;> simp [renameFreeVar_self x b]

theorem rename_hasType_iff {x y : Var} (hty : y.ty = x.ty) :
    ∀ (t : Term) (τ : Ty), HasType (renameFreeVar t x y) τ ↔ HasType t τ
  | .var v, τ => by
      simp only [renameFreeVar]
      by_cases h : v = x
      · subst h
        simp only [beq_self_eq_true, if_true]
        constructor
        · intro hy; have := hasType_var_inv hy; rw [this, hty]; exact .var _
        · intro hv; have := hasType_var_inv hv; rw [this, ← hty]; exact .var _
      · simp [h]
  | .app r s, τ => by
      simp only [renameFreeVar]
      constructor
      · intro h
        obtain ⟨σ, hr, hs⟩ := hasType_app_inv h
        exact .app ((rename_hasType_iff hty r _).1 hr) ((rename_hasType_iff hty s _).1 hs)
      · intro h
        obtain ⟨σ, hr, hs⟩ := hasType_app_inv h
        exact .app ((rename_hasType_iff hty r _).2 hr) ((rename_hasType_iff hty s _).2 hs)
  | .lam v b, τ => by
      simp only [renameFreeVar]
      split
      · exact Iff.rfl
      · constructor
        · intro h
          obtain ⟨ρ, rfl, hb⟩ := hasType_lam_inv h
          exact .lam v ((rename_hasType_iff hty b _).1 hb)
        · intro h
          obtain ⟨ρ, rfl, hb⟩ := hasType_lam_inv h
          exact .lam v ((rename_hasType_iff hty b _).2 hb)

/-- Renaming a free variable `x` to a fresh `y` of the same type. -/
theorem rename_eval {x : Var} (n : Nat) :
    ∀ (t : Term), (⟨n, x.ty⟩ : Var) ∉ allVars t → ∀ (τ : Ty), HasType t τ → ∀ ρ : Env,
      evalT τ (renameFreeVar t x ⟨n, x.ty⟩) ρ = evalT τ t (ρ.upd x (ρ ⟨n, x.ty⟩))
  | .var v, hfresh, τ, ht, ρ => by
      have := hasType_var_inv ht
      subst this
      simp only [renameFreeVar]
      by_cases h : v = x
      · subst h
        simp only [beq_self_eq_true, if_true]
        rw [show evalT v.ty (.var ⟨n, v.ty⟩) ρ = ρ ⟨n, v.ty⟩ from evalT_var ⟨n, v.ty⟩ ρ,
          evalT_var, Env.upd_same]
      · simp only [beq_iff_eq, h, if_false]
        rw [evalT_var, evalT_var, Env.upd_other _ _ h]
  | .app r s, hfresh, τ, ht, ρ => by
      simp only [allVars, List.mem_append, not_or] at hfresh
      obtain ⟨σ, hr, hs⟩ := hasType_app_inv ht
      have hty : (⟨n, x.ty⟩ : Var).ty = x.ty := rfl
      simp only [renameFreeVar]
      rw [evalT_app ((rename_hasType_iff hty r _).2 hr) ((rename_hasType_iff hty s _).2 hs),
        evalT_app hr hs, rename_eval n r hfresh.1 _ hr, rename_eval n s hfresh.2 _ hs]
  | .lam v b, hfresh, τ, ht, ρ => by
      simp only [allVars, List.mem_cons, not_or] at hfresh
      obtain ⟨ρ', rfl, hb⟩ := hasType_lam_inv ht
      simp only [renameFreeVar]
      by_cases h : v = x
      · subst h
        simp only [beq_self_eq_true, if_true]
        rw [evalT_lam hb, evalT_lam hb]
        funext a
        rw [Env.upd_upd_same]
      · simp only [beq_iff_eq, h, if_false]
        have hty : (⟨n, x.ty⟩ : Var).ty = x.ty := rfl
        rw [evalT_lam ((rename_hasType_iff hty b _).2 hb), evalT_lam hb]
        funext a
        have hval : (ρ.upd v a) ⟨n, x.ty⟩ = ρ ⟨n, x.ty⟩ := Env.upd_other _ _ hfresh.1
        rw [rename_eval n b hfresh.2 _ hb, hval, Env.upd_comm _ _ _ h]

/-! ## Substitution -/

theorem allVar_id_le_maxVarId : ∀ (t : Term) (v : Var), v ∈ allVars t → v.id ≤ maxVarId t
  | .var x, v, h => by simp [allVars] at h; subst h; simp [maxVarId]
  | .app r s, v, h => by
      simp only [allVars, List.mem_append] at h
      simp only [maxVarId]
      rcases h with h | h
      · exact Nat.le_trans (allVar_id_le_maxVarId r v h) (Nat.le_max_left _ _)
      · exact Nat.le_trans (allVar_id_le_maxVarId s v h) (Nat.le_max_right _ _)
  | .lam x b, v, h => by
      simp only [allVars, List.mem_cons] at h
      simp only [maxVarId]
      rcases h with h | h
      · subst h; exact Nat.le_max_left _ _
      · exact Nat.le_trans (allVar_id_le_maxVarId b v h) (Nat.le_max_right _ _)

theorem fvo_subset_allVars : ∀ (t : Term) (v : Var), v ∈ freeVarOccurrences t → v ∈ allVars t
  | .var x, v, h => by simpa [allVars] using h
  | .app r s, v, h => by
      rcases (mem_fvo_app _ _ _).1 h with h | h
      · exact List.mem_append_left _ (fvo_subset_allVars r v h)
      · exact List.mem_append_right _ (fvo_subset_allVars s v h)
  | .lam x b, v, h => List.mem_cons_of_mem _ (fvo_subset_allVars b v ((mem_fvo_lam _ _ _).1 h).1)

theorem subst_sound (x : Var) (s : Term) (hs : HasType s x.ty) :
    ∀ (t : Term) (τ : Ty), HasType t τ →
      HasType (substTerm t x s) τ ∧
      ∀ ρ : Env, evalT τ (substTerm t x s) ρ = evalT τ t (ρ.upd x (evalT x.ty s ρ))
  | .var v, τ, ht => by
      have := hasType_var_inv ht
      subst this
      rw [subst_var]
      by_cases h : v = x
      · subst h
        refine ⟨by rw [if_pos rfl]; exact hs, fun ρ => ?_⟩
        rw [if_pos rfl, evalT_var, Env.upd_same]
      · refine ⟨by rw [if_neg h]; exact ht, fun ρ => ?_⟩
        rw [if_neg h, evalT_var, evalT_var, Env.upd_other _ _ h]
  | .app r u, τ, ht => by
      obtain ⟨σ, hr, hu⟩ := hasType_app_inv ht
      obtain ⟨hr', er⟩ := subst_sound x s hs r _ hr
      obtain ⟨hu', eu⟩ := subst_sound x s hs u _ hu
      rw [subst_app]
      exact ⟨.app hr' hu', fun ρ => by rw [evalT_app hr' hu', evalT_app hr hu, er, eu]⟩
  | .lam v body, τ, ht => by
      obtain ⟨ρ', rfl, hb⟩ := hasType_lam_inv ht
      by_cases hvx : v = x
      · subst hvx
        rw [subst_lam_self]
        refine ⟨ht, fun ρ => ?_⟩
        rw [evalT_lam hb, evalT_lam hb]
        funext a
        rw [Env.upd_upd_same]
      · by_cases hvs : v ∈ freeVarOccurrences s
        · rw [subst_lam_capture _ _ hvx hvs]
          dsimp only
          -- the fresh binder `v'`
          let N := Nat.max (maxVarId body) (Nat.max (maxVarId s) x.id) + 1
          have hNb : (⟨N, v.ty⟩ : Var) ∉ allVars body := fun h => by
            have := allVar_id_le_maxVarId body _ h
            have : maxVarId body ≤ Nat.max (maxVarId body) (Nat.max (maxVarId s) x.id) :=
              Nat.le_max_left _ _
            dsimp only [N] at *; omega
          have hNs : (⟨N, v.ty⟩ : Var) ∉ freeVarOccurrences s := fun h => by
            have := freeVar_id_le_maxVarId s _ h
            have : maxVarId s ≤ Nat.max (maxVarId body) (Nat.max (maxVarId s) x.id) :=
              Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
            dsimp only [N] at *; omega
          have hNx : (⟨N, v.ty⟩ : Var) ≠ x := fun h => by
            have := congrArg Var.id h
            have : x.id ≤ Nat.max (maxVarId body) (Nat.max (maxVarId s) x.id) :=
              Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
            dsimp only [N] at *; omega
          have hb' : HasType (renameFreeVar body v ⟨N, v.ty⟩) ρ' :=
            (rename_hasType_iff (x := v) (y := ⟨N, v.ty⟩) rfl body ρ').2 hb
          obtain ⟨hsub, esub⟩ := subst_sound x s hs (renameFreeVar body v ⟨N, v.ty⟩) ρ' hb'
          refine ⟨.lam _ hsub, fun ρ => ?_⟩
          rw [show evalT (.arr v.ty ρ') (.lam ⟨N, v.ty⟩ (substTerm (renameFreeVar body v
              ⟨N, v.ty⟩) x s)) ρ = fun a => evalT ρ' (substTerm (renameFreeVar body v
              ⟨N, v.ty⟩) x s) (ρ.upd ⟨N, v.ty⟩ a) from evalT_lam (x := ⟨N, v.ty⟩) hsub ρ,
            evalT_lam hb]
          funext a
          rw [esub, evalT_coincide x.ty s (ρ := ρ.upd ⟨N, v.ty⟩ a) (ρ' := ρ) (fun w hw => by
              rw [Env.upd_other _ _ (fun e => hNs (by rw [← e]; exact hw))]),
            rename_eval N body hNb ρ' hb]
          apply evalT_coincide
          intro w hw
          have hwN : w ≠ ⟨N, v.ty⟩ := fun e => hNb (e ▸ fvo_subset_allVars body w hw)
          by_cases hwv : w = v
          · subst hwv
            rw [Env.upd_same, Env.upd_same, Env.upd_other _ _ hNx, Env.upd_same]
          · rw [Env.upd_other _ _ hwv, Env.upd_other _ _ hwv]
            by_cases hwx : w = x
            · subst hwx; rw [Env.upd_same, Env.upd_same]
            · rw [Env.upd_other _ _ hwx, Env.upd_other _ _ hwx, Env.upd_other _ _ hwN]
        · rw [subst_lam_fresh _ _ hvx hvs]
          obtain ⟨hsub, esub⟩ := subst_sound x s hs body ρ' hb
          refine ⟨.lam v hsub, fun ρ => ?_⟩
          rw [evalT_lam hsub, evalT_lam hb]
          funext a
          rw [esub, evalT_coincide x.ty s (ρ := ρ.upd v a) (ρ' := ρ) (fun w hw => by
              rw [Env.upd_other _ _ (fun e => hvs (by rw [← e]; exact hw))]),
            Env.upd_comm _ _ _ hvx]
termination_by t => rawSize t
decreasing_by
  all_goals simp_wf
  all_goals (simp only [rawSize, renameFreeVar_rawSize]; omega)

/-! ## α-equivalence and reduction -/

theorem alpha_sound {t t' : Term} (h : AlphaEq t t') :
    ∀ τ, (HasType t τ → HasType t' τ ∧ ∀ ρ, evalT τ t ρ = evalT τ t' ρ) ∧
      (HasType t' τ → HasType t τ ∧ ∀ ρ, evalT τ t ρ = evalT τ t' ρ) := by
  induction h with
  | refl t => exact fun τ => ⟨fun h => ⟨h, fun _ => rfl⟩, fun h => ⟨h, fun _ => rfl⟩⟩
  | symm _ ih =>
      intro τ
      exact ⟨fun h => let r := (ih τ).2 h; ⟨r.1, fun ρ => (r.2 ρ).symm⟩,
        fun h => let r := (ih τ).1 h; ⟨r.1, fun ρ => (r.2 ρ).symm⟩⟩
  | trans _ _ ih1 ih2 =>
      intro τ
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨h1, e1⟩ := (ih1 τ).1 h
        obtain ⟨h2, e2⟩ := (ih2 τ).1 h1
        exact ⟨h2, fun ρ => (e1 ρ).trans (e2 ρ)⟩
      · obtain ⟨h2, e2⟩ := (ih2 τ).2 h
        obtain ⟨h1, e1⟩ := (ih1 τ).2 h2
        exact ⟨h1, fun ρ => (e1 ρ).trans (e2 ρ)⟩
  | app _ _ iht ihs =>
      intro τ
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨σ, ht, hs⟩ := hasType_app_inv h
        obtain ⟨ht', et⟩ := (iht _).1 ht
        obtain ⟨hs', es⟩ := (ihs _).1 hs
        exact ⟨.app ht' hs', fun ρ => by rw [evalT_app ht hs, evalT_app ht' hs', et, es]⟩
      · obtain ⟨σ, ht', hs'⟩ := hasType_app_inv h
        obtain ⟨ht, et⟩ := (iht _).2 ht'
        obtain ⟨hs, es⟩ := (ihs _).2 hs'
        exact ⟨.app ht hs, fun ρ => by rw [evalT_app ht hs, evalT_app ht' hs', et, es]⟩
  | lam_congr x _ ih =>
      intro τ
      refine ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨ρ', rfl, hb⟩ := hasType_lam_inv h
        obtain ⟨hb', eb⟩ := (ih _).1 hb
        exact ⟨.lam x hb', fun ρ => by rw [evalT_lam hb, evalT_lam hb']; funext a; exact eb _⟩
      · obtain ⟨ρ', rfl, hb'⟩ := hasType_lam_inv h
        obtain ⟨hb, eb⟩ := (ih _).2 hb'
        exact ⟨.lam x hb, fun ρ => by rw [evalT_lam hb, evalT_lam hb']; funext a; exact eb _⟩
  | lam_rename x y t hty hy =>
      intro τ
      rcases hy with rfl | hy
      · rw [renameFreeVar_self]
        exact ⟨fun h => ⟨h, fun _ => rfl⟩, fun h => ⟨h, fun _ => rfl⟩⟩
      · obtain ⟨n, yty⟩ := y
        simp only at hty
        subst hty
        have key : ∀ ρ', HasType t ρ' → ∀ ρ,
            evalT (.arr x.ty ρ') (.lam x t) ρ =
              evalT (.arr x.ty ρ') (.lam ⟨n, x.ty⟩ (renameFreeVar t x ⟨n, x.ty⟩)) ρ := by
          intro ρ' hb ρ
          have hb' := (rename_hasType_iff (x := x) (y := ⟨n, x.ty⟩) rfl t ρ').2 hb
          rw [evalT_lam hb, show evalT (.arr x.ty ρ') (.lam ⟨n, x.ty⟩ (renameFreeVar t x
              ⟨n, x.ty⟩)) ρ = fun a => evalT ρ' (renameFreeVar t x ⟨n, x.ty⟩)
              (ρ.upd ⟨n, x.ty⟩ a) from evalT_lam (x := ⟨n, x.ty⟩) hb' ρ]
          funext a
          rw [rename_eval n t hy ρ' hb, Env.upd_same]
          apply evalT_coincide
          intro w hw
          have hwn : w ≠ ⟨n, x.ty⟩ := fun e => hy (e ▸ fvo_subset_allVars t w hw)
          by_cases hwx : w = x
          · subst hwx; rw [Env.upd_same, Env.upd_same]
          · rw [Env.upd_other _ _ hwx, Env.upd_other _ _ hwx, Env.upd_other _ _ hwn]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨ρ', rfl, hb⟩ := hasType_lam_inv h
          exact ⟨.lam _ ((rename_hasType_iff (x := x) (y := ⟨n, x.ty⟩) rfl t ρ').2 hb),
            key ρ' hb⟩
        · obtain ⟨ρ', hτ, hb'⟩ := hasType_lam_inv h
          subst hτ
          have hb := (rename_hasType_iff (x := x) (y := ⟨n, x.ty⟩) rfl t ρ').1 hb'
          exact ⟨.lam x hb, key ρ' hb⟩

/-- **Soundness of reduction**: typing and denotation are preserved. -/
theorem reduces_sound {t t' : Term} (h : ReducesTo t t') :
    ∀ τ, HasType t τ → HasType t' τ ∧ ∀ ρ, evalT τ t ρ = evalT τ t' ρ := by
  induction h with
  | beta x b s =>
      intro τ h
      obtain ⟨σ, hl, hs⟩ := hasType_app_inv h
      obtain ⟨ρ', hρ', hb⟩ := hasType_lam_inv hl
      injection hρ' with hσ hτ
      subst hσ; subst hτ
      obtain ⟨hsub, esub⟩ := subst_sound x s hs b _ hb
      exact ⟨hsub, fun ρ => by rw [evalT_app hl hs, evalT_lam hb, esub]⟩
  | app _ _ ih1 ih2 =>
      intro τ h
      obtain ⟨σ, ht, hs⟩ := hasType_app_inv h
      obtain ⟨ht', e1⟩ := ih1 _ ht
      obtain ⟨hs', e2⟩ := ih2 _ hs
      exact ⟨.app ht' hs', fun ρ => by rw [evalT_app ht hs, evalT_app ht' hs', e1, e2]⟩
  | lam x _ ih =>
      intro τ h
      obtain ⟨ρ', rfl, hb⟩ := hasType_lam_inv h
      obtain ⟨hb', eb⟩ := ih _ hb
      exact ⟨.lam x hb', fun ρ => by rw [evalT_lam hb, evalT_lam hb']; funext a; exact eb _⟩
  | refl_alpha h => exact fun τ ht => (alpha_sound h τ).1 ht
  | trans _ _ ih1 ih2 =>
      intro τ h
      obtain ⟨h1, e1⟩ := ih1 τ h
      obtain ⟨h2, e2⟩ := ih2 τ h1
      exact ⟨h2, fun ρ => (e1 ρ).trans (e2 ρ)⟩

end Schwichtenberg1976V2.Proofs
