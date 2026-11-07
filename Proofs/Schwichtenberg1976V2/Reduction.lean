import Proofs.Schwichtenberg1976V2.Basic

/-!
# Reduction toolkit: substitution, iteration and Church numerals

Equations for `substTerm`, `renameFreeVar` and `substMany` on the term shapes that occur
when Church numerals are applied, and the basic reductions:

* `n̄ t ⊳ λu. tⁿ u` for a binder `u` of type `0` that is not free in `t`;
* `(λy. α^Q y)ⁿ u ⊳ α^{n·Q} u`, the "bound" case;
* `(λy. α^Q w)^{n+1} u ⊳ α^Q w` for `w ≠ y`, the "constant" case.

Every substitution here is into a term without abstractions or into a closed numeral, so all
equations hold literally, not just up to α-equivalence.
-/

namespace Schwichtenberg1976V2.Proofs

open Schwichtenberg1976V2

/-! ## Reflexivity -/

theorem ReducesTo.rfl' (t : Term) : ReducesTo t t := .refl_alpha (.refl t)

/-! ## Equations for `substTerm` -/

theorem subst_var (v x : Var) (s : Term) :
    substTerm (.var v) x s = if v = x then s else .var v := by
  rw [substTerm]; simp

theorem subst_app (a b : Term) (x : Var) (s : Term) :
    substTerm (.app a b) x s = .app (substTerm a x s) (substTerm b x s) := by
  rw [substTerm]

theorem subst_lam_self (x : Var) (b s : Term) :
    substTerm (.lam x b) x s = .lam x b := by
  rw [substTerm]; simp

theorem subst_lam_fresh {v x : Var} (b s : Term) (hvx : v ≠ x)
    (hv : v ∉ freeVarOccurrences s) :
    substTerm (.lam v b) x s = .lam v (substTerm b x s) := by
  rw [substTerm]; simp [hvx, hv]

theorem subst_lam_capture {v x : Var} (b s : Term) (hvx : v ≠ x)
    (hv : v ∈ freeVarOccurrences s) :
    substTerm (.lam v b) x s =
      let v' : Var := ⟨Nat.max (maxVarId b) (Nat.max (maxVarId s) x.id) + 1, v.ty⟩
      .lam v' (substTerm (renameFreeVar b v v') x s) := by
  rw [substTerm]; simp [hvx, hv]

/-- Substituting into a term in which `x` is not free, with a closed term, changes nothing. -/
theorem subst_closed_of_not_mem {s : Term} (hs : freeVarOccurrences s = []) :
    ∀ (t : Term) (x : Var), x ∉ freeVarOccurrences t → substTerm t x s = t := by
  intro t
  induction t with
  | var v =>
      intro x hx
      rw [subst_var]
      have : v ≠ x := by intro h; subst h; simp at hx
      simp [this]
  | app a b iha ihb =>
      intro x hx
      simp only [mem_fvo_app, not_or] at hx
      rw [subst_app, iha x hx.1, ihb x hx.2]
  | lam v b ih =>
      intro x hx
      by_cases hvx : v = x
      · subst hvx; exact subst_lam_self _ _ _
      · rw [subst_lam_fresh b s hvx (by simp [hs]), ih x]
        intro hxb
        exact hx ((mem_fvo_lam v b x).2 ⟨hxb, fun h => hvx h.symm⟩)

/-! ## Iterated application -/

theorem iterApp_succ (a b : Term) (n : Nat) :
    iterApp a b (n + 1) = .app a (iterApp a b n) := rfl

theorem iterApp_add (a b : Term) (m : Nat) :
    ∀ n, iterApp a (iterApp a b m) n = iterApp a b (n + m) := by
  intro n
  induction n with
  | zero => simp [iterApp]
  | succ n ih =>
      rw [iterApp_succ, ih, show n + 1 + m = (n + m) + 1 by omega, iterApp_succ]

theorem subst_iterApp (a b : Term) (x : Var) (s : Term) :
    ∀ n, substTerm (iterApp a b n) x s = iterApp (substTerm a x s) (substTerm b x s) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [iterApp_succ, subst_app, ih, iterApp_succ]

theorem mem_fvo_iterApp (a b : Term) (v : Var) :
    ∀ n, v ∈ freeVarOccurrences (iterApp a b n) ↔
      (0 < n ∧ v ∈ freeVarOccurrences a) ∨ v ∈ freeVarOccurrences b := by
  intro n
  induction n with
  | zero => simp [iterApp]
  | succ n ih =>
      rw [iterApp_succ, mem_fvo_app, ih]
      constructor
      · rintro (h | ⟨_, h⟩ | h)
        · exact Or.inl ⟨by omega, h⟩
        · exact Or.inl ⟨by omega, h⟩
        · exact Or.inr h
      · rintro (⟨_, h⟩ | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem allVars_iterApp_var (a b : Var) (v : Var) :
    ∀ n, v ∈ allVars (iterApp (.var a) (.var b) n) → v = a ∨ v = b := by
  intro n
  induction n with
  | zero => simp only [iterApp, allVars, List.mem_singleton]; exact Or.inr
  | succ n ih =>
      intro h
      rw [iterApp_succ] at h
      simp only [allVars, List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · exact Or.inl h
      · exact ih h

theorem rename_iterApp_var {a b : Var} (c : Var) (hab : a ≠ b) :
    ∀ n, renameFreeVar (iterApp (.var a) (.var b) n) b c = iterApp (.var a) (.var c) n := by
  intro n
  induction n with
  | zero => simp [iterApp, renameFreeVar]
  | succ n ih =>
      rw [iterApp_succ, iterApp_succ, renameFreeVar, ih]
      simp [renameFreeVar, hab]

/-- `(λu. a^m u)` and `(λz. a^m z)` are α-equivalent. -/
theorem alpha_lam_iterApp {a u z : Var} (m : Nat) (hty : u.ty = z.ty)
    (hau : a ≠ u) (haz : a ≠ z) :
    AlphaEq (.lam u (iterApp (.var a) (.var u) m)) (.lam z (iterApp (.var a) (.var z) m)) := by
  have h := AlphaEq.lam_rename u z (iterApp (.var a) (.var u) m) hty (by
    by_cases hzu : z = u
    · exact Or.inl hzu
    · refine Or.inr fun hz => ?_
      rcases allVars_iterApp_var a u z m hz with h | h
      · exact haz h.symm
      · exact hzu h)
  rwa [rename_iterApp_var z hau] at h

/-! ## Church numerals -/

/-- The variables used inside `churchNumeral`. -/
def numα : Var := ⟨1, Ty.endo⟩
def numx : Var := ⟨0, .zero⟩

theorem churchNumeral_eq (n : Nat) :
    churchNumeral n = .lam numα (.lam numx (iterApp (.var numα) (.var numx) n)) := rfl

theorem fvo_churchNumeral (n : Nat) : freeVarOccurrences (churchNumeral n) = [] := by
  rw [churchNumeral_eq]
  refine eq_nil_of_forall_not_mem fun v hv => ?_
  simp only [mem_fvo_lam, mem_fvo_iterApp, mem_fvo_var] at hv
  obtain ⟨⟨h | h, hx⟩, hα⟩ := hv
  · exact hα h.2
  · exact hx h

/-- Applying a Church numeral: `n̄ t ⊳ λu. tⁿ u` with `u : 0` not free in `t`. -/
theorem numeral_app (n : Nat) (t : Term) :
    ∃ u : Var, u.ty = .zero ∧ u ∉ freeVarOccurrences t ∧
      ReducesTo (.app (churchNumeral n) t) (.lam u (iterApp t (.var u) n)) := by
  have hβ := ReducesTo.beta numα (.lam numx (iterApp (.var numα) (.var numx) n)) t
  rw [← churchNumeral_eq] at hβ
  have hxα : numx ≠ numα := by decide
  have hαx : numα ≠ numx := by decide
  by_cases hx : numx ∈ freeVarOccurrences t
  · rw [subst_lam_capture _ _ hxα hx] at hβ
    dsimp only at hβ
    have hne : ∀ m : Nat, numα ≠ (⟨m, numx.ty⟩ : Var) := by
      intro m h
      have := congrArg Var.ty h
      simp [numα, numx, Ty.endo] at this
    rw [rename_iterApp_var _ hαx, subst_iterApp, subst_var, if_pos rfl, subst_var,
      if_neg (fun h => hne _ h.symm)] at hβ
    refine ⟨_, rfl, ?_, hβ⟩
    intro hut
    have hle := freeVar_id_le_maxVarId t _ hut
    have h1 : maxVarId t ≤ Nat.max (maxVarId (iterApp (.var numα) (.var numx) n))
        (Nat.max (maxVarId t) numα.id) :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    dsimp only at hle
    omega
  · rw [subst_lam_fresh _ _ hxα hx, subst_iterApp] at hβ
    rw [subst_var, if_pos rfl, subst_var, if_neg hxα] at hβ
    exact ⟨numx, rfl, hx, hβ⟩

/-! ## Iterating `λy. α^Q y` and `λy. α^Q w` -/

/-- Bound case: `(λy. a^Q y)ⁿ u ⊳ a^{n·Q} u`. -/
theorem iter_bound {a y : Var} (Q : Nat) (hay : a ≠ y) (u : Term) :
    ∀ n, ReducesTo (iterApp (.lam y (iterApp (.var a) (.var y) Q)) u n)
      (iterApp (.var a) u (n * Q)) := by
  intro n
  induction n with
  | zero => simpa [iterApp] using ReducesTo.rfl' u
  | succ n ih =>
      rw [iterApp_succ]
      refine .trans (.app (ReducesTo.rfl' _) ih) ?_
      have hβ := ReducesTo.beta y (iterApp (.var a) (.var y) Q) (iterApp (.var a) u (n * Q))
      rw [subst_iterApp, subst_var, if_neg hay, subst_var, if_pos rfl, iterApp_add] at hβ
      rwa [Nat.succ_mul, Nat.add_comm (n * Q)]

/-- Constant case: `(λy. a^Q w)^{n+1} u ⊳ a^Q w` when `w ≠ y`. -/
theorem iter_const {a y w : Var} (Q : Nat) (hay : a ≠ y) (hwy : w ≠ y) (u : Term) (n : Nat) :
    ReducesTo (iterApp (.lam y (iterApp (.var a) (.var w) Q)) u (n + 1))
      (iterApp (.var a) (.var w) Q) := by
  rw [iterApp_succ]
  have hβ := ReducesTo.beta y (iterApp (.var a) (.var w) Q)
    (iterApp (.lam y (iterApp (.var a) (.var w) Q)) u n)
  rwa [subst_iterApp, subst_var, if_neg hay, subst_var, if_neg hwy] at hβ

/-! ## Sequential substitution of closed terms -/

theorem substMany_app (a b : Term) :
    ∀ l : List (Var × Term),
      substMany (.app a b) l = .app (substMany a l) (substMany b l) := by
  intro l
  induction l generalizing a b with
  | nil => rfl
  | cons p l ih => obtain ⟨x, s⟩ := p; simp only [substMany]; rw [subst_app, ih]

/-- A binder that is not a key passes through a substitution of closed terms. -/
theorem substMany_lam (y : Var) (b : Term) :
    ∀ l : List (Var × Term), (∀ p ∈ l, p.1 ≠ y ∧ freeVarOccurrences p.2 = []) →
      substMany (.lam y b) l = .lam y (substMany b l) := by
  intro l
  induction l generalizing b with
  | nil => intro _; rfl
  | cons p l ih =>
      obtain ⟨x, s⟩ := p
      intro hl
      obtain ⟨hxy, hs⟩ := hl (x, s) (by simp)
      simp only [substMany]
      rw [subst_lam_fresh b s (fun h => hxy h.symm) (by simp [hs])]
      exact ih _ (fun p hp => hl p (by simp [hp]))

theorem substMany_var_of_not_key (x : Var) :
    ∀ l : List (Var × Term), (∀ p ∈ l, p.1 ≠ x) → substMany (.var x) l = .var x := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p l ih =>
      obtain ⟨y, s⟩ := p
      intro hl
      have hyx : y ≠ x := hl (y, s) (by simp)
      simp only [substMany]
      rw [subst_var, if_neg (fun h => hyx h.symm)]
      exact ih (fun p hp => hl p (by simp [hp]))

theorem substMany_closed {t : Term} (ht : freeVarOccurrences t = []) :
    ∀ l : List (Var × Term), (∀ p ∈ l, freeVarOccurrences p.2 = []) → substMany t l = t := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p l ih =>
      obtain ⟨y, s⟩ := p
      intro hl
      simp only [substMany]
      rw [subst_closed_of_not_mem (hl (y, s) (by simp)) t y (by simp [ht])]
      exact ih (fun p hp => hl p (by simp [hp]))

/-- Looking up an injectively indexed key in a substitution of closed terms. -/
theorem substMany_var_index {k : Nat} (Fs : Fin k → Var) (hinj : Function.Injective Fs)
    (N : Fin k → Term) (hN : ∀ j, freeVarOccurrences (N j) = []) (i : Fin k) :
    ∀ L : List (Fin k),
      substMany (.var (Fs i)) (L.map fun j => (Fs j, N j)) =
        if i ∈ L then N i else .var (Fs i) := by
  intro L
  induction L with
  | nil => simp [substMany]
  | cons j L ih =>
      simp only [List.map_cons, substMany]
      rw [subst_var]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl, substMany_closed (hN i) _ (by simp [hN]), if_pos (by simp)]
      · rw [if_neg (fun h => hij (hinj h)), ih]
        simp [hij]

end Schwichtenberg1976V2.Proofs
