import Proofs.Schwichtenberg1976V2.NormalSubterms
import Proofs.Schwichtenberg1976V2.Reduction

/-!
# Closed normal numerals and the basic combinators (p. 113)

* Every closed β-normal term of type `ν` is α-equivalent to a Church numeral `n̄` or to the
  identity `λα. α`.
* `addComb`, `mulComb`, `constComb c` and `condComb` define `+`, `·`, the constant `c`, and
  the conditional `d(n, m, i)`.
-/

namespace Schwichtenberg1976V2.Proofs

open Schwichtenberg1976V2

/-! ## Substitution of closed terms -/

theorem subst_lam_closed {s : Term} (hs : freeVarOccurrences s = []) (v x : Var) (b : Term) :
    substTerm (.lam v b) x s = if v = x then .lam v b else .lam v (substTerm b x s) := by
  by_cases h : v = x
  · subst h; rw [subst_lam_self, if_pos rfl]
  · rw [subst_lam_fresh b s h (by simp [hs]), if_neg h]

/-- `n̄ a s ⊳ aⁿ s`. -/
theorem numeral_app_app (n : Nat) (a : Var) (s : Term) :
    ReducesTo (.app (.app (churchNumeral n) (.var a)) s) (iterApp (.var a) s n) := by
  obtain ⟨u, _, hu, hr⟩ := numeral_app n (.var a)
  refine .trans (.app hr (ReducesTo.rfl' s)) ?_
  have hβ := ReducesTo.beta u (iterApp (.var a) (.var u) n) s
  have hau : a ≠ u := fun h => hu (by simp [h])
  rwa [subst_iterApp, subst_var, if_neg hau, subst_var, if_pos rfl] at hβ

theorem var_ne_of_ty' {a b : Var} (h : a.ty ≠ b.ty) : a ≠ b := fun e => h (e ▸ rfl)

theorem rename_iterApp_head {a b : Var} (c : Var) (hba : b ≠ a) :
    ∀ n, renameFreeVar (iterApp (.var a) (.var b) n) a c = iterApp (.var c) (.var b) n := by
  intro n
  induction n with
  | zero => simp [iterApp, renameFreeVar, hba]
  | succ n ih =>
      rw [iterApp_succ, iterApp_succ, renameFreeVar, ih]
      simp [renameFreeVar]

/-! ## Closed normal terms of type `ν` -/

theorem chain_nil_shape {a z : Var} {body : Term} (h : IsBasicType00Chain [] a z body) :
    ∃ q, body = iterApp (.var a) (.var z) q := by
  induction body generalizing z with
  | var v =>
      cases h with
      | base _ _ => exact ⟨0, rfl⟩
  | app s₁ rest _ ih =>
      cases h with
      | step hb hc =>
          obtain ⟨q, rfl⟩ := ih hc
          cases hb with
          | alpha => exact ⟨q + 1, rfl⟩
          | appF hF _ => simp at hF
  | lam _ _ _ => cases h

theorem fvo_nil_of_closed {t : Term} (h : IsClosed t) : freeVarOccurrences t = [] := by
  refine eq_nil_of_forall_not_mem fun v hv => ?_
  have := (mem_freeVars_iff t v).2 hv
  rw [IsClosed] at h
  rw [h] at this
  simp at this

theorem closed_normal_nu (t : Term) (hty : HasType t Ty.nu) (hcl : IsClosed t)
    (hn : IsBetaNormal t) :
    (∃ n : Nat, AlphaEq t (churchNumeral n)) ∨
    (∃ α : Var, α.ty = Ty.endo ∧ AlphaEq t (.lam α (.var α))) := by
  have hfv := fvo_nil_of_closed hcl
  cases t with
  | var v => simp [freeVarOccurrences] at hfv
  | app p q =>
      exfalso
      rcases neutral_shape (Fs := []) (α := numα) (by simp) rfl (.app p q) _ hn
          (fun _ _ h => Term.noConfusion h) hty (by simp [hfv]) with ⟨_, F, hF, _⟩ | h | h
      · simp at hF
      · exact ty_nu_ne_endo h
      · exact ty_nu_ne_zero h
  | lam a b =>
      obtain ⟨ρ, hρ, hb⟩ := hasType_lam_inv hty
      simp only [Ty.nu] at hρ
      injection hρ with ha hρ
      subst hρ
      have hfvb : ∀ v ∈ freeVarOccurrences b, v = a := by
        intro v hv
        refine Decidable.byContradiction fun hva => ?_
        have : v ∈ freeVarOccurrences (.lam a b) := (mem_fvo_lam a b v).2 ⟨hv, hva⟩
        rw [hfv] at this
        simp at this
      have hgood : Good [] a b Ty.endo :=
        ⟨isBetaNormal_lam hn, hb, fun v hv => Or.inr (Or.inl (hfvb v hv)),
          Or.inr (Or.inl rfl)⟩
      have h00 := (good_shape (Fs := []) (α := a) (by simp) ha.symm b _ hgood).1 rfl
      cases h00 with
      | basic hb0 =>
          cases hb0 with
          | alpha => exact Or.inr ⟨a, ha.symm, .refl _⟩
          | appF hF _ => simp at hF
      | chainLam y z hy hz hc =>
          obtain ⟨q, rfl⟩ := chain_nil_shape hc
          have hza : z ≠ a := fun h => by rw [h, ← ha] at hz; cases hz
          have hzy : z = y := by
            refine Decidable.byContradiction fun hzy => ?_
            have hz' : z ∈ freeVarOccurrences (.lam y (iterApp (.var a) (.var z) q)) :=
              (mem_fvo_lam _ _ _).2 ⟨(mem_fvo_iterApp _ _ _ _).2 (Or.inr (by simp)), hzy⟩
            exact hza (hfvb z hz')
          subst hzy
          refine Or.inl ⟨q, ?_⟩
          have hαz : numα ≠ z := fun h => by rw [← h] at hz; cases hz
          have h1 := AlphaEq.lam_rename a numα (.lam z (iterApp (.var a) (.var z) q))
            (by rw [← ha]; rfl) (by
              by_cases hαa : numα = a
              · exact Or.inl hαa
              · refine Or.inr fun hm => ?_
                simp only [allVars, List.mem_cons] at hm
                rcases hm with h | h
                · exact hαz h
                · rcases allVars_iterApp_var a z numα q h with h | h
                  · exact hαa h
                  · exact hαz h)
          have hza' : (z == a) = false := by simp [hza]
          simp only [renameFreeVar, hza'] at h1
          rw [rename_iterApp_head numα hza] at h1
          refine .trans h1 (.lam_congr numα ?_)
          exact alpha_lam_iterApp q hz hαz (by decide)

/-! ## The combinators -/

def vF : Var := ⟨3, Ty.nu⟩
def vG : Var := ⟨4, Ty.nu⟩
def vH : Var := ⟨5, Ty.nu⟩
def vy : Var := ⟨2, .zero⟩

theorem addComb_eq : addComb = .lam vF (.lam vG (.lam numα (.lam numx
    (.app (.app (.var vF) (.var numα)) (.app (.app (.var vG) (.var numα)) (.var numx)))))) := by
  decide

theorem mulComb_eq : mulComb = .lam vF (.lam vG (.lam numα
    (.app (.var vF) (.app (.var vG) (.var numα))))) := by
  decide

theorem constComb_eq (c : Nat) : constComb c = .lam vF (churchNumeral c) := by
  simp only [constComb, iterTerm, freshVarFor, churchNumeral]
  rfl

theorem condComb_eq : condComb = .lam vF (.lam vG (.lam vH (.lam numα (.lam numx
    (.app (.app (.var vH) (.lam vy (.app (.app (.var vG) (.var numα)) (.var numx))))
      (.app (.app (.var vF) (.var numα)) (.var numx))))))) := rfl

theorem subst_numeral {s : Term} (hs : freeVarOccurrences s = []) (n : Nat) (x : Var) :
    substTerm (churchNumeral n) x s = churchNumeral n :=
  subst_closed_of_not_mem hs _ x (by simp [fvo_churchNumeral])

theorem closed_of_fvo_nil {t : Term} (h : freeVarOccurrences t = []) : IsClosed t := by
  unfold IsClosed freeVars
  rw [h]
  rfl

theorem iterApp_hasType {a : Var} {b : Term} (ha : a.ty = Ty.endo) (hb : HasType b .zero) :
    ∀ n, HasType (iterApp (.var a) b n) .zero := by
  intro n
  induction n with
  | zero => exact hb
  | succ n ih =>
      have h : HasType (.var a) (.arr .zero .zero) := by
        have := HasType.var a
        rw [ha] at this
        exact this
      exact .app h ih

theorem numeral_hasType (n : Nat) : HasType (churchNumeral n) Ty.nu :=
  .lam numα (.lam numx (iterApp_hasType rfl (.var numx) n))

theorem ne_αx : numα ≠ numx := by decide
theorem ne_xα : numx ≠ numα := by decide

/-- `λα x. n̄ α (m̄ α x) ⊳ (n+m)‾`. -/
theorem add_body_reduces (n m : Nat) :
    ReducesTo (.lam numα (.lam numx (.app (.app (churchNumeral n) (.var numα))
        (.app (.app (churchNumeral m) (.var numα)) (.var numx)))))
      (churchNumeral (n + m)) := by
  rw [churchNumeral_eq (n + m)]
  refine .lam numα (.lam numx (.trans (.app (ReducesTo.rfl' _)
    (numeral_app_app m numα (.var numx))) ?_))
  have := numeral_app_app n numα (iterApp (.var numα) (.var numx) m)
  rwa [iterApp_add] at this

theorem addComb_reduces (n m : Nat) :
    ReducesTo (.app (.app addComb (churchNumeral n)) (churchNumeral m))
      (churchNumeral (n + m)) := by
  rw [addComb_eq]
  refine .trans (.app (.beta _ _ _) (ReducesTo.rfl' _)) ?_
  simp (config := { decide := true }) only [subst_lam_closed (fvo_churchNumeral _),
    subst_app, subst_var, if_true, if_false]
  refine .trans (.beta _ _ _) ?_
  simp (config := { decide := true }) only [subst_lam_closed (fvo_churchNumeral _),
    subst_app, subst_var, subst_numeral (fvo_churchNumeral _), if_true, if_false]
  exact add_body_reduces n m

theorem addComb_defines :
    DefinesFunction 2 addComb (fun v => v ⟨0, by decide⟩ + v ⟨1, by decide⟩) := by
  refine ⟨?_, by unfold IsClosed; decide, fun v => addComb_reduces _ _⟩
  rw [addComb_eq]
  exact .lam _ (.lam _ (.lam _ (.lam _
    (.app (.app (.var _) (.var _)) (.app (.app (.var _) (.var _)) (.var _))))))

theorem mulComb_reduces (n m : Nat) :
    ReducesTo (.app (.app mulComb (churchNumeral n)) (churchNumeral m))
      (churchNumeral (n * m)) := by
  rw [mulComb_eq]
  refine .trans (.app (.beta _ _ _) (ReducesTo.rfl' _)) ?_
  simp (config := { decide := true }) only [subst_lam_closed (fvo_churchNumeral _),
    subst_app, subst_var, if_true, if_false]
  refine .trans (.beta _ _ _) ?_
  simp (config := { decide := true }) only [subst_lam_closed (fvo_churchNumeral _),
    subst_app, subst_var, subst_numeral (fvo_churchNumeral _), if_true, if_false]
  rw [churchNumeral_eq (n * m)]
  obtain ⟨u, hu, _, hr1⟩ := numeral_app m (.var numα)
  obtain ⟨w, hw, _, hr2⟩ := numeral_app n (.lam u (iterApp (.var numα) (.var u) m))
  have hαu : numα ≠ u := var_ne_of_ty' (by rw [hu]; decide)
  refine .lam numα (.trans (.app (ReducesTo.rfl' _) hr1) (.trans hr2 ?_))
  refine .trans (.lam w (iter_bound m hαu (.var w) n)) (.refl_alpha ?_)
  exact alpha_lam_iterApp _ hw (var_ne_of_ty' (by rw [hw]; decide)) ne_αx

theorem mulComb_defines :
    DefinesFunction 2 mulComb (fun v => v ⟨0, by decide⟩ * v ⟨1, by decide⟩) := by
  refine ⟨?_, by unfold IsClosed; decide, fun v => mulComb_reduces _ _⟩
  rw [mulComb_eq]
  exact .lam _ (.lam _ (.lam _ (.app (.var _) (.app (.var _) (.var _)))))

theorem constComb_defines (c : Nat) : DefinesFunction 1 (constComb c) (fun _ => c) := by
  rw [constComb_eq]
  refine ⟨.lam vF (numeral_hasType c), closed_of_fvo_nil ?_, fun v => ?_⟩
  · simp [freeVarOccurrences, fvo_churchNumeral]
  · show ReducesTo (.app (.lam vF (churchNumeral c)) (churchNumeral (v ⟨0, by decide⟩))) _
    refine .trans (.beta _ _ _) ?_
    rw [subst_numeral (fvo_churchNumeral _)]
    exact ReducesTo.rfl' _

theorem condComb_reduces (n m i : Nat) :
    ReducesTo (.app (.app (.app condComb (churchNumeral n)) (churchNumeral m)) (churchNumeral i))
      (churchNumeral (condNat n m i)) := by
  rw [condComb_eq]
  refine .trans (.app (.app (.beta _ _ _) (ReducesTo.rfl' _)) (ReducesTo.rfl' _)) ?_
  simp (config := { decide := true }) only [subst_lam_closed (fvo_churchNumeral _),
    subst_app, subst_var, if_true, if_false]
  refine .trans (.app (.beta _ _ _) (ReducesTo.rfl' _)) ?_
  simp (config := { decide := true }) only [subst_lam_closed (fvo_churchNumeral _),
    subst_app, subst_var, subst_numeral (fvo_churchNumeral _), if_true, if_false]
  refine .trans (.beta _ _ _) ?_
  simp (config := { decide := true }) only [subst_lam_closed (fvo_churchNumeral _),
    subst_app, subst_var, subst_numeral (fvo_churchNumeral _), if_true, if_false]
  -- reduce the two inner numeral applications
  have hcong := ReducesTo.app (.app (ReducesTo.rfl' (churchNumeral i))
      (.lam vy (numeral_app_app m numα (.var numx))))
    (numeral_app_app n numα (.var numx))
  obtain ⟨u, hu, hufree, hr⟩ := numeral_app i (.lam vy (iterApp (.var numα) (.var numx) m))
  have hαu : numα ≠ u := var_ne_of_ty' (by rw [hu]; decide)
  have hxu : numx ≠ u := by
    intro h
    apply hufree
    rw [← h]
    exact (mem_fvo_lam _ _ _).2 ⟨(mem_fvo_iterApp _ _ _ _).2 (Or.inr (by simp)), by decide⟩
  rw [churchNumeral_eq]
  refine .lam numα (.lam numx (.trans hcong (.trans (.app hr (ReducesTo.rfl' _)) ?_)))
  cases i with
  | zero =>
      have hβ := ReducesTo.beta u (.var u) (iterApp (.var numα) (.var numx) n)
      rw [subst_var, if_pos rfl] at hβ
      exact hβ
  | succ j =>
      refine .trans (.app (.lam u (iter_const m (by decide) (by decide) (.var u) j))
        (ReducesTo.rfl' _)) ?_
      have hβ := ReducesTo.beta u (iterApp (.var numα) (.var numx) m)
        (iterApp (.var numα) (.var numx) n)
      rw [subst_iterApp, subst_var, if_neg hαu, subst_var, if_neg hxu] at hβ
      exact hβ

theorem condComb_defines :
    DefinesFunction 3 condComb
      (fun v => condNat (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) (v ⟨2, by decide⟩)) := by
  refine ⟨?_, by unfold IsClosed; decide, fun v => condComb_reduces _ _ _⟩
  rw [condComb_eq]
  exact .lam _ (.lam _ (.lam _ (.lam _ (.lam _
    (.app (.app (.var _) (.lam _ (.app (.app (.var _) (.var _)) (.var _))))
      (.app (.app (.var _) (.var _)) (.var _)))))))

end Schwichtenberg1976V2.Proofs
