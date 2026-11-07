import Definitions.Def_Schwichtenberg1976V2_Lambda

namespace Schwichtenberg1976V2

/-- Inductive lemma on clauses (1)–(3) (p. 114, lines 14–22):
For every `s` satisfying `IsType00Subterm (List.ofFn Fs) α s`, either `s = .var α`, or
there exist a multivariate polynomial `P : (Fin k → Nat) → Nat` (`IsPolynomial P`) and
a variable `z` of type `0` (either bound by the outer `λy` or free in `s`) such that for
all positive inputs `v : Fin k → Nat` (`∀ i, v i ≠ 0`), substituting `Fᵢ ↦ v(i)̄` into `s`
reduces to `λy. α^{P(v)} z` (which is `α^{P(v)}` when `z = y`). -/
theorem subterm_polynomial_lemma
    (k : Nat) (Fs : Fin k → Var) (α : Var)
    (hFs_ty : ∀ i : Fin k, (Fs i).ty = Ty.nu)
    (hFs_inj : Function.Injective Fs)
    (hα_ty : α.ty = Ty.endo)
    (s : Term)
    (hs : IsType00Subterm (List.ofFn Fs) α s) :
    s = .var α ∨
    ∃ (P : (Fin k → Nat) → Nat) (z : Var),
      IsPolynomial P ∧
      z.ty = .zero ∧
      ∀ v : Fin k → Nat,
        (∀ i : Fin k, v i ≠ 0) →
        ∃ y : Var,
          y.ty = .zero ∧
          (z = y ∨ z ∈ freeVars s) ∧
          ReducesTo
            (substMany s ((List.finRange k).map (fun i => (Fs i, churchNumeral (v i)))))
            (.lam y (iterApp (.var α) (.var z) (P v))) := by
  sorry

end Schwichtenberg1976V2
