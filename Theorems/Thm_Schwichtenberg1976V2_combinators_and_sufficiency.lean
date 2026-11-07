import Definitions.Def_Schwichtenberg1976V2_Lambda

namespace Schwichtenberg1976V2

/-- First part of Schwichtenberg's characterization (pp. 113–114):
1. Every closed β-normal term of type `ν = (0 → 0) → (0 → 0)` is α-equivalent to a
   Church numeral `n̄` or the identity `λα. α`.
2. `addComb`, `mulComb`, `constComb c`, and `condComb` define addition, multiplication,
   the unary constant `c`, and the conditional `d(n, m, i)` on Church numerals.
3. Every function in the inductive class of extended polynomials (`IsExtendedPolyInd`)
   is λ-definable over `ν`. -/
theorem combinators_and_sufficiency :
    (∀ t : Term,
      HasType t Ty.nu →
      IsClosed t →
      IsBetaNormal t →
      (∃ n : Nat, AlphaEq t (churchNumeral n)) ∨
      (∃ α : Var, α.ty = Ty.endo ∧ AlphaEq t (.lam α (.var α)))) ∧
    DefinesFunction 2 addComb (fun v => v ⟨0, by decide⟩ + v ⟨1, by decide⟩) ∧
    DefinesFunction 2 mulComb (fun v => v ⟨0, by decide⟩ * v ⟨1, by decide⟩) ∧
    (∀ c : Nat, DefinesFunction 1 (constComb c) (fun _ => c)) ∧
    DefinesFunction 3 condComb
      (fun v => condNat (v ⟨0, by decide⟩) (v ⟨1, by decide⟩) (v ⟨2, by decide⟩)) ∧
    (∀ {k : Nat} {f : (Fin k → Nat) → Nat},
      IsExtendedPolyInd f → IsLambdaDefinable k f) := by
  sorry

end Schwichtenberg1976V2
