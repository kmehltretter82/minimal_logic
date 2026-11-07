import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Theorem 5.1 (Bounding)** (Section 5, p. 26):
Let `t` be a closed `RA`-term of type `σ₁ → ⋯ → σₖ → τ`, where `σ₁, ..., σₖ, τ` are all
ground types. Then there exists a polynomial `p_t : Nat → Nat` (`IsUnivariatePoly p_t`)
such that for all numerals `n₁, ..., nₖ` of types `σ₁, ..., σₖ` respectively, there exists
a closed `R`-free `RS`-term `u` of type `τ` equivalent to `t n₁ ... nₖ` of length
`|u| ≤ p_t(∑ |nᵢ|)` whose numeral normal form `nf(t n⃗) = nf(u)` is computed by `NFEval`
in at most `p_t(∑ |nᵢ|)` steps using registers of size at most `p_t(∑ |nᵢ|)`. -/
theorem theorem_5_1
    (k : Nat) (σs : Fin k → Ty) (τ : Ty) (t : Term)
    (ht : IsRATerm t)
    (hclosed : IsClosed t)
    (hty : HasType t (Ty.arrMany (List.ofFn σs) τ))
    (hσs : ∀ i : Fin k, (σs i).isGround = true)
    (hτ : τ.isGround = true) :
    ∃ p_t : Nat → Nat,
      IsUnivariatePoly p_t ∧
      ∀ ns : Fin k → Term,
        (∀ i : Fin k, HasType (ns i) (σs i) ∧ isNumeral (ns i) = true) →
        let m := (List.finRange k).foldr (fun i acc => termLength (ns i) + acc) 0
        ∃ (u nf_val : Term) (steps regs maxLen : Nat),
          IsRSTerm u ∧
          isRFree u = true ∧
          IsClosed u ∧
          HasType u τ ∧
          TermEquiv u (Term.appMany t (List.ofFn ns)) ∧
          NFEval u [] nf_val steps regs maxLen ∧
          IsNormalFormOf (Term.appMany t (List.ofFn ns)) nf_val ∧
          isNumeral nf_val = true ∧
          termLength u ≤ p_t m ∧
          steps ≤ p_t m ∧
          regs ≤ p_t m ∧
          maxLen ≤ p_t m := by
  sorry

end BNS2000
