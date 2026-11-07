import Definitions.Def_AehligSchwichtenberg2002_Bounds

namespace AehligSchwichtenberg2002

theorem corollary_4_9 {k : Nat} {t : Term}
    (ht : HasType [] t (Ty.lolliMany (List.replicate k Ty.bin) Ty.bin)) :
    ∃ B : Nat → Nat,
      IsPolyBoundedOfDegree B (Nat.max (braceDepth t) 1) ∧
      ∀ (Γ : Context) (ls : List Term) (ns : List Nat),
        ls.length = k →
        ValidBinListInputs Γ ls ns →
        ∃ (steps m : Nat) (w : Term),
          RedSteps steps (Term.appMany t ls) w ∧
          IsNormal w ∧
          listEntryCount w = some m ∧
          m ≤ sumListLengths ns ∧
          steps ≤ B (sumListLengths ns) := by sorry

end AehligSchwichtenberg2002
