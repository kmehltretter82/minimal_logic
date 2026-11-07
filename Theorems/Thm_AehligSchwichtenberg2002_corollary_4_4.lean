import Definitions.Def_AehligSchwichtenberg2002_Bounds

namespace AehligSchwichtenberg2002

theorem corollary_4_4 {τ : Ty} {f l w : Term} {n : Nat}
    (hf : HasType [] f (.lolli (.list τ) (.list τ)))
    (hl : IsCanonicalListInput τ l n)
    (hred : RedStar (.app f l) w)
    (hnorm : IsNormal w) :
    ∃ m : Nat, listEntryCount w = some m ∧ m ≤ n := by sorry

end AehligSchwichtenberg2002
