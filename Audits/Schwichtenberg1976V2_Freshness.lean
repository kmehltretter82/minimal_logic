import Definitions.Def_Schwichtenberg1976V2_Lambda

namespace Schwichtenberg1976V2.Audit

/-- Every free variable identifier is bounded by the maximum identifier of the term. -/
theorem freeVar_id_le_maxVarId (t : Term) (v : Var)
    (h : v ∈ freeVarOccurrences t) : v.id ≤ maxVarId t := by
  induction t with
  | var x =>
      simp [freeVarOccurrences, maxVarId] at h ⊢
      subst h
      exact Nat.le_refl _
  | app r s ihr ihs =>
      simp [freeVarOccurrences, maxVarId, Nat.max_def] at h ⊢
      rcases h with hr | hs
      · have := ihr hr; split <;> omega
      · have := ihs hs; split <;> omega
  | lam x r ih =>
      simp [freeVarOccurrences, maxVarId, Nat.max_def] at h ⊢
      have := ih h.1; split <;> omega

/-- The binder selected by `freshVarFor` always has the requested type `τ`. -/
theorem freshVarFor_ty (τ : Ty) (preferred : Nat) (t : Term) :
    (freshVarFor τ preferred t).ty = τ := by
  dsimp [freshVarFor]
  split <;> rfl

/-- The binder selected by `freshVarFor` is never free in `t`. -/
theorem freshVarFor_not_mem_freeVarOccurrences (τ : Ty) (preferred : Nat) (t : Term) :
    freshVarFor τ preferred t ∉ freeVarOccurrences t := by
  dsimp [freshVarFor]
  split
  · intro hmem
    have hle := freeVar_id_le_maxVarId t ⟨maxVarId t + 1, τ⟩ hmem
    dsimp at hle
    omega
  · rename_i hnot
    exact hnot

/-- The binder chosen by `compTerm` has type `τ` and is not free in either input term. -/
theorem compBinder_fresh (τ : Ty) (t s : Term) (xId : Nat) :
    (freshVarFor τ xId (.app t s)).ty = τ ∧
    freshVarFor τ xId (.app t s) ∉ freeVarOccurrences t ∧
    freshVarFor τ xId (.app t s) ∉ freeVarOccurrences s := by
  refine ⟨freshVarFor_ty τ xId (.app t s), ?_, ?_⟩
  · intro ht
    have h := freshVarFor_not_mem_freeVarOccurrences τ xId (.app t s)
    simp [freeVarOccurrences] at h
    exact h.1 ht
  · intro hs
    have h := freshVarFor_not_mem_freeVarOccurrences τ xId (.app t s)
    simp [freeVarOccurrences] at h
    exact h.2 hs

/-- Set-level free-variable contract for `compTerm`: a variable is free in
`compTerm τ t s xId` iff it is free in `t` or free in `s`. -/
theorem mem_freeVarOccurrences_compTerm (τ : Ty) (t s : Term) (xId : Nat) (v : Var) :
    v ∈ freeVarOccurrences (compTerm τ t s xId) ↔
      v ∈ freeVarOccurrences t ∨ v ∈ freeVarOccurrences s := by
  have hfresh := freshVarFor_not_mem_freeVarOccurrences τ xId (.app t s)
  simp [freeVarOccurrences] at hfresh
  simp [compTerm, freeVarOccurrences]
  constructor
  · intro h
    rcases h with ⟨ht, _⟩ | ⟨hs, _⟩
    · exact Or.inl ht
    · exact Or.inr hs
  · intro h
    rcases h with ht | hs
    · refine Or.inl ⟨ht, ?_⟩
      intro heq
      subst heq
      exact hfresh.1 ht
    · refine Or.inr ⟨hs, ?_⟩
      intro heq
      subst heq
      exact hfresh.2 hs

/-- Free variables of `iterApp α base n`. -/
theorem mem_freeVarOccurrences_iterApp (α base : Term) (n : Nat) (v : Var) :
    v ∈ freeVarOccurrences (iterApp α base n) ↔
      (0 < n ∧ v ∈ freeVarOccurrences α) ∨ v ∈ freeVarOccurrences base := by
  induction n with
  | zero =>
      simp [iterApp]
  | succ n ih =>
      simp [iterApp, freeVarOccurrences, ih]
      constructor
      · intro h
        rcases h with hα | ⟨_, hα⟩ | hbase
        · exact Or.inl hα
        · exact Or.inl hα
        · exact Or.inr hbase
      · intro h
        rcases h with hα | hbase
        · exact Or.inl hα
        · exact Or.inr (Or.inr hbase)

/-- Zero-fold iteration `iterTerm α xId 0` has no free variables. -/
theorem freeVarOccurrences_iterTerm_zero (α : Term) (xId : Nat) :
    freeVarOccurrences (iterTerm α xId 0) = [] := by
  simp [iterTerm, iterApp, freeVarOccurrences]

theorem freeVars_iterTerm_zero (α : Term) (xId : Nat) :
    freeVars (iterTerm α xId 0) = [] := by
  simp [freeVars, freeVarOccurrences_iterTerm_zero, List.eraseDups]

/-- Positive-fold iteration `iterTerm α xId n` (`n > 0`) has the exact same free
variable set as `α`. -/
theorem mem_freeVarOccurrences_iterTerm_pos (α : Term) (xId n : Nat) (hn : 0 < n) (v : Var) :
    v ∈ freeVarOccurrences (iterTerm α xId n) ↔ v ∈ freeVarOccurrences α := by
  have hfresh := freshVarFor_not_mem_freeVarOccurrences .zero xId α
  simp [iterTerm, freeVarOccurrences, mem_freeVarOccurrences_iterApp, hn]
  constructor
  · rintro ⟨hα | rfl, hne⟩
    · exact hα
    · exact False.elim (hne rfl)
  · intro hα
    refine ⟨Or.inl hα, ?_⟩
    rintro rfl
    exact hfresh hα

theorem mem_eraseDupsBy_loop (v : Var) (as : List Var) :
    ∀ acc : List Var, v ∈ List.eraseDupsBy.loop (· == ·) as acc ↔ v ∈ as ∨ v ∈ acc := by
  induction as with
  | nil =>
      intro acc
      simp [List.eraseDupsBy.loop]
  | cons a as ih =>
      intro acc
      rw [List.eraseDupsBy.loop]
      cases h : acc.any (fun x => a == x)
      · rw [ih (a :: acc), List.mem_cons, List.mem_cons]
        exact ⟨
          fun
            | Or.inl h1 => Or.inl (Or.inr h1)
            | Or.inr (Or.inl h2) => Or.inl (Or.inl h2)
            | Or.inr (Or.inr h3) => Or.inr h3,
          fun
            | Or.inl (Or.inl h1) => Or.inr (Or.inl h1)
            | Or.inl (Or.inr h2) => Or.inl h2
            | Or.inr h3 => Or.inr (Or.inr h3)⟩
      · rw [ih acc, List.mem_cons]
        simp only [List.any_eq_true, beq_iff_eq] at h
        rcases h with ⟨x, hx, rfl⟩
        exact ⟨
          fun
            | Or.inl h1 => Or.inl (Or.inr h1)
            | Or.inr h2 => Or.inr h2,
          fun
            | Or.inl (Or.inl rfl) => Or.inr hx
            | Or.inl (Or.inr h1) => Or.inl h1
            | Or.inr h2 => Or.inr h2⟩

/-- Membership in `freeVars t` is equivalent to membership in `freeVarOccurrences t`. -/
theorem mem_freeVars_iff (t : Term) (v : Var) :
    v ∈ freeVars t ↔ v ∈ freeVarOccurrences t := by
  unfold freeVars List.eraseDups List.eraseDupsBy
  rw [mem_eraseDupsBy_loop]
  simp

/-- Set-level free-variable contract for `compTerm` on `freeVars`: a variable is free in
`compTerm τ t s xId` iff it is free in `t` or free in `s`. -/
theorem mem_freeVars_compTerm (τ : Ty) (t s : Term) (xId : Nat) (v : Var) :
    v ∈ freeVars (compTerm τ t s xId) ↔ v ∈ freeVars t ∨ v ∈ freeVars s := by
  simp [mem_freeVars_iff, mem_freeVarOccurrences_compTerm]

/-- Positive-fold iteration `iterTerm α xId n` (`n > 0`) has the exact same `freeVars` set as `α`. -/
theorem mem_freeVars_iterTerm_pos (α : Term) (xId n : Nat) (hn : 0 < n) (v : Var) :
    v ∈ freeVars (iterTerm α xId n) ↔ v ∈ freeVars α := by
  simp [mem_freeVars_iff, mem_freeVarOccurrences_iterTerm_pos α xId n hn]

/-- Typing preservation for `compTerm`. -/
theorem compTerm_hasType {τ : Ty} {t s : Term} (xId : Nat)
    (ht : HasType t (.arr τ τ)) (hs : HasType s (.arr τ τ)) :
    HasType (compTerm τ t s xId) (.arr τ τ) := by
  dsimp [compTerm]
  have hvar : HasType (.var (freshVarFor τ xId (.app t s))) τ :=
    Eq.mp (congrArg (HasType (.var (freshVarFor τ xId (.app t s)))) (freshVarFor_ty τ xId (.app t s)))
      (HasType.var (freshVarFor τ xId (.app t s)))
  exact Eq.mp
    (congrArg (fun σ => HasType (.lam (freshVarFor τ xId (.app t s)) (.app t (.app s (.var (freshVarFor τ xId (.app t s)))))) (.arr σ τ))
      (freshVarFor_ty τ xId (.app t s)))
    (HasType.lam (freshVarFor τ xId (.app t s)) (HasType.app ht (HasType.app hs hvar)))

/-- Typing preservation for `iterApp`. -/
theorem iterApp_hasType {α base : Term} (n : Nat)
    (hα : HasType α Ty.endo) (hbase : HasType base .zero) :
    HasType (iterApp α base n) .zero := by
  induction n with
  | zero => exact hbase
  | succ n ih => exact HasType.app hα ih

/-- Typing preservation for `iterTerm`. -/
theorem iterTerm_hasType {α : Term} (xId n : Nat)
    (hα : HasType α Ty.endo) :
    HasType (iterTerm α xId n) Ty.endo := by
  dsimp [iterTerm, Ty.endo]
  have hvar : HasType (.var (freshVarFor .zero xId α)) .zero :=
    Eq.mp (congrArg (HasType (.var (freshVarFor .zero xId α))) (freshVarFor_ty .zero xId α))
      (HasType.var (freshVarFor .zero xId α))
  exact Eq.mp
    (congrArg (fun σ => HasType (.lam (freshVarFor .zero xId α) (iterApp α (.var (freshVarFor .zero xId α)) n)) (.arr σ .zero))
      (freshVarFor_ty .zero xId α))
    (HasType.lam (freshVarFor .zero xId α) (iterApp_hasType n hα hvar))

#print axioms freeVar_id_le_maxVarId
#print axioms freshVarFor_ty
#print axioms freshVarFor_not_mem_freeVarOccurrences
#print axioms compBinder_fresh
#print axioms mem_freeVarOccurrences_compTerm
#print axioms mem_freeVarOccurrences_iterApp
#print axioms freeVarOccurrences_iterTerm_zero
#print axioms freeVars_iterTerm_zero
#print axioms mem_freeVarOccurrences_iterTerm_pos
#print axioms mem_freeVars_iff
#print axioms mem_freeVars_compTerm
#print axioms mem_freeVars_iterTerm_pos
#print axioms compTerm_hasType
#print axioms iterApp_hasType
#print axioms iterTerm_hasType

end Schwichtenberg1976V2.Audit
