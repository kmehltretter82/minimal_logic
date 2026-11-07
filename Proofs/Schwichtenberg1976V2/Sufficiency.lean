import Proofs.Schwichtenberg1976V2.Combinators

/-!
# Every extended polynomial is λ-definable (pp. 113–114)

Projections are defined by `λF₁ … Fₖ. Fᵢ`. Composition `g(h₁(v), …, h_m(v))` is defined by
`λF⃗. G (H₁ F⃗) … (H_m F⃗)` from closed defining terms `G` and `Hⱼ`. Constants, `+`, `·` and
the conditional are compositions with `n̄` and the combinators of p. 113.

All proofs are constructive. The family `H₁, …, H_m` comes from finite choice, proved by
induction on `m`.
-/

namespace Schwichtenberg1976V2.Proofs

open Schwichtenberg1976V2

/-! ## Lists -/

theorem nodup_map_of_injective {α β : Type} {f : α → β} (hf : Function.Injective f) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
      rw [List.nodup_cons] at h
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, nodup_map_of_injective hf h.2⟩
      obtain ⟨b, hb, hfb⟩ := List.mem_map.1 hm
      exact h.1 (hf hfb ▸ hb)

theorem numeralArgs_eq (k : Nat) (v : Fin k → Nat) :
    numeralArgs k v = (List.finRange k).map (fun i => churchNumeral (v i)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [numeralArgs, ih, List.finRange_succ, List.map_cons, List.map_map]
      rfl

/-- Finite choice, proved by induction on `m` without the axiom of choice. -/
theorem fin_choice {m : Nat} {P : Fin m → Term → Prop} (h : ∀ j, ∃ t, P j t) :
    ∃ H : Fin m → Term, ∀ j, P j (H j) := by
  induction m with
  | zero => exact ⟨fun j => j.elim0, fun j => j.elim0⟩
  | succ m ih =>
      obtain ⟨t0, h0⟩ := h 0
      obtain ⟨H', hH'⟩ := ih (P := fun j => P j.succ) (fun j => h j.succ)
      exact ⟨Fin.cases t0 H', fun j => Fin.cases h0 hH' j⟩

/-! ## Application and abstraction blocks -/

theorem appMany_cons (t a : Term) (args : List Term) :
    Term.appMany t (a :: args) = Term.appMany (.app t a) args := rfl

theorem appMany_cong {α : Type} (f g : α → Term) :
    ∀ (L : List α) {t t' : Term}, ReducesTo t t' → (∀ x ∈ L, ReducesTo (f x) (g x)) →
      ReducesTo (Term.appMany t (L.map f)) (Term.appMany t' (L.map g))
  | [], _, _, ht, _ => ht
  | x :: L, _, _, ht, hL => by
      simp only [List.map_cons, appMany_cons]
      exact appMany_cong f g L (.app ht (hL x (List.mem_cons_self ..)))
        (fun y hy => hL y (List.mem_cons_of_mem _ hy))

theorem appMany_cong_head (args : List Term) {t t' : Term} (ht : ReducesTo t t') :
    ReducesTo (Term.appMany t args) (Term.appMany t' args) := by
  have := appMany_cong id id args ht (fun x _ => ReducesTo.rfl' x)
  simpa using this

theorem substMany_appMany (l : List (Var × Term)) :
    ∀ (args : List Term) (t : Term),
      substMany (Term.appMany t args) l =
        Term.appMany (substMany t l) (args.map (substMany · l))
  | [], _ => rfl
  | a :: args, t => by
      rw [appMany_cons, substMany_appMany l args, substMany_app, List.map_cons, appMany_cons]

theorem subst_lamMany_closed {s : Term} (hs : freeVarOccurrences s = []) (x : Var) (b : Term) :
    ∀ xs : List Var, x ∉ xs → substTerm (Term.lamMany xs b) x s = Term.lamMany xs (substTerm b x s)
  | [], _ => rfl
  | y :: xs, hx => by
      have hyx : y ≠ x := fun h => hx (h ▸ List.mem_cons_self ..)
      simp only [Term.lamMany]
      rw [subst_lam_fresh _ s hyx (by simp [hs]),
        subst_lamMany_closed hs x b xs (fun h => hx (List.mem_cons_of_mem _ h))]

/-- β-reducing a block `(λx₁ … xₙ. b) a₁ … aₙ` of closed arguments. -/
theorem beta_lamMany :
    ∀ (ps : List (Var × Term)) (b : Term), (ps.map Prod.fst).Nodup →
      (∀ p ∈ ps, freeVarOccurrences p.2 = []) →
      ReducesTo (Term.appMany (Term.lamMany (ps.map Prod.fst) b) (ps.map Prod.snd))
        (substMany b ps)
  | [], b, _, _ => ReducesTo.rfl' b
  | (x, a) :: ps, b, hnd, hcl => by
      rw [List.map_cons, List.nodup_cons] at hnd
      have ha : freeVarOccurrences a = [] := hcl (x, a) (List.mem_cons_self ..)
      simp only [List.map_cons, Term.lamMany, appMany_cons, substMany]
      refine .trans (appMany_cong_head _ (.beta _ _ _)) ?_
      rw [subst_lamMany_closed ha x b _ hnd.1]
      exact beta_lamMany ps _ hnd.2 (fun p hp => hcl p (List.mem_cons_of_mem _ hp))

/-! ## Typing and free variables of the blocks -/

theorem lamMany_hasType {b : Term} (hb : HasType b Ty.nu) :
    ∀ xs : List Var, (∀ x ∈ xs, x.ty = Ty.nu) →
      HasType (Term.lamMany xs b) (Ty.nuArity xs.length)
  | [], _ => hb
  | x :: xs, hxs => by
      have h := HasType.lam x (lamMany_hasType hb xs fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      rw [hxs x (List.mem_cons_self ..)] at h
      exact h

theorem appMany_hasType :
    ∀ (args : List Term) {t : Term}, HasType t (Ty.nuArity args.length) →
      (∀ a ∈ args, HasType a Ty.nu) → HasType (Term.appMany t args) Ty.nu
  | [], _, ht, _ => ht
  | a :: args, _, ht, ha =>
      appMany_hasType args (.app ht (ha a (List.mem_cons_self ..)))
        (fun b hb => ha b (List.mem_cons_of_mem _ hb))

theorem mem_fvo_appMany (v : Var) :
    ∀ (args : List Term) (t : Term), v ∈ freeVarOccurrences (Term.appMany t args) →
      v ∈ freeVarOccurrences t ∨ ∃ a ∈ args, v ∈ freeVarOccurrences a
  | [], _, h => Or.inl h
  | a :: args, t, h => by
      rcases mem_fvo_appMany v args _ h with h | ⟨b, hb, hv⟩
      · rcases (mem_fvo_app _ _ _).1 h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨a, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hv⟩

theorem mem_fvo_lamMany (v : Var) (b : Term) :
    ∀ xs : List Var, v ∈ freeVarOccurrences (Term.lamMany xs b) →
      v ∈ freeVarOccurrences b ∧ v ∉ xs
  | [], h => ⟨h, by simp⟩
  | x :: xs, h => by
      simp only [Term.lamMany, mem_fvo_lam] at h
      obtain ⟨hb, hx⟩ := mem_fvo_lamMany v b xs h.1
      exact ⟨hb, by simp [hx, h.2]⟩

/-! ## The argument variables -/

/-- The bound variables `F₁, …, Fₖ` of the defining terms. -/
def argVar {k : Nat} (i : Fin k) : Var := ⟨i.val, Ty.nu⟩

theorem argVar_injective {k : Nat} : Function.Injective (argVar (k := k)) := by
  intro i j h
  exact Fin.ext (congrArg Var.id h)

def argVars (k : Nat) : List Var := (List.finRange k).map argVar

/-- The substitution `Fᵢ ↦ v̄ᵢ` performed by applying a defining term to numerals. -/
def argSubst (k : Nat) (v : Fin k → Nat) : List (Var × Term) :=
  (List.finRange k).map (fun i => (argVar i, churchNumeral (v i)))

theorem argSubst_spec (k : Nat) (v : Fin k → Nat) :
    (argSubst k v).map Prod.fst = argVars k ∧
    (argSubst k v).map Prod.snd = numeralArgs k v ∧
    (argVars k).Nodup ∧
    ∀ p ∈ argSubst k v, freeVarOccurrences p.2 = [] := by
  refine ⟨by simp [argSubst, argVars, List.map_map], ?_, ?_, ?_⟩
  · rw [numeralArgs_eq]; simp [argSubst, List.map_map]
  · exact nodup_map_of_injective argVar_injective (List.nodup_finRange k)
  · intro p hp
    simp only [argSubst, List.mem_map] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact fvo_churchNumeral _

/-- Applying `λF⃗. b` to numerals reduces to `b` with the numerals substituted. -/
theorem apply_lamMany (k : Nat) (v : Fin k → Nat) (b : Term) :
    ReducesTo (Term.appMany (Term.lamMany (argVars k) b) (numeralArgs k v))
      (substMany b (argSubst k v)) := by
  obtain ⟨h1, h2, h3, h4⟩ := argSubst_spec k v
  have := beta_lamMany (argSubst k v) b (h1 ▸ h3) h4
  rwa [h1, h2] at this

theorem substMany_argVar (k : Nat) (v : Fin k → Nat) (i : Fin k) :
    substMany (.var (argVar i)) (argSubst k v) = churchNumeral (v i) := by
  have := substMany_var_index argVar argVar_injective (fun j => churchNumeral (v j))
    (fun j => fvo_churchNumeral _) i (List.finRange k)
  rw [if_pos (List.mem_finRange i)] at this
  exact this

theorem substMany_closed' {t : Term} (ht : freeVarOccurrences t = []) (k : Nat)
    (v : Fin k → Nat) : substMany t (argSubst k v) = t :=
  substMany_closed ht _ (argSubst_spec k v).2.2.2

theorem fvo_nil_of_defines {k : Nat} {t : Term} {f : (Fin k → Nat) → Nat}
    (h : DefinesFunction k t f) : freeVarOccurrences t = [] :=
  fvo_nil_of_closed h.2.1

/-! ## Projections and composition -/

theorem proj_definable (k : Nat) (i : Fin k) : IsLambdaDefinable k (fun v => v i) := by
  refine ⟨Term.lamMany (argVars k) (.var (argVar i)), ?_, ?_, fun v => ?_⟩
  · have := lamMany_hasType (HasType.var (argVar i)) (argVars k) (by simp [argVars, argVar])
    simpa [argVars] using this
  · refine closed_of_fvo_nil (eq_nil_of_forall_not_mem fun x hx => ?_)
    obtain ⟨hx1, hx2⟩ := mem_fvo_lamMany x _ _ hx
    rw [mem_fvo_var] at hx1
    subst hx1
    exact hx2 (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)
  · refine .trans (apply_lamMany k v _) ?_
    rw [substMany_argVar]
    exact ReducesTo.rfl' _

theorem comp_definable {k m : Nat} {g : (Fin m → Nat) → Nat}
    {hs : Fin m → (Fin k → Nat) → Nat}
    (hg : IsLambdaDefinable m g) (hh : ∀ j, IsLambdaDefinable k (hs j)) :
    IsLambdaDefinable k (fun v => g (fun j => hs j v)) := by
  obtain ⟨G, hG⟩ := hg
  obtain ⟨H, hH⟩ := fin_choice hh
  let inner (j : Fin m) : Term := Term.appMany (H j) ((argVars k).map Term.var)
  let body : Term := Term.appMany G ((List.finRange m).map inner)
  refine ⟨Term.lamMany (argVars k) body, ?_, ?_, fun v => ?_⟩
  · -- typing
    have hargs : ∀ a ∈ (argVars k).map Term.var, HasType a Ty.nu := by
      intro a ha
      simp only [argVars, List.map_map, List.mem_map] at ha
      obtain ⟨i, _, rfl⟩ := ha
      exact HasType.var (argVar i)
    have hinner : ∀ j, HasType (inner j) Ty.nu := fun j =>
      appMany_hasType _ (by simpa [argVars] using (hH j).1) hargs
    have hbody : HasType body Ty.nu :=
      appMany_hasType _ (by simpa using hG.1) (by
        intro a ha
        simp only [List.mem_map] at ha
        obtain ⟨j, _, rfl⟩ := ha
        exact hinner j)
    have := lamMany_hasType hbody (argVars k) (by simp [argVars, argVar])
    simpa [argVars] using this
  · -- closedness
    refine closed_of_fvo_nil (eq_nil_of_forall_not_mem fun x hx => ?_)
    obtain ⟨hx1, hx2⟩ := mem_fvo_lamMany x _ _ hx
    rcases mem_fvo_appMany x _ _ hx1 with h | ⟨a, ha, h⟩
    · rw [fvo_nil_of_defines hG] at h; simp at h
    · simp only [List.mem_map] at ha
      obtain ⟨j, _, rfl⟩ := ha
      rcases mem_fvo_appMany x _ _ h with h | ⟨b, hb, h⟩
      · rw [fvo_nil_of_defines (hH j)] at h; simp at h
      · simp only [List.mem_map] at hb
        obtain ⟨y, hy, rfl⟩ := hb
        rw [mem_fvo_var] at h
        subst h
        exact hx2 hy
  · -- computation
    refine .trans (apply_lamMany k v body) ?_
    have hsub : substMany body (argSubst k v) =
        Term.appMany G ((List.finRange m).map fun j =>
          Term.appMany (H j) (numeralArgs k v)) := by
      simp only [body, inner, substMany_appMany, substMany_closed' (fvo_nil_of_defines hG),
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      simp only [Function.comp, substMany_appMany, substMany_closed' (fvo_nil_of_defines (hH j)),
        List.map_map]
      congr 1
      rw [numeralArgs_eq]
      simp only [argVars, List.map_map]
      apply List.map_congr_left
      intro i _
      exact substMany_argVar k v i
    rw [hsub]
    refine .trans (appMany_cong (fun j => Term.appMany (H j) (numeralArgs k v))
      (fun j => churchNumeral (hs j v)) (List.finRange m) (ReducesTo.rfl' G)
      (fun j _ => (hH j).2.2 v)) ?_
    have := hG.2.2 (fun j => hs j v)
    rwa [numeralArgs_eq] at this

theorem definable_congr {k : Nat} {f g : (Fin k → Nat) → Nat} (hfg : ∀ v, f v = g v)
    (h : IsLambdaDefinable k f) : IsLambdaDefinable k g := by
  have : f = g := funext hfg
  exact this ▸ h

/-- The argument families of the binary and ternary operations. -/
def pair {k : Nat} (f g : (Fin k → Nat) → Nat) (j : Fin 2) : (Fin k → Nat) → Nat :=
  match j with
  | ⟨0, _⟩ => f
  | _ => g

def triple {k : Nat} (f g h : (Fin k → Nat) → Nat) (j : Fin 3) : (Fin k → Nat) → Nat :=
  match j with
  | ⟨0, _⟩ => f
  | ⟨1, _⟩ => g
  | _ => h

theorem pair_definable {k : Nat} {f g : (Fin k → Nat) → Nat}
    (hf : IsLambdaDefinable k f) (hg : IsLambdaDefinable k g) :
    ∀ j, IsLambdaDefinable k (pair f g j)
  | ⟨0, _⟩ => hf
  | ⟨1, _⟩ => hg

theorem triple_definable {k : Nat} {f g h : (Fin k → Nat) → Nat}
    (hf : IsLambdaDefinable k f) (hg : IsLambdaDefinable k g) (hh : IsLambdaDefinable k h) :
    ∀ j, IsLambdaDefinable k (triple f g h j)
  | ⟨0, _⟩ => hf
  | ⟨1, _⟩ => hg
  | ⟨2, _⟩ => hh

/-- **Sufficiency**: every extended polynomial is λ-definable. -/
theorem sufficiency : ∀ {k : Nat} {f : (Fin k → Nat) → Nat},
    IsExtendedPolyInd f → IsLambdaDefinable k f := by
  intro k f h
  induction h with
  | const c =>
      have h0 : IsLambdaDefinable 0 (fun _ => c) :=
        ⟨churchNumeral c, numeral_hasType c, closed_of_fvo_nil (fvo_churchNumeral c),
          fun _ => ReducesTo.rfl' _⟩
      exact comp_definable (hs := fun j => j.elim0) h0 (fun j => j.elim0)
  | proj i => exact proj_definable _ i
  | add _ _ ihf ihg =>
      exact definable_congr (fun v => rfl)
        (comp_definable ⟨_, addComb_defines⟩ (pair_definable ihf ihg))
  | mul _ _ ihf ihg =>
      exact definable_congr (fun v => rfl)
        (comp_definable ⟨_, mulComb_defines⟩ (pair_definable ihf ihg))
  | cond _ _ _ ihf ihg ihh =>
      exact definable_congr (fun v => rfl)
        (comp_definable ⟨_, condComb_defines⟩ (triple_definable ihf ihg ihh))
  | comp _ _ ihg ihhs => exact comp_definable ihg ihhs

/-- **Milestone 1** (`combinators_and_sufficiency`, pp. 113–114). -/
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
      IsExtendedPolyInd f → IsLambdaDefinable k f) :=
  ⟨closed_normal_nu, addComb_defines, mulComb_defines, constComb_defines, condComb_defines,
    sufficiency⟩

end Schwichtenberg1976V2.Proofs
