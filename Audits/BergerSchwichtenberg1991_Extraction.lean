import Definitions.Def_BergerSchwichtenberg1991_Models

namespace BergerSchwichtenberg1991

def witnessX : Var := indexedVar .base [false]
def witnessTerm : Term := .lam ⟨.named 0, .base⟩ (.lam ⟨.named 1, .base⟩ (.var witnessX))


def auditFree (z : Var) : Term → Prop
  | .var v => z = v
  | .app r s => auditFree z r ∨ auditFree z s
  | .lam v r => z ≠ v ∧ auditFree z r

theorem auditFree_not_all (r : Term) (z : Var) (h : z ∉ allVars r) :
    ¬ auditFree z r := by
  induction r with
  | var v => simp_all [allVars, auditFree]
  | app r s ihr ihs => simp_all [allVars, auditFree]
  | lam v r ih => simp_all [allVars, auditFree]

theorem auditFree_rename (r : Term) (x y z : Var) (hf : y ∉ allVars r) (hne : x ≠ y) :
    auditFree z (renameFreeVar r x y) ↔
      (z = y ∧ auditFree x r) ∨ (z ≠ x ∧ auditFree z r) := by
  induction r with
  | var v =>
    simp only [renameFreeVar]
    split <;> simp_all [auditFree, allVars] <;> grind
  | app r s ihr ihs =>
    simp_all [renameFreeVar, auditFree, allVars]
    grind
  | lam v r ih =>
    simp only [renameFreeVar]
    split
    · simp_all [auditFree, allVars]
    · simp_all [auditFree, allVars]
      grind

theorem auditRename_self (r : Term) (x : Var) : renameFreeVar r x x = r := by
  induction r with
  | var v => simp only [renameFreeVar]; split <;> simp_all
  | app r s ihr ihs => simp [renameFreeVar, ihr, ihs]
  | lam v r ih => simp only [renameFreeVar]; split <;> simp_all

theorem auditFree_alpha {r s : Term} (h : AlphaEq r s) (z : Var) :
    auditFree z r ↔ auditFree z s := by
  induction h with
  | refl r => rfl
  | symm h ih => exact ih.symm
  | trans h h' ih ih' => exact ih.trans ih'
  | app h h' ih ih' => simp_all [auditFree]
  | lam_congr x h ih => simp_all [auditFree]
  | lam_rename x y r hty hf =>
    by_cases hne : x = y
    · subst y
      simp [auditRename_self]
    · have hf' : y ∉ allVars r := hf.resolve_left (Ne.symm hne)
      simp only [auditFree]
      rw [auditFree_rename r x y z hf' hne]
      have noty := auditFree_not_all r y hf'
      grind

instance auditFreeDec (z : Var) (t : Term) : Decidable (auditFree z t) :=
  match t with
  | .var v => inferInstanceAs (Decidable (z = v))
  | .app r s =>
      letI := auditFreeDec z r
      letI := auditFreeDec z s
      inferInstanceAs (Decidable (auditFree z r ∨ auditFree z s))
  | .lam v r =>
      letI := auditFreeDec z r
      inferInstanceAs (Decidable (z ≠ v ∧ auditFree z r))

theorem auditFree_witness : auditFree witnessX witnessTerm := by
  simp [auditFree, witnessX, witnessTerm, indexedVar]

theorem auditNotFree_extracted : ¬ auditFree witnessX (EXTRACT (EMB witnessTerm)) := by
  decide +kernel

theorem extraction_not_alpha : ¬ AlphaEq (EXTRACT (EMB witnessTerm)) witnessTerm := by
  intro h
  exact auditNotFree_extracted ((auditFree_alpha h witnessX).mpr auditFree_witness)

theorem lemma_2_refuted : ¬ ((∀ r s : Term, AlphaEq r s ↔ EMB r = EMB s) ∧
    (∀ r : Term, AlphaEq (EXTRACT (EMB r)) r) ∧
    (∀ (r : Term) (k : Index), EMB (EMB r k) k = EMB r k)) := by
  intro h
  exact extraction_not_alpha (h.2.1 witnessTerm)

#print axioms extraction_not_alpha
#print axioms lemma_2_refuted

universe u

theorem theorem_1_refuted (M : AdmissibleModel.{u}) (IF : InversionFunctionals M) :
    ¬ ((∀ (ρ : Ty) (a : M.Dom ρ),
      M.IsLambdaDefinable ρ a →
      ∃ t : Term,
        IF.IsPeResult ρ a t ∧
        IsClosed t ∧
        IsLongBetaNormal ρ t ∧
        ∀ η : M.Env, M.eqM ρ (M.eval t η ρ) a) ∧
    (∀ (ρ : Ty) (r rStar : Term) (θ : Substitution),
      HasType r ρ →
      HasType rStar ρ →
      IsLongBetaNormal ρ rStar →
      BetaEtaEq r rStar →
      IsWellTypedSubst θ →
      IF.IsPeResult ρ (M.eval r (IF.etaSubst θ) ρ) (EXTRACT (EMB (applySubst θ rStar))) ∧
      AlphaEq (EXTRACT (EMB (applySubst θ rStar))) (applySubst θ rStar)) ∧
    (∀ (ρ : Ty) (r s : Term),
      HasType r ρ →
      HasType s ρ →
      M.ModelsEq ρ r s →
      BetaEtaEq r s)) := by
  intro h
  have ht : HasType witnessTerm (.arr .base (.arr .base .base)) :=
    .lam _ (.lam _ (.var _))
  have hn : IsLongBetaNormal (.arr .base (.arr .base .base)) witnessTerm :=
    .lam ⟨.named 0, .base⟩ (.lam ⟨.named 1, .base⟩ (.baseNeutral (.var witnessX)))
  have he := (h.2.1 _ witnessTerm witnessTerm idSubst ht ht hn (.refl _) (fun x => .var x)).2
  have same : applySubst idSubst witnessTerm = witnessTerm := by decide +kernel
  rw [same] at he
  exact extraction_not_alpha he

#print axioms theorem_1_refuted
end BergerSchwichtenberg1991
