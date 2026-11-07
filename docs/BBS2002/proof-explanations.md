# BBS2002 proof explanations

These are the explanations attached to the accepted prove2.me submissions, in dependency order. Each one describes the matching file in `Solutions/`.

## `BBS2002.lemmas_2_1_to_2_3`

*Equivalence of Z^X and Z_0^X (Lemma 2.1), L-Stability (Lemma 2.2), and Quantifier-Free Case Distinction (Lemma 2.3)*. Accepted 2026-10-31, submission `85581098-c051-4137-a38d-d45bfe64d1ab`.

### Proof of Lemmas 2.1, 2.2 (Stability), and 2.3 (Cases) (Berger–Buchholz–Schwichtenberg 2002)

We formalize the three foundational syntactic metatheorems from Section 2 (p. 5) of Berger, Buchholz, and Schwichtenberg (2002) for Heyting arithmetic in finite types $\mathbf{Z} := \mathbf{HA}^\omega$ and its extensions $\mathbf{Z}^X, \mathbf{Z}_0^X$:

1. **Lemma 2.1 ($\mathbf{Z}^X \vdash A \iff \mathbf{Z}_0^X \vdash A^{\mathsf{F}}$, where $\mathsf{F} := \mathrm{atom}(\mathtt{false})$)**:
   - *Forward direction ($\Rightarrow$)*: We define a recursive proof transformation `substBotFalseProof` on derivation terms $M$ that replaces every occurrence of $\bot$ in formulas and assumption labels by $\mathrm{atom}(\mathtt{false})$ and translates every instance of ex-falso-quodlibet $\mathrm{efq}_B : \bot \to B$ into the truth axiom $\mathrm{axFalse}_{B^{\mathsf{F}}} : \mathrm{atom}(\mathtt{false}) \to B^{\mathsf{F}}$. Since $\mathrm{atom}(\mathtt{false})$ is closed and variable-free, syntactic substitution $A^{\mathsf{F}} := A[\mathrm{atom}(\mathtt{false})/\bot]$ commutes strictly with variable renaming, capture-avoiding term substitution, and $\beta R$-conversion, preserving free assumption variables and transforming any $\mathbf{Z}^X$-derivation of $A$ into a $\mathbf{Z}_0^X$-derivation of $A^{\mathsf{F}}$.
   - *Backward direction ($\Leftarrow$)*: Every $\mathbf{Z}_0^X$-derivation embeds directly into $\mathbf{Z}^X$, and by structural induction on $A \in \mathcal{L}[X]$ we construct closed $\mathbf{Z}^X$-derivations of $A \leftrightarrow A^{\mathsf{F}}$ using $\mathrm{efq}_{\mathrm{atom}(\mathtt{false})} : \bot \to \mathrm{atom}(\mathtt{false})$ and $\mathrm{axFalse}_\bot : \mathrm{atom}(\mathtt{false}) \to \bot$ in the base case $A = \bot$.

2. **Lemma 2.2 (Stability, $\mathbf{Z} \vdash \neg\neg A \to A$ for $A \in \mathcal{L}$)**:
   We proceed by structural induction on well-typed $\mathcal{L}$-formulas $A$:
   - For $A = \bot$, $(\neg\bot \to \bot) \to \bot$ follows by applying the hypothesis $\neg\bot \to \bot$ to $\lambda u^\bot. u$.
   - For $A = \mathrm{atom}(t)$ with $t : \mathbf{o}$, we apply boolean induction $\mathrm{Ind}_{p, B}$ on $p^\mathbf{o}$ with $B(p) := \neg\neg \mathrm{atom}(p) \to \mathrm{atom}(p)$. The $\mathtt{true}$-branch follows from $\mathrm{axTrue} : \mathrm{atom}(\mathtt{true})$, and the $\mathtt{false}$-branch follows by applying $\neg\neg\mathrm{atom}(\mathtt{false})$ to $\mathrm{axFalse}_\bot : \neg\mathrm{atom}(\mathtt{false})$ and eliminating $\bot$ via $\mathrm{efq}_{\mathrm{atom}(\mathtt{false})}$.
   - For $A = B \to C$, from $\neg\neg(B \to C)$ and $B$ we derive $\neg\neg C$ intuitionistically, then apply the induction hypothesis $\neg\neg C \to C$.
   - For $A = \forall x\, B$, from $\neg\neg\forall x\, B$ we derive $\neg\neg B$ via $\forall$-elimination $(\forall x\, B) \to B$, apply the induction hypothesis $\neg\neg B \to B$, and generalize over $x$ (since $x \notin \mathrm{FV}(\neg\neg\forall x\, B)$).

3. **Lemma 2.3 (Cases, $\mathbf{Z}^X \vdash (\neg C \to A) \to (C \to A) \to A$ for quantifier-free $C \in \mathcal{L}$ and $A \in \mathcal{L}[X]$)**:
   We proceed by structural induction on quantifier-free $C \in \mathcal{L}$:
   - For $C = \bot$, we apply $\neg\bot \to A$ to $\lambda u^\bot. u$.
   - For $C = \mathrm{atom}(t)$, we choose a fresh boolean variable $p^\mathbf{o}$ with $\mathrm{id}(p) = \mathrm{maxVarId}(A) + 1$ so that $p \notin \mathrm{FV}(A)$, and apply boolean induction $\mathrm{Ind}_{p, B}$ to $B(p) := (\neg\mathrm{atom}(p) \to A) \to (\mathrm{atom}(p) \to A) \to A$. Using the capture-avoiding $\alpha$-equivalence lemma `substFormula_betaREq_of_not_free` ($A[s/p] \equiv_{\beta R} A$ for $p \notin \mathrm{FV}(A)$) and the conversion rule `Derivable.conv`, the $\mathtt{true}$- and $\mathtt{false}$-branches reduce to $\mathrm{axTrue}$ and $\mathrm{axFalse}_\bot$, and $\forall$-elimination at $t$ yields the claim.
   - For $C = C_1 \to C_2$, assuming $\neg(C_1 \to C_2) \to A$ and $(C_1 \to C_2) \to A$, we first split on $C_1$ using $\mathrm{IH}_{C_1}$: if $\neg C_1$, then $C_1 \to C_2$ holds via $\mathrm{efq}_{C_2}$; if $C_1$, we split on $C_2$ using $\mathrm{IH}_{C_2}$, obtaining $\neg(C_1 \to C_2)$ from $C_1 \land \neg C_2$ and $C_1 \to C_2$ from $C_2$.

## `BBS2002.lemma_3_1_and_3_2`

*Derivability Properties of Definite and Goal Formulas (Lemmas 3.1 & 3.2)*. Accepted 2026-10-31, submission `afb63d6c-b19f-40cb-b447-59f79fd29daf`.

### Proof of Lemmas 3.1 and 3.2 (Berger–Buchholz–Schwichtenberg 2002)

We prove Lemma 3.1 (equations (3)–(6), pp. 6–8) and Lemma 3.2 (p. 9) of Berger, Buchholz, and Schwichtenberg (2002), characterizing the derivability properties in $\mathbf{Z}^X$ of definite formulas $D$ and goal formulas $G$ under the refined $A$-translation $B^X := B[X/\bot]$ (`substBotWithX`):

$$\begin{aligned}
(3)\quad & \mathbf{Z}^X \vdash (\neg D \to X) \to D^X \qquad (\text{for } D \text{ relevant}), \\
(4)\quad & \mathbf{Z}^X \vdash D \to D^X, \\
(5)\quad & \mathbf{Z}^X \vdash G^X \to G \qquad (\text{for } G \text{ irrelevant}), \\
(6)\quad & \mathbf{Z}^X \vdash G^X \to (G \to X) \to X,
\end{aligned}$$

and for any list of goal formulas $\vec{G} = G_1, \dots, G_n$:

$$\mathbf{Z}^X \vdash (\vec{G} \to X) \to \vec{G}^X \to X.$$

#### Proof Idea

Since the inductive definitions of definite formulas (`IsDefiniteFormula`) and goal formulas (`IsGoalFormula`) follow the syntactic structure of formulas $A \in \mathcal{L}$, we establish (3)–(6) simultaneously by structural induction on $A$ (`lemma_3_1_aux`). The critical case in (6) for an implication goal formula $D \to G$ with irrelevant $D$ uses the side condition that irrelevant definite premises of goal implications are quantifier-free, allowing us to invoke **Lemma 2.3 (Cases)** from `BBS2002.lemmas_2_1_to_2_3`.

#### Detailed Steps

1. **Base cases ($A = \bot$ and $A = \mathrm{atom}(t)$)**:
   - For $A = \bot$, we have $\bot^X = X$, $\mathrm{isRelevant}(\bot) = \mathtt{true}$, and $\mathrm{isIrrelevant}(\bot) = \mathtt{false}$. Equation (3) reduces to $(\neg\bot \to X) \to X$ (proved by applying the premise to $\lambda u^\bot. u$), equation (4) is $\mathrm{efq}_X : \bot \to X$, equation (5) holds vacuously, and equation (6) is $X \to (\bot \to X) \to X$.
   - For $A = \mathrm{atom}(t)$, we have $\mathrm{atom}(t)^X = \mathrm{atom}(t)$ and $\mathrm{isRelevant}(\mathrm{atom}(t)) = \mathtt{false}$. Equation (3) holds vacuously, equations (4) and (5) are the identity $\mathrm{atom}(t) \to \mathrm{atom}(t)$, and equation (6) is $\mathrm{atom}(t) \to (\mathrm{atom}(t) \to X) \to X$.

2. **Inductive step for definite implications $G \to D$**:
   - *Equation (3) ($D$ relevant)*: Working in context $\Gamma = [\neg(G \to D) \to X,\, G^X]$, by $\mathrm{IH}_D(3)$ it suffices to derive $\neg D \to X$. Assuming $\neg D$, by $\mathrm{IH}_G(6)$ applied to $G^X$ it suffices to derive $G \to X$; assuming $G$, any $G \to D$ yields $D$ and thus $\bot$ with $\neg D$, establishing $\neg(G \to D)$ and hence $X$.
   - *Equation (4)*: If $D$ is relevant, assuming $G \to D$ and $G^X$, the same reduction via $\mathrm{IH}_D(3)$ and $\mathrm{IH}_G(6)$ reduces the goal to deriving $X$ from $G \to D$, $\neg D$, and $G$, which yields $\bot$ and hence $X$ via $\mathrm{efq}_X$. If $D$ is irrelevant, the side condition on definite implications ensures $G$ is also irrelevant, so $G^X \to G$ holds by $\mathrm{IH}_G(5)$ and $D \to D^X$ holds by $\mathrm{IH}_D(4)$.

3. **Inductive step for goal implications $D \to G$**:
   - *Equation (5) ($G$ irrelevant)*: Immediate from $\mathrm{IH}_D(4) : D \to D^X$ and $\mathrm{IH}_G(5) : G^X \to G$.
   - *Equation (6)*: Working in context $\Gamma_0 = [D^X \to G^X,\, (D \to G) \to X]$, we first establish three auxiliary derivations:
     $$\Gamma_0 \vdash \neg D \to X, \qquad \Gamma_0 \vdash G \to X, \qquad \Gamma_0 \vdash D^X \to X,$$
     where the first uses $\mathrm{efq}_G : \bot \to G$ to build $D \to G$ from $\neg D$, the second uses weakening $G \to (D \to G)$, and the third chains $D^X \to G^X$ with $\mathrm{IH}_G(6) : G^X \to (G \to X) \to X$.
     If $D$ is relevant, $\mathrm{IH}_D(3) : (\neg D \to X) \to D^X$ yields $\Gamma_0 \vdash D^X$ and hence $\Gamma_0 \vdash X$. If $D$ is irrelevant, the goal-formula condition guarantees that $D$ is quantifier-free; combining $\Gamma_0 \vdash \neg D \to X$ with $\Gamma_0 \vdash D \to X$ (obtained from $\mathrm{IH}_D(4) : D \to D^X$ and $\Gamma_0 \vdash D^X \to X$) via Lemma 2.3 (`lemmas_2_1_to_2_3.2.2`) yields $\Gamma_0 \vdash X$.

4. **Inductive step for universal quantifiers $\forall x\, D$ and $\forall x\, G$**:
   - For a definite formula $\forall x\, D$, equation (4) follows from $\mathrm{IH}_D(4)$ by $\forall$-congruence (`Provable.all_congr`), and equation (3) follows from $\mathrm{IH}_D(3)$, $\forall$-elimination $(\forall x\, D) \to D$ (which yields $\neg D \to \neg\forall x\, D$), and $\forall$-introduction over $x \notin \mathrm{FV}(\neg\forall x\, D \to X)$.
   - For a goal formula $\forall x\, G$, the constructor requires $G$ to be irrelevant, so $\mathrm{IH}_G(5) : G^X \to G$ and $\forall$-congruence immediately yield $(\forall x\, G)^X \to \forall x\, G$, which gives both (5) and (6).

5. **Lemma 3.2 (`lemma_3_2`)**:
   We induct on the list $\vec{G}$. For $\vec{G} = []$, the claim is $X \to X$. For $G :: \vec{G}'$, in context $[G \to \vec{G}' \to X,\, G^X] \mathbin{++} (\vec{G}')^X$, applying equation (6) for $G$ reduces the goal to deriving $G \to X$; assuming $G$, we obtain $\vec{G}' \to X$, apply the induction hypothesis to get $(\vec{G}')^X \to X$, and discharge $(\vec{G}')^X$ from the context via `Provable.ctx_apply_impMany`.

## `BBS2002.theorem_3_3`

*Refined A-Translation for Definite and Goal Formulas (Theorem 3.3)*. Accepted 2026-10-31, submission `c505fc37-611d-43cb-8e2c-fa68bf0973f6`.

We formalize the proof of **Theorem 3.3** (Refined $A$-Translation for Definite and Goal Formulas) from Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, *"Refined program extraction from classical proofs"*, *Annals of Pure and Applied Logic* 114 (2002), pp. 3–25 (Section 3, p. 9):

> **Theorem 3.3.** Assume that for definite formulas $\vec{D}$ and goal formulas $\vec{G}$ we have
> $$Z_0 \vdash \vec{D} \to \forall \vec{y}(\vec{G} \to \bot) \to \bot.$$
> Then we also have
> $$Z^X \vdash \vec{D} \to \forall \vec{y}(\vec{G} \to X) \to X.$$

### Proof Overview

1. **Syntactic $\bot \mapsto X$ Translation of $Z_0$-Derivations into $Z^X$ (`Derivable.substBotProof`, `Provable.substBotProof`)**:
   Since $Z_0$ is pure minimal logic without *ex falso* (`efq` is disabled in `SysConfig.Z0`), replacing every occurrence of $\bot$ in formulas by the distinguished propositional variable $X$ (`substBotWithX`, written $A \mapsto A^X$) and transforming proof terms via `substBotProof` turns any $Z_0$-derivation of $A$ into a $Z^X$-derivation of $A^X$. Key helper lemmas establish:
   - Commutation of `substBotWithX` with capture-avoiding term substitution: $(A[x := t])^X = A^X[x := t]$ (`substFormula_substBotWithX`), relying on the preservation of variable-id bounds (`maxVarIdFormula_substBotWithX`), bound/free variable sets (`allVarsFormula_substBotWithX`, `freeVarsFormula_substBotWithX`), and $\alpha$-renaming (`renameFreeVarFormula_substBotWithX`).
   - Preservation of formula well-typedness (`FormulaWellTyped.substBotWithX`) and $\beta R$-conversion (`FormulaBetaREq.substBotWithX`).
   - Exact tracking of free assumption variables under `substBotProof` (`mem_freeAssumpVars_substBotProof`), ensuring both the eigenspace condition of $\forall$-introduction and the closedness of the resulting $Z^X$-derivation.

   Applying `Provable.substBotProof` to the given $Z_0$-derivation of $\vec{D} \to \forall \vec{y}(\vec{G} \to \bot) \to \bot$ yields:
   $$Z^X \vdash \vec{D}^X \to \forall \vec{y}(\vec{G}^X \to X) \to X.$$

2. **Strengthening Goal Premises via Lemma 3.2 (`Provable.allMany_congr`)**:
   By **Lemma 3.2** (imported from `Theorems.Thm_BBS2002_lemma_3_1_and_3_2`), for any list of goal formulas $\vec{G}$ we have
   $$Z^X \vdash (\vec{G} \to X) \to \vec{G}^X \to X.$$
   Using monotonicity of universal quantification (`Provable.all_congr` and `Provable.allMany_congr`), we obtain
   $$Z^X \vdash \forall \vec{y}(\vec{G} \to X) \to \forall \vec{y}(\vec{G}^X \to X),$$
   and hence by contravariance of implication in the antecedent (`Provable.imp_congr`),
   $$Z^X \vdash \bigl(\forall \vec{y}(\vec{G}^X \to X) \to X\bigr) \to \bigl(\forall \vec{y}(\vec{G} \to X) \to X\bigr).$$

3. **Replacing $\vec{D}^X$ with $\vec{D}$ via Lemma 3.1 (4) (`Provable.impMany_definite_congr`)**:
   By **Lemma 3.1 (4)** (from `Theorems.Thm_BBS2002_lemma_3_1_and_3_2`), every definite formula $D \in \vec{D}$ satisfies $Z^X \vdash D \to D^X$. Inducting along the list $\vec{D}$ with `Provable.imp_congr` (`Provable.impMany_definite_congr`) combines the antecedent implications $Z^X \vdash D_i \to D_i^X$ with the consequent implication from Step 2 to derive
   $$Z^X \vdash \bigl(\vec{D}^X \to \forall \vec{y}(\vec{G}^X \to X) \to X\bigr) \to \bigl(\vec{D} \to \forall \vec{y}(\vec{G} \to X) \to X\bigr).$$
   Applying modus ponens (`Provable.mp`) to the $Z^X$-translated derivation from Step 1 concludes $Z^X \vdash \vec{D} \to \forall \vec{y}(\vec{G} \to X) \to X$.

## `BBS2002.V2.theorem_4_1`

*Soundness of modified realizability (Theorem 4.1, corrected)*. Accepted 2026-11-01, submission `3a1ed386-6405-4d60-9b20-5ad1eef0756c`.

We prove the exact corrected soundness theorem, with the extracted realizer identified with the supplied proof's structural extraction and with every free assumption of the resulting Z derivation traced to a translated free assumption of the original derivation. There are no open theorem dependencies or additional freshness premises in the result.

First, induction on the derivability judgment proves that raw extraction has exactly the shape of the assigned type and is well typed. At the omitted type it is none; at a computational type it is a term. This also identifies extractProgram with extractRaw for derivable proof terms. Conversion preserves the assigned type, so it preserves this argument without changing extraction.

We then prove realizability by induction on the source derivation, initially choosing the comprehension parameters fresh for the source object variables and the variables used to realize assumptions. The induction is formulated using a predicate on permitted free-assumption formulas, which records the exact assumption-tracking conclusion. Implication introduction and elimination correspond to abstraction and application, with omitted arguments handled explicitly. Universal introduction and elimination use capture-avoiding substitution and freshly named formula binders. The conversion case uses the independently proved compatibility of modified realizability with formula conversion and beta-reduction of realizers. The truth, falsity, and ex-falso axioms use their corresponding Z derivations and typed dummy realizers.

For natural-number and Boolean induction, the realizing terms are exactly the primitive recursors specified by extraction. We choose a fresh object index and apply Z induction to the realizability predicate for the source induction formula instantiated at that index. The recursor equations supply the base and successor, or true and false, cases. The resulting proof is converted back to the modified-realizability translation of the original induction axiom. These cases allow arbitrary free comprehension parameters.

A separate support lemma handles variables introduced only by conversion: if a variable is absent from allVarsProof M and M derives B, substituting for that variable in B leaves B unchanged modulo formula conversion. Thus a converted conclusion need not satisfy a false literal free-variable bound. The proof includes the quantifier-elimination case by viewing each atomic term under formula quantifiers as a lambda abstraction and using beta-reduction after application. This support statement supplies the freshness modulo conversion required in the binding cases.

Finally, we remove the temporary freshness restriction on the comprehension term. Induct on a finite list covering its free parameters. Replace a conflicting parameter by a fresh variable of the same type, chosen above all relevant object and assumption identifiers, and apply the induction hypothesis. Close the translated assumptions into a finite implication prefix, substitute the original parameter back using universal introduction and elimination on the closed proof, and reopen the assumptions. A general transport theorem proves that this substitution commutes with modified realizability while changing the comprehension term. The fresh alias leaves the source formulas and the extracted realizer unchanged modulo conversion. Consequently the final theorem permits the original arbitrary comprehension term, even when its free parameters overlap source variables.

All formula-substitution, conversion, typing, context-management, induction, and parameter-restoration lemmas are proved within the submission or its definition imports. The final solution has exactly the published theorem type and uses only the standard Lean axioms propext, Classical.choice, and Quot.sound.

Source: Berger, Buchholz, and Schwichtenberg, Refined program extraction from classical proofs (2002), Section 4 and Theorem 4.1, author's preprint pp. 11–12; https://doi.org/10.1016/S0168-0072(01)00073-2.

## `BBS2002.V2.theorem_5_1`

*Computational content of classical proofs (Theorem 5.1, corrected)*. Accepted 2026-11-01, submission `65af0c42-2403-4b84-8bde-d0fe404dbd39`.

This is a checked reduction of the corrected Theorem 5.1 to BBS2002.V2.theorem_4_1, the corrected realizability soundness theorem. Theorem 4.1 remains open. All other auxiliary proof steps are included in the submitted Lean file. The solution matches the published statement exactly, including its freshness hypotheses and the equation identifying p with successful raw extraction from the supplied proof.

Replacing falsity by X preserves the source derivation and preserves absence of free assumption variables. Soundness therefore supplies a typed realizer of the translated input formula and a closed Z derivation of its modified realizability interpretation. The type assignment for the nested implications and quantifiers shows that this realizer has a program component. Its option equality from soundness identifies that component with the exact raw extraction p; no fallback term is used.

Under the assumptions D, hypothesis (7) supplies the realizability premises for the definite formulas. Repeated implication elimination in modified realizability applies p to precisely the indexed list of supplied realizers, omitting every irrelevant argument. This leaves the premise corresponding to the universally quantified goal implication.

To establish that premise, instantiate hypothesis (9) at the object variables y. Use the goal eliminators in hypothesis (8) successively to replace each ordinary goal premise with its realizability premise. The body obtained is the nested application of the supplied goal combinators to r applied to y. The declared freshness conditions justify universal introduction for the auxiliary realizer variables and for y while retaining D as undischarged assumptions. The combinators are permitted to depend freely on y: the final abstraction binds that dependence.

Capture-avoiding realizability conversion identifies this quantified matrix with the realizability interpretation of the exact term s = λy λw. s1 w1 (... (sm wm (r y)) ...), with omitted realizer arguments and binders handled by the option-indexed representation. Applying the remaining implication gives D → A(p t s), and structural typing proves that p t s has type ν. Empty lists and omitted types are covered by the list inductions.

The required substitution, formula-conversion, and abstraction laws for modified realizability are fully proved in this file. A paired strong induction on formula size establishes conversion compatibility and substitution commutation, using common fresh binders to prevent capture. These laws are independent of the open soundness theorem. Thus the reduction has exactly one open imported theorem, Theorem 4.1.

Source: Berger, Buchholz, and Schwichtenberg, Refined program extraction from classical proofs (2002), Theorem 5.1 and equations (7)–(11), author's preprint pp. 12–13; https://doi.org/10.1016/S0168-0072(01)00073-2.

## `BBS2002.V2.theorem_5_2`

*Uniform realizers with free parameters (Theorem 5.2, corrected)*. Accepted 2026-11-01, submission `0a8d916f-5a11-426f-87de-9a5bec7755a8`.

This is a checked reduction of the corrected Theorem 5.2 to the corrected soundness theorem BBS2002.V2.theorem_4_1 and the already proved BBS2002.lemma_3_1_and_3_2. Theorem 4.1 remains the sole open dependency. The solution has exactly the published conclusion, including the quantifier order that chooses the realizers before the comprehension term and the free-variable support bounds; it does not assume that the realizers are closed.

First we prove a uniform consequence of soundness. A derivation with no free assumption variables can be normalized so that the object-variable support of its extracted term is contained in the free variables of its conclusion: close each extraneous object variable by abstraction followed by application to a closed default term, then relabel assumption identifiers injectively above all object identifiers. These transformations preserve derivability and give the required extraction admissibility. Apply soundness once to select the realizer. Applying soundness at any other comprehension term gives the identical realizer because both option representations equal the same structural extraction. Thus the realizer is independent of the comprehension term.

For a definite formula D, Lemma 3.1 supplies a ZX proof of D → D^X. Uniform soundness gives its realizer and support bound. Since D is an ordinary formula, its assigned type is omitted and its realizability translation is convertible to D; conversion gives the definite half of Theorem 5.2.

For a goal formula G, Lemma 3.1 supplies a ZX proof of G^X → (G → X) → X. Uniform soundness gives a typed realizer s with free variables contained in those of G. Apply the realizability interpretation of implication elimination twice, first to the supplied optional realizer variable w and then to v as a realizer for G → X. Ordinary-formula realizability and the clause for X convert the result to the exact goal-eliminator formula in the statement, with the argument w omitted when its assigned type is omitted.

The substitution and conversion laws needed for implication elimination are proved within this submission, independently of soundness. A formula view records logical shape and encodes enclosing formula binders as term abstractions at atomic leaves; this proves the capture-avoiding formula substitution algebra and binder inversion lemmas. A paired strong induction on formula size then proves that modified realizability respects formula conversion and commutes with substitution for variables fresh for the free comprehension parameters. Common fresh binders reconcile the different names chosen by the translation. These auxiliary laws have only the standard propext and Quot.sound axioms and introduce no open theorem.

Source: Berger, Buchholz, and Schwichtenberg, Refined program extraction from classical proofs (2002), Theorem 5.2 and equations (12)–(13), author's preprint pp. 13–14; https://doi.org/10.1016/S0168-0072(01)00073-2.

## `BBS2002.V2.corollary_5_3`

*Refined program extraction with free parameters (Corollary 5.3, corrected)*. Accepted 2026-11-01, submission `32c9a598-6f4c-425f-98c7-70e2016c00ec`.

This is a conditional derivation of Corollary 5.3 from the corrected Theorems 5.1 and 5.2. Those two imported results are open dependencies of the submission.

For definite assumptions and a goal formula, the resulting output satisfies

$$Z\vdash D_1\to\cdots\to D_n\to G[y:=p\,t_1\cdots t_n\,s],\qquad p=\llbracket M^X\rrbracket.$$

Theorem 5.2 supplies one typed realizer for each definite formula and a typed goal realizer, with free variables contained in the corresponding formula. These witnesses are chosen before the classical proof. Choose the auxiliary realizer and value variables fresh for the finite collection of formulas. Form the comprehension term with body G and distinguished variable y, and take the identity function as the initial program r.

The supplied uniform realizer implications give hypotheses (7) and (8) of Theorem 5.1 after adding the definite assumptions. Hypothesis (9) is the identity implication for G, with the identity program's beta redex substituted for y. The proof checks this conversion and all freshness conditions explicitly. In particular, the goal realizer may depend on y, and the outer lambda of the final combinator abstracts this parameter.

Theorem 5.1 now provides the exact successful raw-extraction equation, typing of the output, and its correctness under the comprehension term. Unfolding comprehension application gives the required substitution in G. The formula-realizer support bounds are inherited from Theorem 5.2; the final combinator's type and support are proved directly from its construction. Empty assumption lists and omitted-type realizers are handled by the indexed families and optional application convention.
