# Roadmap

This file plans the repository's work. It draws on `ideas.txt` and `further_ideas.txt` and on what the repository has already proved. Last updated 2026-11-07.

## The idea in one sentence

Take a mathematical proof about a system, and get from it a program that runs, together with Lean-checked guarantees: that the program is correct, how much input information it needs, and how much it costs to run.

Minimal logic is the base layer for this. It has implication, conjunction and ∀/∃, but no rule `⊥ → P`. Most of the power comes from what we add on top of it, one piece at a time: arithmetic, induction and coinduction, realizability, translations of classical proofs, resource restrictions, analysis and probability. The repository's distinctive contribution can be a clear, verified account of what each addition buys computationally.

## Principles

- **Constructive proofs.** Every proof uses at most `propext` and `Quot.sound`, never `Classical.choice`. `scripts/ClassicalAudit.lean` checks this. The one exception is the BBS2002 proofs, which were accepted on prove2.me before this rule and stay classical.
- **Finish here, then publish.** A formalization goes to prove2.me for public review only after it has been checked against the paper and fully proved in this repository.
- **Faithful to the source.** Every formal statement is checked against the paper. Wherever the formalization departs from the paper, the departure is written down.
- **Honest status.** Known false statements stay visible and labelled until they are repaired.

## Where we are

| Paper | State |
|---|---|
| Berger, Buchholz & Schwichtenberg 2002: refined program extraction from classical proofs | Proved (prove2.me solutions; these use `Classical.choice`) |
| Schwichtenberg 1976: λ-definable functions are the extended polynomials | Proved, constructively, in `Proofs/` |
| Aehlig & Schwichtenberg 2002: non-size-increasing polynomial time | One false statement (Cor 4.4), small repair |
| Aehlig, Berger, Hofmann & Schwichtenberg 2004: an arithmetic for non-size-increasing polynomial time | One false statement and two definition defects, medium repair |
| Berger & Schwichtenberg 1991: an inverse of the evaluation functional | False extraction lemma, and the main theorem assumes too much, large repair |
| Bellantoni, Niggl & Schwichtenberg 2000: higher type recursion and polynomial time | False evaluator theorem, and the term syntax needs α-equivalence, largest repair |

Each of the four remaining repairs is also the first step towards one of the "wild dreams" below. That gives the Schwichtenberg work a direction beyond the repairs themselves.

## Wild dreams

Each dream below comes with:

- why the minimal-logic tradition is relevant;
- the first Lean experiment that would test it;
- a reality check, meaning what minimal logic alone does not provide.

### For programs

**P1. Proofs that run.** Every proof in a supported fragment of arithmetic becomes a verified program, and a classical existence proof becomes an algorithm.

- **Why us:** BBS2002 Theorem 4.1, already proved here, is soundness of modified realizability, and Corollary 5.3 is the refined A-translation. That is a verified extraction pipeline for one calculus.
- **First experiment:** pick a classical proof of an existence statement of the form ∀∃ (for example, Bézout coefficients or a minimum of a list). Build its derivation in the BBS2002 syntax, run the extracted System T program with `#eval`, and show the Lean theorem that the output is correct.
- **Reality check:** extraction works only for restricted formula classes. No procedure turns every classical existence proof into a program; that would decide the halting problem.

**P2. Programs with resource bounds by construction.** If a program type-checks in the restricted calculus, Lean certifies a polynomial bound on its running time.

- **Why us:** this is what Aehlig & Schwichtenberg 2002, ABHS 2004 and BNS 2000 prove. Their ⋄ tokens make resources explicit: a program cannot output more than it is given. Repairing these three papers builds the dream.
- **First experiment:** repair Corollary 4.4 of Aehlig & Schwichtenberg 2002, then prove the step bound of Corollary 4.9 for a concrete list program such as insertion sort.
- **Reality check:** the bound comes from the linearity and ramification restrictions, not from minimal logic itself. A correctness proof and an efficiency proof are separate theorems.

**P3. A normalizer extracted from a proof.** A verified normalization-by-evaluation algorithm for typed λ-terms.

- **Why us:** Berger & Schwichtenberg 1991, *An inverse of the evaluation functional*, is where normalization by evaluation began, so repairing it gives the normalizer. The 1976 proof here already contains a set-theoretic semantics and a Kripke logical relation, which are the right tools.
- **First experiment:**
  - Fix the extraction lemma (Lemma 2) with fresh-variable tracking.
  - Build the inversion functionals Φ and Ψ, which the paper constructs and the current formalization merely assumes.
  - Run the normalizer on example terms.
- **Reality check:** termination is not efficiency. Deciding whether two simply typed terms have the same normal form has non-elementary worst-case complexity.

**P4. Computing with infinite data.** A program computes on exact real numbers given as infinite digit streams, and Lean proves both the answer and how many input digits it reads.

- **Why us:** Schwichtenberg and Wiesnet extract stream algorithms for exact reals from proofs about coinductive predicates, and Köpp and Schwichtenberg make the amount of lookahead part of the specification.
- **First experiment:** average two signed-digit streams. Prove that `n` output digits need at most `n + 1` digits of each input, that emitted digits never change, and that every finite request terminates.
- **Reality check:** "the output depends only on a finite prefix" is a mathematical fact; "the implementation reads only that prefix" is a separate theorem about the evaluator.

### For physics

**F1. Certified prediction from finite information.** Before running a prediction, the tool says how precisely the initial state must be known for a requested output accuracy, and then computes a certified enclosure of the answer.

- **First experiment:** the logistic map `f(x) = 4x(1 − x)` on `[0, 1]`.
  - The bound `|f(x) − f(y)| ≤ 4|x − y|` gives `|fᴺ(x) − fᴺ(y)| ≤ 4ᴺ |x − y|`. So `k` bits of output accuracy after `N` steps need `b ≥ k + 2N` bits of input accuracy; for example, 80 bits for 20 bits after 30 steps.
  - Prove this over the rationals, which keeps it constructive. Then evaluate exact rational intervals with `#eval` to get certified enclosures, reporting "not certified" when the input is too coarse.
- **Next steps:**
  - Local bounds instead of global ones.
  - Rounding error.
  - Precision requirements that are derived from the proof rather than stated by hand.
  - A connection to P4's streams.
- **Reality check:** a certificate is a statement about the model. Three sources of uncertainty stay separate: the measurement error (an assumption), the numerical error (proved), and the gap between model and reality (empirical).

**F2. Finite stability from infinite convergence.** A theorem only says "`xₙ` converges", yet its proof yields a computable bound on how far to search for a stretch where the sequence varies by less than `ε`. This is proof mining and metastability.

- **Why us:** metastability statements have the ∀∃ form that refined A-translation (BBS2002) handles, so the extraction machinery already here applies.
- **First experiment:** the monotone convergence theorem for bounded sequences. Prove the metastable form with an explicit bound function, and extract that bound from a classical proof with the BBS2002 pipeline.
- **Long term:** one substantial convergence theorem from analysis or stochastic approximation, with its quantitative content extracted and verified.
- **Reality check:** the obtainable result is often metastability, not a convergence rate. The extraction method has to match the theorem.

**F3. Logic and quantum constraints.** This is the most surprising connection.

- **The connection:**
  - For the fragment with only implication and conjunction, minimal negation `¬A := A → R` (for an arbitrary object `R`) has a precise meaning in categories.
  - Collapse theorems (Joyal's lemma) say that adding a dualizing negation to a cartesian closed category forces it to be a preorder: at most one arrow between any two objects.
  - Abramsky relates a similar collapse to quantum no-cloning: uniform copying makes a compact category degenerate.
- **First experiment:**
  - Formalize the category semantics of this fragment with an arbitrary `R`, and prove it sound.
  - Then state and prove a Joyal-type collapse in Mathlib's category theory, first working out exactly which hypotheses on `R` are needed; the idea files state it loosely.
- **Bridge to P2:** minimal logic proves `A → A ∧ A`, so it can copy freely, and quantum states cannot be copied. The affine ⋄-resources of the polynomial-time papers are the resource-aware side of this contrast. That contrast is a structural analogy to make precise, not an identity.
- **Reality check:** "minimal quantum logic" in the quantum-logic literature means orthologic, not Johansson's minimal logic, so the two must not be conflated.

**F4. Reasoning without explosion.** A contradiction in one calibration assumption should not let you prove an unrelated prediction.

- **First experiment:** an evidence checker that keeps source assumptions explicit and records which conclusions depend on a conflict.
- **Reality check:** in minimal logic, `⊥` still proves every negation `¬A`, so a serious evidence logic probably needs a paraconsistent system or source annotations. This is a small, separate line of work.

### Also in algebra

**A1. Finite certificates from proofs about infinite objects.** A proof may use maximal ideals or Zorn's lemma and still yield a finite, checkable certificate, for example a Nullstellensatz identity `Σ gᵢfᵢ = 1` showing that polynomial equations have no common solution.

- **First experiment:** a small certificate checker, next to the interpretation of one abstract proof (the universal Krull algorithm of Powell, Schuster and Wiesnet).

## Limits that shape the project

- **Proof search is hard even in tiny fragments.** Validity of implicational propositional logic is PSPACE-complete, and there minimal and intuitionistic logic coincide.
- **Normalization can be expensive.** Comparing normal forms of simply typed terms is non-elementary in the worst case.
- **Classical proofs do not always give programs.** No uniform extraction exists for all of them.
- **Models are not reality.** A certified answer about a model says nothing about the model's fit to the world.

These limits are why the plan aims at specific, well-chosen classes of proofs, with every assumption visible.

## Phases

### Phase 0: finish the Schwichtenberg base (now)

1. Package the 1976 proofs as single-file prove2.me solutions, ready for when its review completes.
2. Repair Aehlig & Schwichtenberg 2002. This is the first step of P2.
3. Repair ABHS 2004 (P2), Berger & Schwichtenberg 1991 (P3), and BNS 2000 (P2).
4. The BBS2002 proofs stay classical: they use `Classical.choice` and are already accepted on prove2.me (decided 2026-11-07).

### Phase 1: the minimal logic core

1. An explicit object language: formulas, derivations, and a checker.
2. Separation results:
   - `⊥ → P` is not derivable, shown with a Kripke countermodel;
   - `⊥ → ¬A` is derivable;
   - a table comparing minimal, intuitionistic and classical logic.
3. A small certified explorer: given a formula, return a checked derivation, a checked countermodel, or "unknown". This is the first public tool.

### Phase 2: the first two wild-dream demos

1. P1 "proofs that run": a classical proof, then a program, then a correct output, using the BBS2002 pipeline.
2. F1 "certified prediction": precision bounds and certified enclosures for the logistic map.

### Phase 3: computing with structure

1. P4 exact reals: signed-digit averaging with a proved lookahead bound.
2. P3 normalization by evaluation, from the repaired Berger & Schwichtenberg 1991.
3. P2 polynomial time by construction, from the repaired polynomial-time papers.

### Phase 4: research directions

1. F2 proof mining: metastability from one convergence proof.
2. F3 logic and quantum: categorical semantics, collapse theorems, and the copying contrast with resource-aware calculi.
3. A1 algebra certificates.

## Suggested first steps

1. **Phase 0, item 2:** repair Aehlig & Schwichtenberg 2002. This is the smallest repair, and it starts P2.
2. **F1, first experiment:** the logistic-map precision theorem over the rationals. It is quick, easy to understand, and the first physics result.
3. **Phase 1, item 2:** the `⊥ → P` separation theorem. It gives the repository's name a theorem.
4. **P1, first experiment:** run one program extracted with BBS2002. This shows the whole pipeline working.

## Reading list

These pointers come from the idea files and have **not yet been checked**. Confirm each one before citing it.

- **Extraction and exact reals:**
  - Schwichtenberg & Wiesnet, extraction of exact-real stream algorithms (LMCS, 2021).
  - Köpp & Schwichtenberg, lookahead (TCS 943, 2023).
  - Wiesnet, number-theory extraction (2025/26) and the limits of the refined A-translation (2026).
  - Berger, Berghofer, Letouzey & Schwichtenberg, program extraction from normalization proofs.
- **Minimal logic:**
  - Johansson 1937, *Der Minimalkalkül*.
  - Ishihara & Schwichtenberg 2016, *Embedding classical in minimal implicational logic*.
  - Schwichtenberg & Senjak 2013, *Minimal from classical proofs*.
  - Fellin, *A Unifying Conservation Theorem* (CSL 2026).
  - Saraiva & Haeusler, minimal-logic proofs to Boolean circuits in Lean (2026).
- **Proof mining:**
  - Avigad, Gerhardy & Towsner, local stability of ergodic averages.
  - Neri & Pischke, proof mining and probability theory (2025).
  - Neri & Powell, quantitative Robbins–Siegmund.
  - Pischke, nonlinear semigroups (2025).
- **Logic and physics:**
  - Abramsky, no-cloning in categorical quantum mechanics.
  - Joyal's lemma, in Lambek & Scott.
  - Aguilera & Massas, *Constructive quantum logics* (2026).
  - Immler, verified ODE solver (Lorenz attractor).
- **Algebra:**
  - Coste, Lombardi & Roy, effective Nullstellensätze.
  - Powell, Schuster & Wiesnet, a universal algorithm for Krull's theorem.
- **Limits:**
  - Statman, PSPACE-completeness of intuitionistic implicational logic.
  - Nguyên 2024, TOWER-completeness of normal-form equality for safe λ-terms.
