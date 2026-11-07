# minimal_logic

This repository holds Lean 4 formalizations of papers by Helmut Schwichtenberg and his coauthors. The goal is to formalize and fully prove all of them here, starting with the six papers below.

## How we work

We finish each paper in this repository before opening a public review on [prove2.me](https://prove2.me). A paper is finished when:

1. its definitions and statements have been checked against the paper, and no counterexample to any of them is known; and
2. every statement, including the main theorem, is proved here without `sorry`.

Only then does it go to prove2.me as a mission for public review, because by then we know the formalization is correct and can be proved. Fixes and new proofs are made here first.

The six papers below began as prove2.me missions, before this rule:

- One paper is finished: fully formalized and proved.
- One has corrected statements, but its theorems are not proved yet.
- The other four contain statements that we know are false. They are kept here as published and will be fixed here.

## Status

| Paper | Lean namespace | State |
|---|---|---|
| Berger, Buchholz & Schwichtenberg 2002, *Refined program extraction from classical proofs* | `BBS2002`, `BBS2002.V2` | **Proved.** All six milestones and the main goal (Corollary 5.3) have accepted proofs. See the [prove2.me mission](https://prove2.me/missions/Refined_Program_Extraction_from_Classical_Proofs). |
| Schwichtenberg 1976, *Definierbare Funktionen im λ-Kalkül mit Typen* | `Schwichtenberg1976V2` | Statements only, with 4 open theorems. V2 fixes variable capture in two helper functions. Its proposal went into prove2.me review on 2026-11-02, before the rule above. |
| Aehlig & Schwichtenberg 2002, *A syntactical analysis of non-size-increasing polynomial time computation* | `AehligSchwichtenberg2002` | **Contains a false statement** (Corollary 4.4). Statements only. |
| Aehlig, Berger, Hofmann & Schwichtenberg 2004, *An arithmetic for non-size-increasing polynomial-time computation* | `ABHS2004` | **Contains a false statement** (Theorem 4.7) and defective definitions. Statements only. |
| Berger & Schwichtenberg 1991, *An inverse of the evaluation functional for typed λ-calculus* | `BergerSchwichtenberg1991` | **Contains false statements** (Lemma 2 and part of Theorem 1) and defective definitions. Statements only. |
| Bellantoni, Niggl & Schwichtenberg 2000, *Higher type recursion, ramification and polynomial time* | `BNS2000` | **Contains a false statement** (Theorem 4.3 / Corollary 4.4) and defective definitions. Statements only. |

These defects are in our formalizations, not in the papers. In two places, though, reading the paper's notation literally caused the defect:

- Aehlig & Schwichtenberg state Corollary 4.4 for every `L(τ) ⊸ L(τ)`. The sentence before it limits the corollary to type-1 functions.
- ABHS 2004 writes the realizer of axiom 16 as `id_ρ`. Read literally, that term has the wrong type.

None of the four papers marked as containing false statements should be built on until it is repaired.

Planned order: Aehlig & Schwichtenberg 2002, which needs the smallest repair, then ABHS 2004, Berger & Schwichtenberg 1991, and BNS 2000. The four open theorems of Schwichtenberg 1976 also still need proofs.

## Known defects

Each defect listed here was found in the audit of 2026-11-02. The full reports are in [`docs/audits/2026-11-02`](docs/audits/2026-11-02). The Lean counterexamples are in [`Audits/`](Audits), and they build with the rest of the repository.

**Aehlig & Schwichtenberg 2002** ([report](docs/audits/2026-11-02/syntactical_nsi-report.txt))
- `corollary_4_4` is false when the elements are themselves lists. A valid program turns a one-entry list into a two-entry list. Proof of the negation: `Audits/AehligSchwichtenberg2002_Corollary44.lean`.
- The planned repair restricts the corollary to `τ = B`, as the paper's text does.
- The prove2.me descriptions of all ten items do not match the Lean code.

**ABHS 2004** ([report](docs/audits/2026-11-02/arithmetic_nsi-report.txt))
- `theorem_4_7` is false. The extracted program for axiom 16 lacks its `U` argument. Proof: `Audits/ABHS2004_Axiom16.lean`.
- Cleaning breaks the typing of list iterators: `Audits/ABHS2004_CleanIterator.lean`.
- `theorem_2_25` and `corollary_4_11` bound syntactic length with coefficient one. That bound is too tight: `Audits/ABHS2004_SizeMeasure.lean`.

**Berger & Schwichtenberg 1991** ([report](docs/audits/2026-11-02/inverse_evaluation-report.txt))
- Extraction can capture a free variable, which refutes `lemma_2` and part of `theorem_1`. Proof: `Audits/BergerSchwichtenberg1991_Extraction.lean`.
- The main theorem assumes combinators and inversion functionals that the paper constructs itself.
- The model definition allows empty environments: `Audits/BergerSchwichtenberg1991_EmptyEnvironment.lean`.

**BNS 2000** ([report](docs/audits/2026-11-02/higher_type-report.txt))
- The evaluator cannot evaluate `(!!0)κκ`, which refutes `theorem_4_3_and_4_4`.
- `TermEquiv` is not transitive, because the terms use named binders without alpha-equivalence. Both proofs: `Audits/BNS2000_Counterexample.lean`.
- Theorems 4.5 and 5.1 leave out the cost of constructing the recursion-free term.

**Schwichtenberg 1976 V2**
- V1's `compTerm` and `iterTerm` could capture a free variable. V2 picks a fresh binder whenever the requested one would capture.
- `Audits/Schwichtenberg1976V2_Freshness.lean` proves that the new binders are fresh. `Audits/Schwichtenberg1976V2_Regression.lean` re-checks the old capture examples and shows that the paper's combinators are syntactically unchanged.
- Design notes: [`docs/Schwichtenberg1976V2`](docs/Schwichtenberg1976V2).

## Layout

The layout follows prove2.me, so every file matches the published item exactly.

| Folder | Contents |
|---|---|
| `Definitions/` | Published definition modules, with no `sorry` |
| `Theorems/` | Published statements. Each is a single theorem ending in `sorry` |
| `Solutions/` | Accepted prove2.me proofs for BBS2002. Each ends in `theorem solution` with the exact target type |
| `Audits/` | Lean counterexamples and checks from the audits |
| `docs/` | Audit reports, the BBS2002 V2 source audit, proof explanations, and [`prove2me-items.json`](docs/prove2me-items.json), which maps each file to its prove2.me ID |

The files were downloaded from prove2.me on 2026-11-07. From now on this repository is the source of truth, and prove2.me is updated only when a paper is finished. The original BBS2002 statements of Theorems 4.1, 5.1, 5.2 and Corollary 5.3 are deprecated on prove2.me and are not included. Their V2 replacements are included. Likewise, Schwichtenberg 1976 V1 has been replaced by V2.

## Building

The project needs Lean `v4.33.1` and Mathlib `0df444a`, both pinned in `lean-toolchain` and `lakefile.lean`.

```sh
lake exe cache get
lake build Definitions Theorems Solutions Audits
```

On 2026-11-07 this build passed (168 jobs). The only `sorry`s are in the 41 statement files in `Theorems/`: 34 open targets, plus the 7 BBS2002 statements whose proofs are in `Solutions/`.

As on prove2.me, a proof may cite another target by importing its statement from `Theorems/`. The axioms of each `solution` are:

| Proof | Cites | Axioms |
|---|---|---|
| `Sol_BBS2002_lemmas_2_1_to_2_3` | none | `propext`, `Quot.sound` |
| `Sol_BBS2002_V2_theorem_4_1` | none | `propext`, `Classical.choice`, `Quot.sound` |
| `Sol_BBS2002_lemma_3_1_and_3_2` | Lemmas 2.1–2.3 | the above, plus `sorryAx` from the cited statement |
| `Sol_BBS2002_theorem_3_3` | Lemmas 3.1/3.2 | the above, plus `sorryAx` from the cited statement |
| `Sol_BBS2002_V2_theorem_5_1` | Theorem 4.1 | the above, plus `sorryAx` from the cited statement |
| `Sol_BBS2002_V2_theorem_5_2` | Theorem 4.1, Lemmas 3.1/3.2 | the above, plus `sorryAx` from the cited statements |
| `Sol_BBS2002_V2_corollary_5_3` | Theorems 5.1, 5.2 | the above, plus `sorryAx` from the cited statements |

None of the proof files contains a `sorry`, so `sorryAx` enters only through a cited statement. Every cited statement is proved by another file in `Solutions/`. The files cannot be linked into a single module, because each one repeats its own helper lemmas and is named `solution`.

## Sources

The papers themselves are not included. They are:

- U. Berger, W. Buchholz, H. Schwichtenberg. Refined program extraction from classical proofs. *Annals of Pure and Applied Logic* 114 (2002) 3–25. [doi:10.1016/S0168-0072(01)00073-2](https://doi.org/10.1016/S0168-0072(01)00073-2)
- H. Schwichtenberg. Definierbare Funktionen im λ-Kalkül mit Typen. *Archiv für mathematische Logik und Grundlagenforschung* 17 (1975/76) 113–114. [doi:10.1007/BF02011242](https://doi.org/10.1007/BF02011242)
- K. Aehlig, H. Schwichtenberg. A syntactical analysis of non-size-increasing polynomial time computation. *ACM Transactions on Computational Logic* 3(3) (2002) 383–401. [doi:10.1145/507382.507386](https://doi.org/10.1145/507382.507386)
- K. Aehlig, U. Berger, M. Hofmann, H. Schwichtenberg. An arithmetic for non-size-increasing polynomial-time computation. *Theoretical Computer Science* 318(1–2) (2004) 3–27. [doi:10.1016/j.tcs.2003.10.023](https://doi.org/10.1016/j.tcs.2003.10.023)
- U. Berger, H. Schwichtenberg. An inverse of the evaluation functional for typed λ-calculus. *LICS 1991*, 203–211. [doi:10.1109/LICS.1991.151645](https://doi.org/10.1109/LICS.1991.151645)
- S. Bellantoni, K.-H. Niggl, H. Schwichtenberg. Higher type recursion, ramification and polynomial time. *Annals of Pure and Applied Logic* 104 (2000) 17–30. [doi:10.1016/S0168-0072(00)00006-3](https://doi.org/10.1016/S0168-0072(00)00006-3)

## License

Apache License 2.0. Public contributions on prove2.me use the same license.
