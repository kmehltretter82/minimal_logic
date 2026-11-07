# Audit of 2026-11-02

An agent wrote this audit of five prove2.me proposals. It is not a human review. Start with `REVIEW.txt`, which summarizes all five. The per-mission reports are:

| Report prefix | Paper |
|---|---|
| `syntactical_nsi` | Aehlig & Schwichtenberg 2002 |
| `arithmetic_nsi` | Aehlig, Berger, Hofmann & Schwichtenberg 2004 |
| `inverse_evaluation` | Berger & Schwichtenberg 1991 |
| `higher_type` | Bellantoni, Niggl & Schwichtenberg 2000 |
| `extended_polynomials` | Schwichtenberg 1976 (version 1) |

The reports cite paths from the audit's working folder. They map to this repository as follows:

| Path in the reports | File in this repository |
|---|---|
| `code/NN_<Name>.lean` | `Definitions/Def_<Name>.lean` or `Theorems/Thm_<Name>.lean` |
| `syntactical_nsi/counterexample.lean` | `Audits/AehligSchwichtenberg2002_Corollary44.lean` |
| `arithmetic_nsi/Axiom16Audit.lean` | `Audits/ABHS2004_Axiom16.lean` |
| `arithmetic_nsi/CleanIteratorAudit.lean` | `Audits/ABHS2004_CleanIterator.lean` |
| `arithmetic_nsi/SizeMeasureAudit.lean` | `Audits/ABHS2004_SizeMeasure.lean` |
| `inverse_evaluation/SyntaxAudit.lean` | `Audits/BergerSchwichtenberg1991_Extraction.lean` |
| `inverse_evaluation/EmptyEnvironmentAudit.lean` | `Audits/BergerSchwichtenberg1991_EmptyEnvironment.lean` |
| `higher_type/Counterexample.lean` | `Audits/BNS2000_Counterexample.lean` |

Two files from the audit are not included:

- `extended_polynomials/UtilityCapture.lean` targets the replaced version 1 of the 1976 definitions. Its capture examples are re-checked against V2 in `Audits/Schwichtenberg1976V2_Regression.lean`.
- `arithmetic_nsi/counterexamples.lean` repeats `ABHS2004_Axiom16.lean` with the definitions inlined.

Downloaded copies of the papers are also left out. Build the counterexamples with `lake build Audits`.
