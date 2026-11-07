import Proofs.Schwichtenberg1976V2.Sufficiency
import Proofs.Schwichtenberg1976V2.Piecewise
import Proofs.Schwichtenberg1976V2.Semantics
import Proofs.Schwichtenberg1976V2.SubtermPolynomial
import Lean

/-!
Lists every declaration in `Schwichtenberg1976V2.Proofs` that depends on `Classical.choice`,
followed by the axioms of each milestone. Run with `lake env lean scripts/ClassicalAudit.lean`.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, _) in env.constants.toList do
    if (`Schwichtenberg1976V2.Proofs).isPrefixOf n && !n.isInternal then
      names := names.push n
  let mut bad : Array Name := #[]
  for n in names do
    let axs ← liftCoreM (collectAxioms n)
    if axs.contains ``Classical.choice then
      bad := bad.push n
  logInfo m!"{names.size} declarations, {bad.size} use Classical.choice:\n{bad.qsort Name.lt}"
