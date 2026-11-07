import Theorems.Thm_Schwichtenberg1976V2_normal_subterm_structure
import Proofs.Schwichtenberg1976V2.NormalSubterms
import Theorems.Thm_Schwichtenberg1976V2_subterm_polynomial_lemma
import Proofs.Schwichtenberg1976V2.SubtermPolynomial
import Theorems.Thm_Schwichtenberg1976V2_combinators_and_sufficiency
import Proofs.Schwichtenberg1976V2.Sufficiency

/-!
# The proofs prove exactly the published statements

Each `example` assigns a proof from `Proofs/` to the type of the published prove2.me
statement in `Theorems/`, so any difference between the two statements is a type error.
-/

example : type_of% @Schwichtenberg1976V2.normal_subterm_structure :=
  @Schwichtenberg1976V2.Proofs.normal_subterm_structure

example : type_of% @Schwichtenberg1976V2.subterm_polynomial_lemma :=
  @Schwichtenberg1976V2.Proofs.subterm_polynomial_lemma

example : type_of% @Schwichtenberg1976V2.combinators_and_sufficiency :=
  @Schwichtenberg1976V2.Proofs.combinators_and_sufficiency
