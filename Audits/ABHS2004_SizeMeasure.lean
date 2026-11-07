import Definitions.Def_ABHS2004_TermSystem

namespace ArithmeticSizeAudit
open ABHS2004

-- Constructor representations of n units and n true booleans, with the same
-- n distinct diamond variables. The cert below checks sizes, not correctness
-- of a list-map evaluator or the full negation of Theorem 2.25.
def dataList (ρ : Ty) (element : Term) : Nat → Term
  | 0 => .const (.nil ρ)
  | n + 1 => .app (.app (.app (.const (.cons ρ)) (.var ⟨n, .diamond⟩)) element)
      (dataList ρ element n)

def input (n : Nat) : Term := dataList .unit (.const .eps) n
def output (n : Nat) : Term := dataList Ty.bool Term.tt n

theorem list_length (ρ : Ty) (element : Term) (n : Nat) :
    termLength (dataList ρ element n) = (2 + termLength element) * n + 1 := by
  induction n with
  | zero => simp [dataList, termLength]
  | succ n ih => simp [dataList, termLength, ih, Nat.mul_succ]; omega

theorem input_length (n : Nat) : termLength (input n) = 3 * n + 1 := by
  exact list_length .unit (.const .eps) n

theorem output_length (n : Nat) : termLength (output n) = 4 * n + 1 := by
  exact list_length Ty.bool Term.tt n

theorem no_additive_syntax_length_bound :
    ∀ k : Nat, ∃ n : Nat, termLength (input n) + k < termLength (output n) := by
  intro k
  refine ⟨k + 1, ?_⟩
  rw [input_length, output_length]
  omega

#print axioms input_length
#print axioms output_length
#print axioms no_additive_syntax_length_bound
end ArithmeticSizeAudit
