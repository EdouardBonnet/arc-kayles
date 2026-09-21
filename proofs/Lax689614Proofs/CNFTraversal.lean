import Lax689614Proofs.UnaryCode
import Lax689614Proofs.ParserLengths
import Lax429075Proofs.EmitFormula

namespace Lax689614Proofs.CNFTraversal

open Lax429075 CNF Encoding
open Lax434930.PolynomialTime

/-- Advance one literal in a clause; a clause terminator is a fixed point. -/
def literalStep (w : Word) : Word :=
  if w.head?.getD false then w.drop (((w.drop 1).takeWhile id).length + 3) else w

theorem literalStep_length (w : Word) : (literalStep w).length ≤ w.length := by
  unfold literalStep
  split_ifs <;> simp

theorem literalStep_nil (tail : Word) : literalStep (encodeClause [] ++ tail) = encodeClause [] ++ tail := rfl

theorem literalStep_cons (l : Literal) (C : Clause) (tail : Word) :
    literalStep (encodeClause (l :: C) ++ tail) = encodeClause C ++ tail := by
  simp only [encodeClause, encodeList, List.cons_append, List.append_assoc,
    literalStep, List.head?_cons, Option.getD_some, Bool.true_eq, ↓reduceIte,
    List.drop_succ_cons, List.drop_zero, encodeLiteral, encodeNat]
  simp [takeWhile_unary_prefix, List.drop_append, Nat.add_assoc]

theorem literalStep_iterate (C : Clause) (tail : Word) (j : ℕ) :
    literalStep^[j] (encodeClause C ++ tail) = encodeClause (C.drop j) ++ tail := by
  induction j generalizing C with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    cases C with
    | nil => simp only [literalStep_nil, ih, List.drop_nil]
    | cons l C => rw [literalStep_cons, ih, List.drop_succ_cons]

theorem clause_length_le (C : Clause) : C.length ≤ (encodeClause C).length := by
  induction C with
  | nil => simp
  | cons l C ih => simp only [encodeClause, encodeList, List.length_cons, List.length_append] at *; omega

def clauseStep (w : Word) : Word := (literalStep^[w.length] w).drop 1

theorem clauseStep_correct (C : Clause) (tail : Word) :
    clauseStep (encodeClause C ++ tail) = tail := by
  rw [clauseStep, literalStep_iterate]
  have hd : C.drop (encodeClause C ++ tail).length = [] := by
    apply List.drop_eq_nil_of_le
    have := clause_length_le C
    simp only [List.length_append]; omega
  rw [hd]
  rfl

theorem iterate_length {f : Word → Word} (hf : ∀ w, (f w).length ≤ w.length) (j : ℕ) (w : Word) :
    (f^[j] w).length ≤ w.length := by
  induction j generalizing w with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply]; exact (ih _).trans (hf w)

theorem clauseStep_length (w : Word) : (clauseStep w).length ≤ w.length :=
  (by simp only [clauseStep, List.length_drop]; exact
    (Nat.sub_le _ _).trans (iterate_length literalStep_length _ _))

def formulaStep (w : Word) : Word :=
  if w.head?.getD false then clauseStep (w.drop 1) else w

theorem formulaStep_length (w : Word) : (formulaStep w).length ≤ w.length := by
  unfold formulaStep
  split_ifs
  · exact (clauseStep_length _).trans (by simp)
  · rfl

theorem formulaStep_nil : formulaStep (encodeCNF []) = encodeCNF [] := rfl

theorem formulaStep_cons (C : Clause) (F : Formula) :
    formulaStep (encodeCNF (C :: F)) = encodeCNF F := by
  change clauseStep (encodeClause C ++ encodeCNF F) = _
  exact clauseStep_correct C _

theorem formulaStep_iterate (F : Formula) (j : ℕ) :
    formulaStep^[j] (encodeCNF F) = encodeCNF (F.drop j) := by
  induction j generalizing F with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    cases F with
    | nil => simp only [formulaStep_nil, ih, List.drop_nil]
    | cons C F => rw [formulaStep_cons, ih, List.drop_succ_cons]

theorem formula_length_le (F : Formula) : F.length ≤ (encodeCNF F).length := by
  induction F with
  | nil => simp
  | cons C F ih => simp only [encodeCNF, encodeList, List.length_cons, List.length_append] at *; omega

end Lax689614Proofs.CNFTraversal
