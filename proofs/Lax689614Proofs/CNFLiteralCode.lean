import Lax689614Proofs.CNFTraversalCode
import Lax689614Proofs.ListTraversal
import Lax689614Proofs.ByskovEncoding
import Lax689614Proofs.AlternatingNormalization

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CNFTraversal

open Lax429075 CNF Encoding
open Lax434930.PolynomialTime
open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

def bindTest {I : Type} (c : Code I) (t : Test (Option I)) : Test I where
  value a := t.value (extend a (c.eval a))
  code := .bind c t.code
  correct a := t.correct _

def literalIndex {I : Type} (word : I) : Number I where
  value a := ((a word).drop 1 |>.takeWhile id).length
  code := .bind (dropCode word (.constant 1)) (MachineCode.leadingOnes none).code
  correct a := by simp [Code.eval, dropCode_eval, Number.constant, Number.correct,
    MachineCode.leadingOnes_value, extend]

theorem literalIndex_cons (l : Literal) (C : Clause) (tail : Word) :
    ((encodeClause (l :: C) ++ tail).drop 1 |>.takeWhile id).length = l.index := by
  simp [encodeClause, encodeList, encodeLiteral, encodeNat, List.append_assoc, takeWhile_unary_prefix]

theorem literalSign_cons (l : Literal) (C : Clause) (tail : Word) :
    ((encodeClause (l :: C) ++ tail)[l.index + 2]?).getD false = l.positive := by
  simp [encodeClause, encodeList, encodeLiteral, encodeNat, List.append_assoc,
    List.getElem?_append_right, List.getElem?_replicate]

def literalAddress (flags : Word) (l : Literal) : ℕ :=
  4 * l.index + (if (flags[l.index]?).getD false then 0 else 2) + (if l.positive then 1 else 0)

def addressNumber {I : Type} (flags word : I) : Number I :=
  let index := literalIndex word
  (((Number.constant 4).mul index).add
    (Number.choose (Test.input flags index) (.constant 0) (.constant 2))).add
      (Number.choose (Test.input word (index.add (.constant 2))) (.constant 1) (.constant 0))

theorem addressNumber_cons {I : Type} (flags word : I) (a : I → Word) (l : Literal) (C : Clause) (tail : Word)
    (hw : a word = encodeClause (l :: C) ++ tail) :
    (addressNumber flags word).value a = literalAddress (a flags) l := by
  simp only [addressNumber, Number.add, Number.mul, Number.constant, Number.choose, Test.input,
    literalIndex, hw, literalIndex_cons, literalSign_cons, literalAddress]

def headMatches {I : Type} (flags word : I) (target : Number I) : Test I :=
  (Test.input word (.constant 0)).and
    ((Test.lt (literalIndex word) (.length flags)).and (Test.eq (addressNumber flags word) target))

theorem headMatches_nil {I : Type} (flags word : I) (target : Number I) (a : I → Word) (tail : Word)
    (hw : a word = encodeClause [] ++ tail) : (headMatches flags word target).value a = false := by
  simp [headMatches, Test.and, Test.input, Number.constant, hw, encodeClause, encodeList]

theorem headMatches_cons {I : Type} (flags word : I) (target : Number I) (a : I → Word)
    (l : Literal) (C : Clause) (tail : Word) (hw : a word = encodeClause (l :: C) ++ tail) :
    (headMatches flags word target).value a = true ↔
      l.index < (a flags).length ∧ literalAddress (a flags) l = target.value a := by
  simp only [headMatches, Test.and, Bool.and_eq_true, Test.lt, Test.eq_value, decide_eq_true_eq,
    Number.length, addressNumber_cons flags word a l C tail hw]
  have hi : (literalIndex word).value a = l.index := by
    simp only [literalIndex, hw, literalIndex_cons]
  rw [hi]
  simp [Test.input, Number.constant, hw, encodeClause, encodeList]

def clauseMatches {I : Type} (flags word : I) (target : Number I) : Test I :=
  Test.exists (.length word)
    (bindTest (literalSuffixCode (some word) (.length none))
      (headMatches (some (some flags)) none (target.rename (some ∘ some))))

theorem clauseMatches_correct {I : Type} (flags word : I) (target : Number I) (a : I → Word)
    (C : Clause) (tail : Word) (hw : a word = encodeClause C ++ tail) :
    (clauseMatches flags word target).value a = true ↔
      ∃ l ∈ C, l.index < (a flags).length ∧ literalAddress (a flags) l = target.value a := by
  rw [clauseMatches, Test.exists_true]
  simp only [Number.length, bindTest, literalSuffixCode_eval, extend,
    Option.elim_some, Option.elim_none, List.length_replicate, hw, literalStep_iterate]
  let P (D : Clause) := (headMatches (some (some flags)) none (target.rename (some ∘ some))).value
    (extend (extend a []) (encodeClause D ++ tail)) = true
  have he (j : ℕ) (D : Clause) :
      (headMatches (some (some flags)) none (target.rename (some ∘ some))).value
        (extend (extend a (List.replicate j true)) (encodeClause D ++ tail)) = true ↔ P D := Iff.rfl
  change (∃ j < (encodeClause C ++ tail).length,
    (headMatches (some (some flags)) none (target.rename (some ∘ some))).value
      (extend (extend a (List.replicate j true)) (encodeClause (C.drop j) ++ tail)) = true) ↔ _
  simp only [he]
  apply exists_heads P (fun l => l.index < (a flags).length ∧ literalAddress (a flags) l = target.value a)
  · have hn := headMatches_nil (some (some flags)) none (target.rename (some ∘ some))
      (extend (extend a []) (encodeClause [] ++ tail)) tail rfl
    unfold P
    rw [hn]
    decide
  · intro l D
    exact headMatches_cons (some (some flags)) none (target.rename (some ∘ some))
      (extend (extend a []) (encodeClause (l :: D) ++ tail)) l D tail rfl
  · have := clause_length_le C
    simp only [List.length_append]; omega

end Lax689614Proofs.CNFTraversal
