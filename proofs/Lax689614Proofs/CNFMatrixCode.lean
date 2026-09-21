import Lax689614Proofs.CNFMatrix

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CNFTraversal

open Lax429075 CNF Encoding
open Lax434930.PolynomialTime
open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

theorem extend_skip_two {I : Type} (a : I → Word) (x y z : Word) :
    extend (extend (extend a x) y) z ∘ Option.map (some ∘ some) = extend a z := by
  funext i; cases i <;> rfl

def formulaHeadCode {I : Type} (word : I) (body : Code (Option I)) : Code I :=
  .branch word (.bind (dropCode word (.constant 1)) body) (.literal [])

def formulaTraverseCode {I : Type} (word : I) (body : Code (Option I)) : Code I :=
  Code.loop (.length word) (.bind (formulaSuffixCode (some word) (.length none))
    (formulaHeadCode none (body.rename (Option.map (some ∘ some)))))

theorem formulaTraverseCode_eval {I : Type} (word : I) (body : Code (Option I)) (a : I → Word)
    (F : Formula) (hw : a word = encodeCNF F) (g : Clause → Word)
    (hb : ∀ C tail, body.eval (extend a (encodeClause C ++ tail)) = g C) :
    (formulaTraverseCode word body).eval a = F.flatMap g := by
  rw [formulaTraverseCode, Code.eval_loop]
  simp only [Number.length, Code.eval, formulaSuffixCode_eval, Number.length, extend,
    Option.elim_some, Option.elim_none, List.length_replicate, hw, formulaStep_iterate]
  let f (D : Formula) := if (encodeCNF D).head?.getD false then
    body.eval (extend a ((encodeCNF D).drop 1)) else []
  have he (j : ℕ) (D : Formula) :
      (formulaHeadCode none (body.rename (Option.map (some ∘ some)))).eval
        (extend (extend a (List.replicate j true)) (encodeCNF D)) = f D := by
    simp only [formulaHeadCode, Code.eval, dropCode_eval, Number.constant,
      Code.eval_rename, extend_skip_two]
    rfl
  change (List.range (encodeCNF F).length).flatMap (fun j =>
    (formulaHeadCode none (body.rename (Option.map (some ∘ some)))).eval
      (extend (extend a (List.replicate j true)) (encodeCNF (F.drop j)))) = _
  simp only [he]
  apply range_heads f g
  · rfl
  · intro C D
    exact hb C (encodeCNF D)
  · exact formula_length_le F

def clauseCountCode {I : Type} (word : I) : Code I := formulaTraverseCode word (.literal [true])

theorem clauseCountCode_eval {I : Type} (word : I) (a : I → Word)
    (F : Formula) (hw : a word = encodeCNF F) :
    (clauseCountCode word).eval a = List.replicate F.length true := by
  rw [clauseCountCode, formulaTraverseCode_eval word _ a F hw (fun _ => [true]) (fun _ _ => rfl)]
  clear hw
  induction F with
  | nil => rfl
  | cons C F ih => simp [ih, List.replicate_succ]

def matrixRowsCode {I : Type} (flags word : I) : Code I :=
  formulaTraverseCode word (clauseRowCode (some flags) none)

theorem matrixRowsCode_eval {I : Type} (flags word : I) (a : I → Word)
    (F : Formula) (hw : a word = encodeCNF F) :
    (matrixRowsCode flags word).eval a = F.flatMap (fun C => clauseBits (matrixClause (a flags) C)) := by
  exact formulaTraverseCode_eval word _ a F hw _ (fun C tail =>
    clauseRowCode_eval (some flags) none (extend a (encodeClause C ++ tail)) C tail rfl)

def signedMatrixCode {I : Type} (flags word : I) : Code I :=
  .append (((Number.constant 4).mul (.length flags)).code)
    (.append (.literal [false]) (.append (clauseCountCode word)
      (.append (.literal [false]) (matrixRowsCode flags word))))

theorem signedMatrixCode_eval {I : Type} (flags word : I) (a : I → Word)
    (F : Formula) (hw : a word = encodeCNF F) :
    (signedMatrixCode flags word).eval a =
      Byskov.signedWord (Quantified.signedFormula (a flags).length (fun i => (a flags)[i.val]) F) := by
  change (((Number.constant 4).mul (.length flags)).code.eval a) ++
    ([false] ++ ((clauseCountCode word).eval a ++ ([false] ++ (matrixRowsCode flags word).eval a))) = _
  rw [Number.correct, clauseCountCode_eval word a F hw, matrixRowsCode_eval flags word a F hw]
  simp only [Byskov.signedWord, Byskov.matrixFormula, Quantified.signedFormula,
    Lax689614.Encoding.formulaWord, List.length_map, List.flatMap_map, matrixClause,
    List.singleton_append, List.append_assoc, Number.mul, Number.constant, Number.length,
    List.cons_append, List.nil_append, clauseBits]

end Lax689614Proofs.CNFTraversal
