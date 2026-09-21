import Lax689614Proofs.ByskovTests
import Lax689614Proofs.GraphCode

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Byskov

open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930.PolynomialTime

def vertexNumber {I : Type} (r : Number I) : Number I :=
  ((Number.constant 9).mul r).add (.constant 1)

def clauseNumber {I : Type} (r m : Number I) : Number I :=
  (((Number.constant 9).mul r).add m).add (.constant 1)

noncomputable def rawLocalRow (r i j : ℕ) : Word :=
  (List.range (9 * r + 1)).map fun u => @decide
    (priorControl r i u ∨ localCell r i j u) (Classical.propDecidable _)

noncomputable def rawBaseRow (r : ℕ) (bits : Word) (j : ℕ) : Word :=
  (List.range (9 * r + 1)).map fun u => @decide
    (priorControl r r u ∨ literalCell r bits j u) (Classical.propDecidable _)

noncomputable def localRowCode {I : Type} (r i j : Number I) : Code I :=
  Code.loop (vertexNumber r)
    (((controlTest (r.rename some) (i.rename some) (.length none)).or
      (localTest (r.rename some) (i.rename some) (j.rename some) (.length none))).code)

noncomputable def baseRowCode {I : Type} (r : Number I) (bits : I) (j : Number I) : Code I :=
  Code.loop (vertexNumber r)
    (((controlTest (r.rename some) (r.rename some) (.length none)).or
      (literalTest (r.rename some) (some bits) (j.rename some) (.length none))).code)

theorem localRowCode_eval {I : Type} (r i j : Number I) (a : I → Word) :
    (localRowCode r i j).eval a = rawLocalRow (r.value a) (i.value a) (j.value a) := by
  classical
  have ht {J : Type} (r i j u : Number J) (b : J → Word) :
      ((controlTest r i u).or (localTest r i j u)).value b =
        decide (priorControl (r.value b) (i.value b) (u.value b) ∨
          localCell (r.value b) (i.value b) (j.value b) (u.value b)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Test.or, Bool.or_eq_true, decide_eq_true_eq, controlTest_value, localTest_value]
  simp only [localRowCode, Code.eval_loop, Test.correct, ht, vertexNumber,
    Number.add, Number.mul, Number.constant, Number.rename, Number.length, extend,
    Option.elim_some, Option.elim_none, List.length_replicate, Function.comp_def,
    List.flatMap_map, List.flatMap_cons, List.flatMap_nil, List.append_nil, rawLocalRow,
    ← List.map_eq_flatMap]
  apply List.map_congr_left
  intro u hu
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

theorem baseRowCode_eval {I : Type} (r : Number I) (bits : I) (j : Number I) (a : I → Word) :
    (baseRowCode r bits j).eval a = rawBaseRow (r.value a) (a bits) (j.value a) := by
  classical
  have ht {J : Type} (r j u : Number J) (bits : J) (b : J → Word) :
      ((controlTest r r u).or (literalTest r bits j u)).value b =
        decide (priorControl (r.value b) (r.value b) (u.value b) ∨
          literalCell (r.value b) (b bits) (j.value b) (u.value b)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Test.or, Bool.or_eq_true, decide_eq_true_eq, controlTest_value, literalTest_value]
  simp only [baseRowCode, Code.eval_loop, Test.correct, ht, vertexNumber,
    Number.add, Number.mul, Number.constant, Number.rename, Number.length, extend,
    Option.elim_some, Option.elim_none, List.length_replicate, Function.comp_def,
    List.flatMap_map, List.flatMap_cons, List.flatMap_nil, List.append_nil, rawBaseRow,
    ← List.map_eq_flatMap]
  apply List.map_congr_left
  intro u hu
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]

def dummyRowCode {I : Type} (r : Number I) : Code I :=
  Code.loop (vertexNumber r) (Test.eq (.length none) ((Number.constant 9).mul (r.rename some))).code

theorem dummyRowCode_eval {I : Type} (r : Number I) (a : I → Word) :
    (dummyRowCode r).eval a =
      (List.range (9 * r.value a + 1)).map (fun u => decide (u = 9 * r.value a)) := by
  simp only [dummyRowCode, Code.eval_loop, Test.correct, Test.eq_value, vertexNumber,
    Number.add, Number.mul, Number.constant, Number.rename, Number.length, extend,
    Option.elim_some, Option.elim_none, List.length_replicate, Function.comp_def,
    List.flatMap_map, List.flatMap_cons, List.flatMap_nil, List.append_nil, ← List.map_eq_flatMap]

noncomputable def allLocalCode {I : Type} (r : Number I) : Code I :=
  Code.loop r (Code.loop (.constant 9)
    (localRowCode (r.rename (some ∘ some)) (.length (some none)) (.length none)))

noncomputable def positiveCode {I : Type} (r m : Number I) (bits : I) : Code I :=
  .append (vertexNumber r).code (.append (.literal [false])
    (.append (clauseNumber r m).code (.append (.literal [false])
      (.append (dummyRowCode r) (.append (allLocalCode r)
        (Code.loop m (baseRowCode (r.rename some) (some bits) (.length none))))))))

noncomputable def positiveWord (r m : ℕ) (bits : Word) : Word :=
  List.replicate (9 * r + 1) true ++ [false] ++
    List.replicate (9 * r + m + 1) true ++ [false] ++
      (List.range (9 * r + 1)).map (fun u => decide (u = 9 * r)) ++
        (List.range r).flatMap (fun i => (List.range 9).flatMap (rawLocalRow r i)) ++
          (List.range m).flatMap (rawBaseRow r bits)

theorem positiveCode_eval {I : Type} (r m : Number I) (bits : I) (a : I → Word) :
    (positiveCode r m bits).eval a = positiveWord (r.value a) (m.value a) (a bits) := by
  change (vertexNumber r).code.eval a ++ ([false] ++ ((clauseNumber r m).code.eval a ++
    ([false] ++ ((dummyRowCode r).eval a ++ ((allLocalCode r).eval a ++
      (Code.loop m (baseRowCode (r.rename some) (some bits) (.length none))).eval a))))) = _
  rw [Number.correct, Number.correct]
  simp only [dummyRowCode_eval, allLocalCode,
    Code.eval_loop, localRowCode_eval, baseRowCode_eval, vertexNumber, clauseNumber,
    Number.add, Number.mul, Number.constant, Number.rename, Number.length, extend,
    Option.elim_some, Option.elim_none, List.length_replicate, Function.comp_def,
    positiveWord, List.append_assoc]

end Lax689614Proofs.Byskov
