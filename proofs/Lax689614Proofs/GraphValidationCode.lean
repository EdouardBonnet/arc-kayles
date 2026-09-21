import Lax689614Proofs.GraphHeader
import Lax689614Proofs.TransitionCode

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.MachineCode

open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930.PolynomialTime
open Lax689614 Encoding DepthFirst
open scoped Classical

def Test.sameBit {I : Type} (t u : Test I) : Test I :=
  (t.and u).or (t.not.and u.not)

theorem sameBit_value {I : Type} (t u : Test I) (a : I → Word) :
    (Test.sameBit t u).value a = true ↔ t.value a = u.value a := by
  change ((t.value a && u.value a) || (!t.value a && !u.value a)) = true ↔ _
  cases t.value a <;> cases u.value a <;> decide

def diagonalTest {I : Type} (n : Number I) (bits : I) : Test I :=
  Test.forall n (Test.input (some bits)
    (((Number.length none).mul (n.rename some)).add (.length none))).not

def symmetricTest {I : Type} (n : Number I) (bits : I) : Test I :=
  Test.forall n (Test.forall (n.rename some)
    (Test.sameBit
      (Test.input (some (some bits))
        (((Number.length (some none)).mul (n.rename (some ∘ some))).add (.length none)))
      (Test.input (some (some bits))
        (((Number.length none).mul (n.rename (some ∘ some))).add (.length (some none))))))

def matrixTest {I : Type} (n : Number I) (bits : I) : Test I :=
  (Test.eq (.length bits) (n.mul n)).and ((diagonalTest n bits).and (symmetricTest n bits))

theorem matrixTest_value {I : Type} (n : Number I) (bits : I) (a : I → Word) :
    (matrixTest n bits).value a = true ↔ MatrixValid (n.value a) (a bits) := by
  simp only [matrixTest, Test.and, Bool.and_eq_true, Test.eq_value, decide_eq_true_eq,
    Number.length, Number.mul, diagonalTest, symmetricTest, Test.forall_true,
    sameBit_value, Test.not, Bool.not_eq_true', Test.input, Number.add,
    Number.rename, extend, Option.elim_none, Option.elim_some, List.length_replicate]
  change (_ ∧ (∀ i, i < n.value a → bit (a bits) (i * n.value a + i) = false) ∧
    (∀ i, i < n.value a → ∀ j, j < n.value a →
      bit (a bits) (i * n.value a + j) = bit (a bits) (j * n.value a + i))) ↔ _
  simp only [MatrixValid, Fin.forall_iff]

def graphHeaderCode {I : Type} (input : I) (body : Code (Option (Option I))) : Code I :=
  .bind (leadingOnes input).code
    (.bind (dropCode (some input) ((Number.length none).add (.constant 1))) body)

def initialBody {I : Type} (input : I) : Code (Option (Option I)) :=
  let n : Number (Option (Option I)) := .length (some none)
  Code.when ((Test.lt n (.length (some (some input)))).and (matrixTest n none))
    (.append (.literal [false, false]) (frameCode n (n.mul n) n.code))
    (.literal [true, false])

def initialCode {I : Type} (input : I) : Code I := graphHeaderCode input (initialBody input)

noncomputable def initialWord (w : Word) : Word :=
  if ValidGraphHeader w then
    [false, false] ++ rawFrame (inputVars w) (inputVars w * inputVars w)
      (List.replicate (inputVars w) true)
  else [true, false]

theorem initialCode_eval {I : Type} (input : I) (a : I → Word) :
    (initialCode input).eval a = initialWord (a input) := by
  classical
  simp only [initialCode, graphHeaderCode, eval_bind, Number.correct, dropCode_eval,
    leadingOnes_value, Number.length, Number.add, Number.constant, extend,
    Option.elim_none, Option.elim_some, List.length_replicate]
  simp only [initialBody, Code.eval_when, Test.and, Bool.and_eq_true, Test.lt,
    decide_eq_true_eq, matrixTest_value, eval_append, frameCode_eval, Number.correct]
  simp only [Number.length, Number.mul, extend, Option.elim_none, Option.elim_some,
    List.length_replicate, Code.eval]
  simp only [initialWord, ValidGraphHeader, inputVars, afterVars]

theorem initialWord_graph (G : Graph) :
    initialWord (graphWord G) = stateWord (.search [⟨Finset.univ, edgeList G.vertices, G.vertices⟩]) := by
  have h := graphWord_header G
  have hb : clauseBits (Finset.univ : Finset (Fin G.vertices)) = List.replicate G.vertices true := by
    simp [clauseBits]
  simp [initialWord, h.2.2, h.1, stateWord, frameWord, rawFrame, edgeList_length, hb]

theorem initialWord_invalid {w : Word} (h : parseGraph w = none) : initialWord w = [true, false] := by
  have hv : ¬ValidGraphHeader w := by rw [validGraphHeader_iff]; simp [h]
  simp [initialWord, hv]

def driverCode : Code Bool := Code.when (Test.eq (.length true) (.constant 0))
  (initialCode false) nextCode

theorem driverCode_initial (w : Word) : driverCode.eval (fun b => if b then [] else w) = initialWord w := by
  rw [driverCode, Code.eval_when]
  simp [Test.eq_value, Number.length, Number.constant, initialCode_eval]

theorem driverCode_next (w s : Word) (hs : s ≠ []) :
    driverCode.eval (fun b => if b then s else w) = nextWord w s := by
  rw [driverCode, Code.eval_when]
  simp [Test.eq_value, Number.length, Number.constant, hs, nextCode_eval]

end Lax689614Proofs.MachineCode
