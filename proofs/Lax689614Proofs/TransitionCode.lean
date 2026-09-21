import Lax689614Proofs.TransitionWords

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.MachineCode

open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930.PolynomialTime
open DepthFirst

def boundedTakeCode {I : Type} (n : Number I) (bits : I) : Code I :=
  takeCode (n.min (.length bits)) bits

theorem boundedTakeCode_eval {I : Type} (n : Number I) (bits : I) (a : I → Word) :
    (boundedTakeCode n bits).eval a = (a bits).take (n.value a) := by
  rw [boundedTakeCode, takeCode_eval]
  simp only [Number.min_value, Number.length]
  rw [take_as_range _ _ (Nat.min_le_right _ _)]
  simp

def frameCode {I : Type} (fuel count : Number I) (board : Code I) : Code I :=
  .append fuel.code (.append (.literal [false])
    (.append count.code (.append (.literal [false]) board)))

theorem frameCode_eval {I : Type} (fuel count : Number I) (board : Code I) (a : I → Word) :
    (frameCode fuel count board).eval a = rawFrame (fuel.value a) (count.value a) (board.eval a) := by
  change fuel.code.eval a ++ ([false] ++ (count.code.eval a ++ ([false] ++ board.eval a))) = _
  rw [Number.correct, Number.correct]
  rfl

def clearPairCode {I : Type} (n u v : Number I) (bits : I) : Code I :=
  Code.loop n (((Test.input (some bits) (.length none)).and
    (Test.eq (.length none) (u.rename some)).not).and
    (Test.eq (.length none) (v.rename some)).not).code

theorem clearPairCode_eval {I : Type} (n u v : Number I) (bits : I) (a : I → Word) :
    (clearPairCode n u v bits).eval a = clearPair (n.value a) (u.value a) (v.value a) (a bits) := by
  simp only [clearPairCode, Code.eval_loop]
  simp only [Test.correct]
  simp only [Test.and, Test.not,
    Test.eq_value, Test.input, Number.rename, Number.length, extend,
    Option.elim_none, Option.elim_some, List.length_replicate, ← List.map_eq_flatMap]
  rfl

def nextBodyCode {I : Type} (n fuel count : Number I) (graph state frames boardRest : I) : Code I :=
  let rest := dropCode boardRest n
  let j := (n.mul n).sub count
  let u := j.div n
  let v := j.mod n
  let parent := Code.append (frameCode fuel (count.sub (.constant 1)) (boundedTakeCode n boardRest)) rest
  Code.when (Test.input state (.constant 0))
    (Code.when (Test.input state (.constant 1))
      (.append (.literal [false, false]) (.source frames))
      (.append (.literal [true, true]) rest))
    (Code.when ((Test.eq fuel (.constant 0)).or (Test.eq count (.constant 0)))
      (.append (.literal [true, false]) rest)
      (Code.when (((Test.input boardRest u).and (Test.input boardRest v)).and
        (Test.input graph ((n.add (.constant 1)).add j)))
        (.append (.literal [false, false])
          (.append (frameCode (fuel.sub (.constant 1)) (n.mul n) (clearPairCode n u v boardRest)) parent))
        (.append (.literal [false, false]) parent)))

theorem eval_append {I : Type} (p q : Code I) (a : I → Word) :
    (Code.append p q).eval a = p.eval a ++ q.eval a := rfl

theorem nextBodyCode_eval {I : Type} (n fuel count : Number I)
    (graph state frames boardRest : I) (a : I → Word) :
    (nextBodyCode n fuel count graph state frames boardRest).eval a =
      nextBody (n.value a) (fuel.value a) (count.value a)
        (a graph) (a state) (a frames) (a boardRest) := by
  simp only [nextBodyCode, Code.eval_when, eval_append, frameCode_eval, boundedTakeCode_eval,
    dropCode_eval, clearPairCode_eval, Test.input, Test.or, Test.and, Test.eq_value,
    Number.constant, Number.add, Number.mul, Number.sub, Number.div, Number.mod]
  simp only [Code.eval, nextBody, bit, Bool.or_eq_true, decide_eq_true_eq,
    List.append_assoc, List.cons_append, List.nil_append]

abbrev StepContext := Option (Option (Option (Option (Option Bool))))
def stepCount : StepContext := some none
def stepFuel : StepContext := some (some (some none))
def stepFrames : StepContext := some (some (some (some none)))
def stepInput (b : Bool) : StepContext := some (some (some (some (some b))))

def withFrame (body : Code StepContext) : Code Bool :=
  .bind (dropCode true (.constant 2))
    (.bind (leadingOnes none).code
      (.bind (dropCode (some none) ((Number.length none).add (.constant 1)))
        (.bind (leadingOnes none).code
          (.bind (dropCode (some none) ((Number.length none).add (.constant 1))) body))))

def nextCode : Code Bool := withFrame
  (nextBodyCode (leadingOnes (stepInput false)) (.length stepFuel) (.length stepCount)
    (stepInput false) (stepInput true) stepFrames none)

theorem nextCode_eval (a : Bool → Word) :
    nextCode.eval a = nextWord (a false) (a true) := by
  simp only [nextCode, withFrame, eval_bind, Number.correct, dropCode_eval, nextBodyCode_eval,
    leadingOnes_value, Number.add, Number.length, Number.constant, extend,
    Option.elim_none, Option.elim_some, List.length_replicate,
    stepInput, stepFrames, stepCount, stepFuel]
  rfl

end Lax689614Proofs.MachineCode
