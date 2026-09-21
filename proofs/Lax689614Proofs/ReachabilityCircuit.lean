import Lax689614Proofs.UniformValidation
import Lax689614Proofs.NumericReachLayout

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax429075Proofs.CircuitBuilder Lax429075Proofs.Streaming
open Lax434930.PolynomialTime
open Quantified (Vector)

def vectorValue {I : Type} (n : ℕ) (e : Expression (Option I)) (a : I → Word) (ρ : ℕ → Bool) : Vector n :=
  fun i => (e.value (extend a (List.replicate i.val true))).eval ρ

def readExpression {I : Type} (base : Number I) : Expression (Option I) :=
  Expression.wire ((base.rename some).add (.length none))

theorem readExpression_value {I : Type} (base : Number I) (n : ℕ) (a : I → Word) (ρ : ℕ → Bool) :
    vectorValue n (readExpression base) a ρ = Quantified.NumericReach.readVector n (base.value a) ρ := by
  funext i
  simp [vectorValue, readExpression, Expression.wire, Number.add, Number.rename,
    Number.length, extend_some, extend, Expr.eval, Quantified.NumericReach.readVector]

def muxExpression {I : Type} (b p q : Expression I) : Expression I :=
  (b.conj p).disj (b.neg.conj q)

theorem muxExpression_eval {I : Type} (b p q : Expression I) (a : I → Word) (ρ : ℕ → Bool) :
    ((muxExpression b p q).value a).eval ρ =
      if (b.value a).eval ρ then (p.value a).eval ρ else (q.value a).eval ρ := by
  simp only [muxExpression, Expression.conj, Expression.disj, Expression.binary, Expression.neg,
    Bool.true_eq, Bool.false_eq_true, ↓reduceIte, Expr.eval]
  cases (b.value a).eval ρ <;> simp

def vectorEqExpression {I : Type} (n : Number I) (x y : Expression (Option I)) : Expression I :=
  variableFold true n (iffExpression x y)

theorem vectorEqExpression_eval {I : Type} (n : Number I) (x y : Expression (Option I))
    (a : I → Word) (ρ : ℕ → Bool) :
    ((vectorEqExpression n x y).value a).eval ρ = true ↔
      vectorValue (n.value a) x a ρ = vectorValue (n.value a) y a ρ := by
  simp only [vectorEqExpression, variableFold_true_eval, iffExpression_eval]
  constructor
  · intro h; funext i; exact h i.val i.isLt
  · intro h i hi; exact congrFun h ⟨i, hi⟩

def leftNumber {I : Type} (n start : Number I) : Number I := (start.add n).add (.constant 1)
def rightNumber {I : Type} (n start : Number I) : Number I :=
  (start.add ((Number.constant 2).mul n)).add (.constant 1)
def widthNumber {I : Type} (n : Number I) : Number I := ((Number.constant 3).mul n).add (.constant 1)

def alignedExpression {I : Type} (n start : Number I) (x y : Expression (Option I)) : Expression I :=
  let side : Expression (Option I) := .wire ((start.add n).rename some)
  let mid := readExpression start
  (vectorEqExpression n (readExpression (leftNumber n start)) (muxExpression side x mid)).conj
    (vectorEqExpression n (readExpression (rightNumber n start)) (muxExpression side mid y))

theorem alignedExpression_eval {I : Type} (n start : Number I) (x y : Expression (Option I))
    (a : I → Word) (ρ : ℕ → Bool) :
    ((alignedExpression n start x y).value a).eval ρ = true ↔
      Quantified.NumericReach.aligned (n.value a) (start.value a)
        (vectorValue (n.value a) x a) (vectorValue (n.value a) y a) ρ := by
  simp only [alignedExpression, Expression.conj, Expression.binary, Bool.true_eq, ↓reduceIte,
    Expr.eval, Bool.and_eq_true, vectorEqExpression_eval, readExpression_value,
    Quantified.NumericReach.aligned]
  have hm (p q : Expression (Option I)) :
      vectorValue (n.value a) (muxExpression (.wire ((start.add n).rename some)) p q) a ρ =
        if ρ (start.value a + n.value a) then vectorValue (n.value a) p a ρ else vectorValue (n.value a) q a ρ := by
    funext i
    simp only [vectorValue, muxExpression_eval, Expression.wire, Number.rename, Number.add,
      extend_some, Expr.eval]
    split_ifs <;> rfl
  rw [hm, hm, readExpression_value]
  rfl

def endpointExpression {I : Type} (n stage : Number I) (side : Bool) : Expression (Option I) :=
  Expression.choose ((Test.eq stage (.constant 0)).rename some) (.constant (.constant side))
    (readExpression (if side then rightNumber n ((stage.sub (.constant 1)).mul (widthNumber n))
      else leftNumber n ((stage.sub (.constant 1)).mul (widthNumber n))))

theorem endpointExpression_value {I : Type} (n stage : Number I) (side : Bool)
    (a : I → Word) (ρ : ℕ → Bool) :
    vectorValue (n.value a) (endpointExpression n stage side) a ρ =
      Quantified.NumericReach.endpoint (n.value a) (stage.value a) side ρ := by
  by_cases hs : stage.value a = 0
  · funext i
    simp [vectorValue, endpointExpression, Expression.choose, Test.rename, Test.eq_value,
      Number.constant, extend_some, hs, Expression.constant, Test.constant, Expr.eval,
      Quantified.NumericReach.endpoint]
  · obtain ⟨j, hj⟩ : ∃ j, stage.value a = j + 1 := ⟨stage.value a - 1, by omega⟩
    have he : vectorValue (n.value a) (endpointExpression n stage side) a ρ =
        vectorValue (n.value a) (readExpression (if side then
          rightNumber n ((stage.sub (.constant 1)).mul (widthNumber n)) else
          leftNumber n ((stage.sub (.constant 1)).mul (widthNumber n)))) a ρ := by
      funext i
      simp [vectorValue, endpointExpression, Expression.choose, Test.rename, Test.eq_value,
        Number.constant, extend_some, hs]
    rw [he, readExpression_value, hj]
    cases side <;> simp [rightNumber, leftNumber, widthNumber, Number.add, Number.sub, Number.mul,
      Number.constant, hj, Quantified.NumericReach.endpoint, Quantified.NumericReach.leftBase,
      Quantified.NumericReach.rightBase, Quantified.NumericReach.width]

def stageExpression {I : Type} (n stage : Number I) : Expression I :=
  alignedExpression n (stage.mul (widthNumber n))
    (endpointExpression n stage false) (endpointExpression n stage true)

theorem stageExpression_eval {I : Type} (n stage : Number I) (a : I → Word) (ρ : ℕ → Bool) :
    ((stageExpression n stage).value a).eval ρ = true ↔
      Quantified.NumericReach.aligned (n.value a) (stage.value a * Quantified.NumericReach.width (n.value a))
        (Quantified.NumericReach.endpoint (n.value a) (stage.value a) false)
        (Quantified.NumericReach.endpoint (n.value a) (stage.value a) true) ρ := by
  rw [stageExpression, alignedExpression_eval]
  have he (side : Bool) : vectorValue (n.value a) (endpointExpression n stage side) a =
      Quantified.NumericReach.endpoint (n.value a) (stage.value a) side :=
    funext (endpointExpression_value n stage side a)
  simp only [he, widthNumber, Number.add, Number.mul, Number.constant,
    Quantified.NumericReach.width]

def matrixExpression {I : Type} (n depth : Number I) (edge : Expression I) : Expression I :=
  (variableFold true depth (stageExpression (n.rename some) (.length none))).conj
    ((vectorEqExpression n (endpointExpression n depth false) (endpointExpression n depth true)).disj edge)

theorem matrixExpression_eval {I : Type} (n depth : Number I) (edge : Expression I)
    (a : I → Word) (ρ : ℕ → Bool) (E : Vector (n.value a) → Vector (n.value a) → Prop)
    (he : (edge.value a).eval ρ = true ↔
      E (Quantified.NumericReach.endpoint (n.value a) (depth.value a) false ρ)
        (Quantified.NumericReach.endpoint (n.value a) (depth.value a) true ρ)) :
    ((matrixExpression n depth edge).value a).eval ρ = true ↔
      Quantified.NumericReach.matrixCondition (n.value a) (depth.value a) E ρ := by
  simp only [matrixExpression, Expression.conj, Expression.disj, Expression.binary,
    Bool.true_eq, Bool.false_eq_true, ↓reduceIte, Expr.eval, Bool.and_eq_true, Bool.or_eq_true,
    variableFold_true_eval, stageExpression_eval, vectorEqExpression_eval, endpointExpression_value,
    he, Number.rename, Number.length, extend_some, extend, Option.elim_none, List.length_replicate,
    Quantified.NumericReach.matrixCondition]

end Lax689614Proofs.CircuitStreaming
