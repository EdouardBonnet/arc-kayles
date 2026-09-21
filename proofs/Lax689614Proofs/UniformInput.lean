import Lax689614Proofs.UniformPrefix
import Lax689614Proofs.DigitTable
import Lax689614Proofs.ConfigurationValidity

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax429075Proofs.CircuitBuilder Lax429075Proofs.Streaming
open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs ConfigurationWords PatternAutomata

noncomputable def headerExpression (M : Machine) {I : Type} (input : I) (i : Number I)
    (head : UniformSymbol (Letter M) I) : Expression I :=
  Expression.choose (Test.eq i (.constant 0)) (head.test (Set.range (fun q => header M q .leftEnd)))
    (Expression.choose (Test.lt (i.sub (.constant 1)) (.length input))
      (Expression.choose (Test.input input (i.sub (.constant 1)))
        (head.test (Set.range (fun q => header M q (.bit true))))
        (head.test (Set.range (fun q => header M q (.bit false)))))
      (head.test (Set.range (fun q => header M q .rightEnd))))

theorem headerExpression_correct (M : Machine) {I : Type} (input : I) (i : Number I)
    (head : UniformSymbol (Letter M) I) (a : I → Word) (ρ : ℕ → Bool) :
    ((headerExpression M input i head).value a).eval ρ = true ↔
      head.value a ρ ∈ Set.range (fun q => header M q (readInput (a input) (i.value a))) := by
  simp only [headerExpression, Expression.choose, Test.eq_value, Number.constant,
    Test.lt, Number.sub, Number.length, Test.input]
  by_cases hz : i.value a = 0
  · simp [hz, head.correct, readInput]
  · obtain ⟨j, hi⟩ : ∃ j, i.value a = j + 1 := ⟨i.value a - 1, by omega⟩
    simp only [hi]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, decide_false, ↓reduceIte,
      Nat.add_sub_cancel, readInput]
    by_cases hj : j < (a input).length
    · have he : (a input)[j]? = some ((a input)[j]'hj) := List.getElem?_eq_getElem hj
      rw [he]
      cases hb : (a input)[j] <;> simp [hj, hb, head.correct]
    · have he : (a input)[j]? = none := List.getElem?_eq_none (by omega)
      simp [hj, he, head.correct]

noncomputable def inputPositionExpression (M : Machine) {I : Type}
    (input table : I) (k i pos : Number I) (symbol : UniformSymbol (Letter M) I) : Expression I :=
  Expression.choose (Test.eq pos (.constant 0)) (headerExpression M input i symbol)
    (Expression.choose (Test.eq pos (k.add (.constant 1))) (symbol.test {split M})
      (Expression.choose (Test.input table ((i.mul k).add (pos.sub (.constant 1))))
        (symbol.test {bit M true}) (symbol.test {bit M false})))

theorem inputPrefix_length (M : Machine) (w : Word) (k i : ℕ) :
    (Quantified.inputPrefix M w k i).length = k + 2 := by simp [Quantified.inputPrefix]

theorem inputPrefix_get_bit (M : Machine) (w : Word) (k i j : ℕ) (hj : j < k) :
    (Quantified.inputPrefix M w k i)[j + 1]'(by rw [inputPrefix_length]; omega) =
      {bit M ((BinaryCounter.word k i)[j]'(by simpa using hj))} := by
  simp only [Quantified.inputPrefix]
  rw [List.getElem_append_left (by simp; omega), List.getElem_cons_succ, List.getElem_map]

theorem inputPrefix_get_split (M : Machine) (w : Word) (k i : ℕ) :
    (Quantified.inputPrefix M w k i)[k + 1]'(by rw [inputPrefix_length]; omega) = {split M} := by
  simp [Quantified.inputPrefix]

theorem inputPositionExpression_correct (M : Machine) {I : Type} (input table : I)
    (k i pos : Number I) (symbol : UniformSymbol (Letter M) I) (a : I → Word) (ρ : ℕ → Bool)
    (ht : a table = digitTable ((a input).length + 2) (k.value a))
    (hi : i.value a ≤ (a input).length + 1) (hp : pos.value a < k.value a + 2) :
    ((inputPositionExpression M input table k i pos symbol).value a).eval ρ = true ↔
      symbol.value a ρ ∈ (Quantified.inputPrefix M (a input) (k.value a) (i.value a))[pos.value a]'(by
        rw [inputPrefix_length]; exact hp) := by
  by_cases hzero : pos.value a = 0
  · simp only [inputPositionExpression, Expression.choose, Test.eq_value, Number.constant, hzero,
      decide_true, ↓reduceIte, headerExpression_correct]
    rfl
  · by_cases hsplit : pos.value a = k.value a + 1
    · simp only [inputPositionExpression, Expression.choose, Test.eq_value, Number.constant,
        hzero, decide_false, ↓reduceIte, Number.add, hsplit, decide_true, symbol.correct,
        inputPrefix_get_split]
      simp [symbol.correct]
    · obtain ⟨j, hj⟩ : ∃ j, pos.value a = j + 1 := ⟨pos.value a - 1, by omega⟩
      have hjk : j < k.value a := by omega
      have hget : (a table)[i.value a * k.value a + j]? =
          some (decide (i.value a / 2 ^ j % 2 = 1)) := by
        rw [ht]
        exact digitTable_get _ _ ⟨i.value a, by omega⟩ ⟨j, hjk⟩
      simp only [inputPositionExpression, Expression.choose, Test.eq_value, Number.constant,
        hzero, decide_false, ↓reduceIte, Number.add, hsplit, Test.input, Number.mul, Number.sub,
        hj, Nat.add_sub_cancel, hget, Option.getD_some, inputPrefix_get_bit M _ _ _ _ hjk,
        binaryWord_get _ _ ⟨j, hjk⟩]
      cases hb : decide (i.value a / 2 ^ j % 2 = 1) <;> simp [hb, symbol.correct, Nat.ne_of_lt hjk]

noncomputable def inputPrefixExpression (M : Machine) {I : Type} (input table : I)
    (count k i : Number I) (source : UniformSymbol (Letter M) (Option I)) : Expression I :=
  prefixCheck count (k.add (.constant 2))
    (inputPositionExpression M (some input) (some table) (k.rename some) (i.rename some) (.length none)
      ((source.rename (Option.map some)).at (.length none)))

theorem inputPrefixExpression_correct (M : Machine) {I : Type} (input table : I)
    (count k i : Number I) (source : UniformSymbol (Letter M) (Option I)) (a : I → Word) (ρ : ℕ → Bool)
    (ht : a table = digitTable ((a input).length + 2) (k.value a))
    (hi : i.value a ≤ (a input).length + 1) :
    ((inputPrefixExpression M input table count k i source).value a).eval ρ = true ↔
      Matches ((Quantified.inputPrefix M (a input) (k.value a) (i.value a)).map Piece.one ++ [.star Set.univ])
        (slice (fun j => source.value (extend a (List.replicate j true)) ρ) 0 (count.value a)) := by
  apply prefixCheck_correct
  · simp [Number.add, Number.constant, inputPrefix_length]
  · intro j hj
    have hj' : j < k.value a + 2 := by simpa only [inputPrefix_length] using hj
    have hh := inputPositionExpression_correct M (some input) (some table)
      (k.rename some) (i.rename some) (.length none)
      ((source.rename (Option.map some)).at (.length none)) (extend a (List.replicate j true)) ρ
      (by simpa only [extend_some, Number.rename, extend, Option.elim_some] using ht)
      (by simpa only [extend_some, Number.rename, extend, Option.elim_some] using hi)
      (by simpa only [Number.length, Number.rename, extend_some, extend, Option.elim_none,
        List.length_replicate] using hj')
    simpa only [UniformSymbol.at, UniformSymbol.rename, Number.length, Number.rename,
      extend_some, extend_skip, extend, Option.elim_none, Option.elim_some, List.length_replicate] using hh

end Lax689614Proofs.CircuitStreaming
