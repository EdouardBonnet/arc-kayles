import Lax689614Proofs.UniformBounds

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax429075Proofs.CircuitBuilder Lax429075Proofs.Streaming
open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs ConfigurationWords

theorem codedArray_bounded (α : Type) [Fintype α] [Inhabited α] {I : Type}
    (base : Number I) (a : I → Word) (j count b : ℕ) (hj : j < count)
    (hb : base.value a + FiniteCoding.width α * count ≤ b) :
    (codedArray α base).Bounded (extend a (List.replicate j true)) b := by
  apply uniformSymbol_bounded
  intro i
  simp only [Number.add, Number.mul, Number.rename, Number.length, Number.constant,
    extend_some, extend, Option.elim_none, List.length_replicate]
  have hi := i.isLt
  have hmul := Nat.mul_le_mul_left (FiniteCoding.width α) (show j + 1 ≤ count by omega)
  nlinarith

theorem headerExpression_bounded (M : Machine) {I : Type} (input : I) (i : Number I)
    (source : UniformSymbol (Letter M) I) (a : I → Word) (b : ℕ)
    (hs : source.Bounded a b) : ((headerExpression M input i source).value a).Bounded b := by
  unfold headerExpression
  apply choose_bounded _ _ _ _ _ (hs _)
  apply choose_bounded
  · exact choose_bounded _ _ _ _ _ (hs _) (hs _)
  · exact hs _

theorem inputPositionExpression_bounded (M : Machine) {I : Type} (input table : I)
    (k i pos : Number I) (source : UniformSymbol (Letter M) I) (a : I → Word) (b : ℕ)
    (hs : source.Bounded a b) :
    ((inputPositionExpression M input table k i pos source).value a).Bounded b := by
  unfold inputPositionExpression
  apply choose_bounded _ _ _ _ _ (headerExpression_bounded M input i source a b hs)
  apply choose_bounded _ _ _ _ _ (hs _)
  exact choose_bounded _ _ _ _ _ (hs _) (hs _)

theorem inputPrefixExpression_bounded (M : Machine) {I : Type} (input table : I)
    (count k i : Number I) (source : UniformSymbol (Letter M) (Option I))
    (a : I → Word) (b : ℕ) (hk : k.value a + 2 ≤ count.value a)
    (hs : ∀ j < count.value a, source.Bounded (extend a (List.replicate j true)) b) :
    ((inputPrefixExpression M input table count k i source).value a).Bounded b := by
  apply (conj_bounded _ _ _ _).mpr
  refine ⟨trivial, ?_⟩
  apply variableFold_bounded
  intro j hj
  have hj' : j < count.value a := by
    simp only [Number.add, Number.constant] at hj
    omega
  apply inputPositionExpression_bounded
  simpa only [UniformSymbol.Bounded, UniformSymbol.at, UniformSymbol.rename, bindExpression,
    Expression.rename, Number.length, extend_skip, extend, Option.elim_none,
    List.length_replicate] using hs j hj'

theorem validationExpression_bounded (M : Machine) {I : Type} (input table : I)
    (count k : Number I) (source : UniformSymbol (Letter M) (Option I))
    (a : I → Word) (b : ℕ) (hk : k.value a + 2 ≤ count.value a)
    (hs : ∀ j < count.value a, source.Bounded (extend a (List.replicate j true)) b) :
    ((validationExpression M input table count k source).value a).Bounded b := by
  apply (disj_bounded _ _ _ _).mpr
  constructor
  · apply segmentExpression_bounded
    simpa only [Number.constant, Nat.zero_add] using hs
  · apply (disj_bounded _ _ _ _).mpr
    constructor
    · apply segmentExpression_bounded
      simpa only [Number.constant, Nat.zero_add] using hs
    · apply variableFold_bounded
      intro i hi
      apply inputPrefixExpression_bounded
      · simpa only [Number.rename, extend_some] using hk
      · intro j hj
        simp only [Number.rename, extend_some] at hj
        simpa only [UniformSymbol.Bounded, UniformSymbol.rename, Expression.rename,
          extend_skip] using hs j hj

theorem transitionExpression_bounded (M : Machine) {I : Type} (input table : I)
    (count k left right : Number I) (a : I → Word) (b : ℕ)
    (hk : k.value a + 2 ≤ count.value a)
    (hl : left.value a + FiniteCoding.width (Payload M) * count.value a ≤ b)
    (hr : right.value a + FiniteCoding.width (Payload M) * count.value a ≤ b) :
    ((transitionExpression M input table count k left right).value a).Bounded b := by
  have hleft := fun j hj => codedArray_bounded (Payload M) left a j (count.value a) b hj hl
  have hright := fun j hj => codedArray_bounded (Payload M) right a j (count.value a) b hj hr
  apply (conj_bounded _ _ _ _).mpr
  constructor
  · apply fixedFold_bounded
    intro p hp
    apply patternExpression_bounded
    · exact Nat.zero_le _
    · intro j hj
      exact pair_bounded _ _ _ _ (hleft j hj) (hright j hj)
  · exact ⟨validationExpression_bounded M input table count k _ a b hk hleft,
      validationExpression_bounded M input table count k _ a b hk hright⟩

end Lax689614Proofs.CircuitStreaming
