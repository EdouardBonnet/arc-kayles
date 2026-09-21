import Lax689614Proofs.ConfigurationBounds
import Lax689614Proofs.MachineCircuit

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax429075Proofs.CircuitBuilder Lax429075Proofs.Streaming
open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs ConfigurationWords

theorem readExpression_bounded {I : Type} (base : Number I) (a : I → Word) (i n b : ℕ)
    (hi : i < n) (hb : base.value a + n ≤ b) :
    ((readExpression base).value (extend a (List.replicate i true))).Bounded b := by
  simp only [readExpression, wire_bounded, Number.add, Number.rename, Number.length,
    extend_some, extend, Option.elim_none, List.length_replicate]
  omega

theorem vectorEqExpression_bounded {I : Type} (n : Number I) (x y : Expression (Option I))
    (a : I → Word) (b : ℕ)
    (hx : ∀ i < n.value a, (x.value (extend a (List.replicate i true))).Bounded b)
    (hy : ∀ i < n.value a, (y.value (extend a (List.replicate i true))).Bounded b) :
    ((vectorEqExpression n x y).value a).Bounded b := by
  apply variableFold_bounded
  intro i hi
  exact iffExpression_bounded _ _ _ _ (hx i hi) (hy i hi)

theorem endpointExpression_bounded {I : Type} (n stage : Number I) (a : I → Word) (i depth : ℕ)
    (hi : i < n.value a) (hs : stage.value a ≤ depth) :
    ((endpointExpression n stage false).value (extend a (List.replicate i true))).Bounded
        (depth * Quantified.NumericReach.width (n.value a)) ∧
      ((endpointExpression n stage true).value (extend a (List.replicate i true))).Bounded
        (depth * Quantified.NumericReach.width (n.value a)) := by
  have bound (side : Bool) : ((endpointExpression n stage side).value (extend a (List.replicate i true))).Bounded
      (depth * Quantified.NumericReach.width (n.value a)) := by
    by_cases hz : stage.value a = 0
    · simp [endpointExpression, Expression.choose, Test.rename, Test.eq_value,
        Number.constant, extend_some, hz]
    · have he : stage.value a - 1 + 1 = stage.value a := by omega
      have hm := Nat.mul_le_mul_right (Quantified.NumericReach.width (n.value a)) hs
      simp only [endpointExpression, Expression.choose, Test.rename, Test.eq_value,
        Number.constant, extend_some, hz, decide_false, ↓reduceIte]
      apply readExpression_bounded _ _ _ _ _ hi
      cases side <;>
        simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte, leftNumber, rightNumber,
          widthNumber, Number.add, Number.mul, Number.sub, Number.constant]
      all_goals
        simp only [Quantified.NumericReach.width] at hm ⊢
        nlinarith
  exact ⟨bound false, bound true⟩

theorem muxExpression_bounded {I : Type} (q x y : Expression I) (a : I → Word) (b : ℕ)
    (hq : (q.value a).Bounded b) (hx : (x.value a).Bounded b) (hy : (y.value a).Bounded b) :
    ((muxExpression q x y).value a).Bounded b := ⟨⟨hq, hx⟩, hq, hy⟩

theorem alignedExpression_bounded {I : Type} (n start : Number I) (x y : Expression (Option I))
    (a : I → Word) (b : ℕ) (hb : start.value a + Quantified.NumericReach.width (n.value a) ≤ b)
    (hx : ∀ i < n.value a, (x.value (extend a (List.replicate i true))).Bounded b)
    (hy : ∀ i < n.value a, (y.value (extend a (List.replicate i true))).Bounded b) :
    ((alignedExpression n start x y).value a).Bounded b := by
  have hmid : ∀ i < n.value a, ((readExpression start).value (extend a (List.replicate i true))).Bounded b := by
    intro i hi
    apply readExpression_bounded _ _ _ _ _ hi
    simp only [Quantified.NumericReach.width] at hb
    omega
  have hside (i : ℕ) : ((Expression.wire ((start.add n).rename some)).value
      (extend a (List.replicate i true))).Bounded b := by
    simp only [wire_bounded, Number.rename, Number.add, extend_some]
    simp only [Quantified.NumericReach.width] at hb
    omega
  apply (conj_bounded _ _ _ _).mpr
  constructor
  · apply vectorEqExpression_bounded
    · intro i hi
      apply readExpression_bounded _ _ _ _ _ hi
      simp only [leftNumber, Number.add, Number.constant, Quantified.NumericReach.width] at *
      omega
    · intro i hi
      exact muxExpression_bounded _ _ _ _ _ (hside i) (hx i hi) (hmid i hi)
  · apply vectorEqExpression_bounded
    · intro i hi
      apply readExpression_bounded _ _ _ _ _ hi
      simp only [rightNumber, Number.add, Number.mul, Number.constant, Quantified.NumericReach.width] at *
      omega
    · intro i hi
      exact muxExpression_bounded _ _ _ _ _ (hside i) (hmid i hi) (hy i hi)

theorem stageExpression_bounded {I : Type} (n stage : Number I) (a : I → Word) (depth : ℕ)
    (hs : stage.value a < depth) :
    ((stageExpression n stage).value a).Bounded (depth * Quantified.NumericReach.width (n.value a)) := by
  apply alignedExpression_bounded
  · change stage.value a * Quantified.NumericReach.width (n.value a) +
      Quantified.NumericReach.width (n.value a) ≤ _
    simpa only [Nat.add_mul, Nat.one_mul] using
      Nat.mul_le_mul_right (Quantified.NumericReach.width (n.value a)) (show stage.value a + 1 ≤ depth by omega)
  · intro i hi; exact (endpointExpression_bounded n stage a i depth hi (by omega)).1
  · intro i hi; exact (endpointExpression_bounded n stage a i depth hi (by omega)).2

theorem matrixExpression_bounded {I : Type} (n depth : Number I) (edge : Expression I)
    (a : I → Word)
    (he : (edge.value a).Bounded (depth.value a * Quantified.NumericReach.width (n.value a))) :
    ((matrixExpression n depth edge).value a).Bounded
      (depth.value a * Quantified.NumericReach.width (n.value a)) := by
  apply (conj_bounded _ _ _ _).mpr
  constructor
  · apply variableFold_bounded
    intro i hi
    have h := stageExpression_bounded (n.rename some) (.length none)
      (extend a (List.replicate i true)) (depth.value a)
      (by simpa only [Number.length, extend, Option.elim_none, List.length_replicate] using hi)
    simpa only [Number.rename, extend_some] using h
  · apply (disj_bounded _ _ _ _).mpr
    refine ⟨?_, he⟩
    apply vectorEqExpression_bounded
    · intro i hi; exact (endpointExpression_bounded n depth a i _ hi (le_refl _)).1
    · intro i hi; exact (endpointExpression_bounded n depth a i _ hi (le_refl _)).2

theorem machineMatrix_bounded (M : Machine) {I : Type} (input table : I)
    (count k : Number I) (a : I → Word) (hk : k.value a + 2 ≤ count.value a) :
    ((machineMatrix M input table count k).value a).Bounded
      ((Quantified.NumericReach.reachPrefix ((bitNumber M count).value a)
        ((bitNumber M count).value a)).count) := by
  rw [Quantified.NumericReach.reachPrefix_count]
  apply matrixExpression_bounded
  have hn : 0 < (bitNumber M count).value a :=
    Nat.mul_pos (FiniteCoding.width_pos (Payload M)) (by omega)
  have he : (bitNumber M count).value a - 1 + 1 = (bitNumber M count).value a := by omega
  apply transitionExpression_bounded _ _ _ _ _ _ _ _ _ hk
  all_goals
    simp only [lastNumber, Bool.true_eq, Bool.false_eq_true, ↓reduceIte, leftNumber, rightNumber,
      widthNumber, Number.add, Number.mul, Number.sub, Number.constant, Quantified.NumericReach.width]
    change _ ≤ (bitNumber M count).value a * (3 * (bitNumber M count).value a + 1)
    have he' : FiniteCoding.width (Payload M) * count.value a = (bitNumber M count).value a := rfl
    rw [he']
    nlinarith

end Lax689614Proofs.CircuitStreaming
