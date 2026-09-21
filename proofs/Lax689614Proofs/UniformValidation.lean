import Lax689614Proofs.UniformInput
import Lax689614Proofs.UniformConfigurationSymbols

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax429075Proofs.CircuitBuilder Lax429075Proofs.Streaming
open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs ConfigurationWords PatternAutomata

theorem matches_inputPrefix (M : Machine) (w : Word) (k i : ℕ) (xs : List (Letter M)) :
    Matches ((Quantified.inputPrefix M w k i).map Piece.one ++ [.star Set.univ]) xs ↔
      ∃ q tail, xs = header M q (readInput w i) ::
        ((BinaryCounter.word k i).map (bit M) ++ split M :: tail) := by
  simp only [Quantified.inputPrefix, List.map_cons, List.map_append, List.map_map, List.cons_append,
    matches_one_range, Function.comp_def, List.map_nil, List.append_assoc]
  have he : (fun b => Piece.one ({bit M b} : Set (Letter M))) =
      (fun x => Piece.one ({x} : Set (Letter M))) ∘ bit M := rfl
  rw [he, ← List.map_map]
  simp_rw [Quantified.matches_singletons]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, matches_one_single,
    matches_star, Set.mem_univ, implies_true, and_true]
  constructor
  · rintro ⟨q, rest, he, tail, hr, final, hf⟩
    exact ⟨q, final, by rw [he, hr, hf]⟩
  · rintro ⟨q, tail, he⟩
    exact ⟨q, _, he, split M :: tail, rfl, tail, rfl⟩

noncomputable def validationExpression (M : Machine) {I : Type} (input table : I)
    (count k : Number I) (source : UniformSymbol (Letter M) (Option I)) : Expression I :=
  (segmentExpression {Sum.inl false} count (.constant 0) source).disj
    ((segmentExpression {Sum.inl true} count (.constant 0) source).disj
      (variableFold false ((Number.length input).add (.constant 2))
        (inputPrefixExpression M (some input) (some table) (count.rename some) (k.rename some)
          (.length none) (source.rename (Option.map some)))))

theorem validationExpression_correct (M : Machine) {I : Type} (input table : I)
    (count k : Number I) (source : UniformSymbol (Letter M) (Option I)) (a : I → Word) (ρ : ℕ → Bool)
    (ht : a table = digitTable ((a input).length + 2) (k.value a)) :
    ((validationExpression M input table count k source).value a).eval ρ = true ↔
      Quantified.InputForm M (a input) (k.value a)
        (slice (fun j => source.value (extend a (List.replicate j true)) ρ) 0 (count.value a)) := by
  simp only [validationExpression, Expression.disj, Expression.binary, Bool.false_eq_true,
    ↓reduceIte, Expr.eval, Bool.or_eq_true, segmentExpression_correct, Number.constant,
    Nat.zero_add, Set.mem_singleton_iff, Quantified.InputForm]
  have hspecial (b : Bool) :
      (∀ j < count.value a, source.value (extend a (List.replicate j true)) ρ = Sum.inl b) ↔
        ∀ x ∈ slice (fun j => source.value (extend a (List.replicate j true)) ρ) 0 (count.value a), x = Sum.inl b := by
    simp [slice]
  apply or_congr (hspecial false)
  apply or_congr (hspecial true)
  rw [variableFold_false_eval]
  simp only [Number.add, Number.length, Number.constant]
  have hc (i : ℕ) (hi : i ≤ (a input).length + 1) :
      ((inputPrefixExpression M (some input) (some table) (count.rename some) (k.rename some)
        (.length none) (source.rename (Option.map some))).value (extend a (List.replicate i true))).eval ρ = true ↔
      ∃ q tail, slice (fun j => source.value (extend a (List.replicate j true)) ρ) 0 (count.value a) =
        header M q (readInput (a input) i) ::
          ((BinaryCounter.word (k.value a) i).map (bit M) ++ split M :: tail) := by
    have hh := inputPrefixExpression_correct M (some input) (some table)
      (count.rename some) (k.rename some) (.length none) (source.rename (Option.map some))
      (extend a (List.replicate i true)) ρ
      (by simpa only [Number.rename, extend_some, extend, Option.elim_some] using ht)
      (by simpa only [Number.length, extend, Option.elim_none, Option.elim_some, List.length_replicate] using hi)
    rw [matches_inputPrefix] at hh
    simpa only [Number.rename, Number.length, UniformSymbol.rename, extend_some, extend_skip,
      extend, Option.elim_none, Option.elim_some, List.length_replicate] using hh
  constructor
  · rintro ⟨i, hi, hv⟩
    exact ⟨i, by omega, (hc i (by omega)).mp hv⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨i, by omega, (hc i hi).mpr hv⟩

noncomputable def transitionExpression (M : Machine) {I : Type} (input table : I)
    (count k left right : Number I) : Expression I :=
  (fixedFold false (graphPatterns M) (fun p => patternExpression p count (.constant 0)
    ((codedArray (Payload M) left).pair (codedArray (Payload M) right)))).conj
      ((validationExpression M input table count k (codedArray (Payload M) left)).conj
        (validationExpression M input table count k (codedArray (Payload M) right)))

theorem transitionExpression_correct (M : Machine) {I : Type} (input table : I)
    (count k left right : Number I) (a : I → Word) (ρ : ℕ → Bool)
    (ht : a table = digitTable ((a input).length + 2) (k.value a)) :
    ((transitionExpression M input table count k left right).value a).eval ρ = true ↔
      (∃ p ∈ graphPatterns M, Matches p (List.zip
        (FiniteCoding.decodeWord (Payload M) (slice ρ (left.value a) (FiniteCoding.width (Payload M) * count.value a)))
        (FiniteCoding.decodeWord (Payload M) (slice ρ (right.value a) (FiniteCoding.width (Payload M) * count.value a))))) ∧
      Quantified.InputForm M (a input) (k.value a)
        (FiniteCoding.decodeWord (Payload M) (slice ρ (left.value a) (FiniteCoding.width (Payload M) * count.value a))) ∧
      Quantified.InputForm M (a input) (k.value a)
        (FiniteCoding.decodeWord (Payload M) (slice ρ (right.value a) (FiniteCoding.width (Payload M) * count.value a))) := by
  simp only [transitionExpression, Expression.conj, Expression.binary, Bool.true_eq, ↓reduceIte,
    Expr.eval, Bool.and_eq_true, fixedFold_false_eval, patternExpression_correct, Number.constant,
    Nat.sub_zero, pairedArray_word, validationExpression_correct _ _ _ _ _ _ _ _ ht, codedArray_word]

end Lax689614Proofs.CircuitStreaming
