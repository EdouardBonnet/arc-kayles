import Lax689614Proofs.UniformExpressions
import Lax689614Proofs.PatternExpressions

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax429075Proofs.CircuitBuilder Lax429075Proofs.Streaming
open Lax434930.PolynomialTime
open Lax434930Proofs.SavitchProofs.PatternAutomata

def slice {α : Type} (f : ℕ → α) (start n : ℕ) : List α :=
  (List.range n).map (fun i => f (start + i))

theorem slice_length {α : Type} (f : ℕ → α) (start n : ℕ) : (slice f start n).length = n := by simp [slice]

theorem slice_zero {α : Type} (f : ℕ → α) (start : ℕ) : slice f start 0 = [] := rfl

theorem slice_cons {α : Type} (f : ℕ → α) (start n : ℕ) :
    slice f start (n + 1) = f start :: slice f (start + 1) n := by
  apply List.ext_getElem
  · simp [slice]
  · intro j hj hk
    cases j <;> simp [slice, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem slice_take {α : Type} (f : ℕ → α) (start n k : ℕ) (hk : k ≤ n) :
    (slice f start n).take k = slice f start k := by
  apply List.ext_getElem <;> simp [slice, Nat.min_eq_left hk]

theorem slice_drop {α : Type} (f : ℕ → α) (start n k : ℕ) :
    (slice f start n).drop k = slice f (start + k) (n - k) := by
  apply List.ext_getElem <;> simp [slice, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem matches_star_slice {α : Type} (S : Set α) (p : Pattern α) (f : ℕ → α) (start n : ℕ) :
    Matches (.star S :: p) (slice f start n) ↔
      ∃ k ≤ n, (∀ j < k, f (start + j) ∈ S) ∧ Matches p (slice f (start + k) (n - k)) := by
  rw [Quantified.matches_star_split, slice_length]
  apply exists_congr; intro k
  apply and_congr_right; intro hk
  rw [slice_take f start n k hk, slice_drop]
  simp [slice]

theorem variableFold_false_eval {I : Type} (count : Number I) (term : Expression (Option I))
    (a : I → Word) (ρ : ℕ → Bool) :
    ((variableFold false count term).value a).eval ρ = true ↔
      ∃ i < count.value a, (term.value (extend a (List.replicate i true))).eval ρ = true := by
  simp only [variableFold, foldExpr, Bool.false_eq_true, ↓reduceIte, anyExpr_eval,
    List.any_map, List.any_eq_true, List.mem_range, Function.comp_def]

theorem variableFold_true_eval {I : Type} (count : Number I) (term : Expression (Option I))
    (a : I → Word) (ρ : ℕ → Bool) :
    ((variableFold true count term).value a).eval ρ = true ↔
      ∀ i < count.value a, (term.value (extend a (List.replicate i true))).eval ρ = true := by
  simp only [variableFold, foldExpr, Bool.true_eq, ↓reduceIte, allExpr_eval,
    List.all_map, List.all_eq_true, List.mem_range, Function.comp_def]

def segmentExpression {α I : Type} (S : Set α) (count start : Number I)
    (source : UniformSymbol α (Option I)) : Expression I :=
  variableFold true count (((source.rename (Option.map some)).at
    ((start.rename some).add (.length none))).test S)

theorem segmentExpression_correct {α I : Type} (S : Set α) (count start : Number I)
    (source : UniformSymbol α (Option I)) (a : I → Word) (ρ : ℕ → Bool) :
    ((segmentExpression S count start source).value a).eval ρ = true ↔
      ∀ j < count.value a, source.value (extend a (List.replicate (start.value a + j) true)) ρ ∈ S := by
  simp only [segmentExpression, variableFold_true_eval,
    UniformSymbol.at, UniformSymbol.rename, bindExpression, Expression.rename, source.correct,
    Number.add, Number.rename, Number.length,
    extend_some, extend_skip, extend, Option.elim_none, List.length_replicate]

def patternExpression {α I : Type} : Pattern α → Number I → Number I → UniformSymbol α (Option I) → Expression I
  | [], count, start, _ => Expression.constant (Test.lt start count).not
  | .one S :: p, count, start, source =>
      Expression.choose (Test.lt start count)
        (((source.at start).test S).conj
          (patternExpression p count (start.add (.constant 1)) source))
        (.constant (.constant false))
  | .star S :: p, count, start, source =>
      variableFold false ((count.sub start).add (.constant 1))
        ((segmentExpression S (.length none) (start.rename some) (source.rename (Option.map some))).conj
          (patternExpression p (count.rename some) ((start.rename some).add (.length none))
            (source.rename (Option.map some))))

theorem patternExpression_correct {α I : Type} (p : Pattern α) (count start : Number I)
    (source : UniformSymbol α (Option I)) (a : I → Word) (ρ : ℕ → Bool) :
    ((patternExpression p count start source).value a).eval ρ = true ↔
      Matches p (slice (fun j => source.value (extend a (List.replicate j true)) ρ)
        (start.value a) (count.value a - start.value a)) := by
  induction p generalizing I with
  | nil =>
    simp [patternExpression, Expression.constant, Test.not, Test.lt, Expr.eval,
      Matches, slice, Nat.sub_eq_zero_iff_le]
  | cons piece p ih =>
    cases piece with
    | one S =>
      by_cases hlt : start.value a < count.value a
      · have hn : count.value a - start.value a = (count.value a - (start.value a + 1)) + 1 := by omega
        rw [hn, slice_cons]
        simp only [patternExpression, Expression.choose, Test.lt, hlt, decide_true, ↓reduceIte,
          Expression.conj, Expression.binary, Bool.true_eq, Expr.eval, Bool.and_eq_true,
          UniformSymbol.correct, UniformSymbol.at, ih, Number.add, Number.constant, Matches,
          List.cons.injEq, exists_eq_left]
        simp [bindExpression, source.correct]
      · have hn : count.value a - start.value a = 0 := Nat.sub_eq_zero_of_le (by omega)
        simp [patternExpression, Expression.choose, Test.lt, hlt, Expression.constant,
          Test.constant, Expr.eval, hn, slice_zero, Matches]
    | star S =>
      rw [matches_star_slice]
      simp only [patternExpression, variableFold_false_eval, Expression.conj, Expression.binary,
        Bool.true_eq, ↓reduceIte, Expr.eval, Bool.and_eq_true, segmentExpression_correct, ih,
        Number.add, Number.sub, Number.constant, Number.rename, Number.length, UniformSymbol.rename,
        extend_some, extend_skip, extend, Option.elim_none, List.length_replicate]
      apply exists_congr; intro k
      have he : count.value a - (start.value a + k) = count.value a - start.value a - k := by omega
      simp only [he]
      constructor
      · rintro ⟨hk, hf, ht⟩; exact ⟨by omega, hf, ht⟩
      · rintro ⟨hk, hf, ht⟩; exact ⟨by omega, hf, ht⟩

end Lax689614Proofs.CircuitStreaming
