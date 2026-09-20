import Lax689614Proofs.CodeComputer
import Lax689614Proofs.FormulaParser

namespace Lax689614Proofs.MachineCode

open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930.PolynomialTime

theorem prefix_all_iff (w : Word) (k : ℕ) :
    (∀ j ≤ k, (w[j]?).getD false = true) ↔ k < (w.takeWhile id).length := by
  induction w generalizing k with
  | nil => simp; exact ⟨0, Nat.zero_le _⟩
  | cons b w ih =>
    cases b
    · simp only [List.takeWhile_cons, id_eq, Bool.false_eq_true, ↓reduceIte, List.length_nil,
        Nat.not_lt_zero, iff_false]
      intro h
      have hh := h 0 (Nat.zero_le _)
      simp at hh
    · cases k with
      | zero => simp
      | succ k =>
        simp only [List.takeWhile_cons, id_eq, ↓reduceIte, List.length_cons, Nat.add_lt_add_iff_right]
        constructor
        · intro h
          apply (ih k).mp
          intro j hj
          simpa using h (j + 1) (by omega)
        · intro h j hj
          cases j with
          | zero => rfl
          | succ j => exact (ih k).mpr h j (by omega)

theorem range_prefix_bits (n p : ℕ) :
    (List.range n).flatMap (fun i => if i < p then [true] else []) =
      List.replicate (min n p) true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    by_cases hn : n < p
    · simp [hn, Nat.min_eq_left (show n ≤ p by omega),
        Nat.min_eq_left (show n + 1 ≤ p by omega), List.replicate_succ', List.flatMap]
    · simp [hn, Nat.min_eq_right (show p ≤ n by omega),
        Nat.min_eq_right (show p ≤ n + 1 by omega)]

def leadingOnes {I : Type} (i : I) : Number I where
  value a := ((a i).takeWhile id).length
  code := .forRange i (Code.when
    (Test.forall ((Number.length none).add (.constant 1))
      (Test.input (some (some i)) (Number.length none)))
    (.literal [true]) (.literal []))
  correct a := by
    simp only [Code.eval, Code.eval_when]
    have htest (k : ℕ) :
        (Test.forall ((Number.length none).add (.constant 1))
          (Test.input (some (some i)) (Number.length none))).value
          (extend a (List.replicate k true)) = decide (k < ((a i).takeWhile id).length) := by
      apply Bool.eq_iff_iff.mpr
      rw [Test.forall_true]
      simp only [Number.add, Number.length, Number.constant, Test.input, extend,
        Option.elim_none, Option.elim_some, List.length_replicate, decide_eq_true_eq]
      simpa only [Nat.lt_add_one_iff] using prefix_all_iff (a i) k
    simp only [htest, decide_eq_true_eq]
    rw [range_prefix_bits]
    have hle : ((a i).takeWhile id).length ≤ (a i).length := by
      induction a i with
      | nil => simp
      | cons b w ih => cases b <;> simp_all
    rw [Nat.min_eq_right hle]

theorem leadingOnes_value {I : Type} (i : I) (a : I → Word) :
    (leadingOnes i).value a = ((a i).takeWhile id).length := rfl

end Lax689614Proofs.MachineCode
