import Lax689614Proofs.InputExpressions

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified

open Lax434930Proofs.SavitchProofs
open ConfigurationWords PatternAutomata
open Lax434930.SpaceMachines Lax434930.PolynomialTime

def InputForm (M : Machine) (w : Word) (k : ℕ) (xs : List (Letter M)) : Prop :=
  (∀ x ∈ xs, x = Sum.inl false) ∨ (∀ x ∈ xs, x = Sum.inl true) ∨
    ∃ i ≤ w.length + 1, ∃ q tail, xs = header M q (readInput w i) ::
      ((BinaryCounter.word k i).map (bit M) ++ split M :: tail)

theorem inputExpr_correct (M : Machine) (w : Word) (k : ℕ) {β : Type}
    (xs : List (Symbol (Letter M) β)) (a : β → Bool) :
    (inputExpr M w k xs).eval a = true ↔ InputForm M w k (xs.map (fun x => x.value a)) := by
  simp only [inputExpr, Expr.eval, Bool.or_eq_true, Expr.eval_all, List.forall_mem_map,
    Symbol.correct, Set.mem_singleton_iff, InputForm]
  apply or_congr Iff.rfl
  apply or_congr Iff.rfl
  rw [Expr.eval_any]
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    exact ⟨i, by have := List.mem_range.mp hi; omega, (inputPrefix_correct M w k i xs a).mp hv⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩,
      (inputPrefix_correct M w k i xs a).mpr h⟩

theorem InputForm.special (M : Machine) (w : Word) (k n : ℕ) (b : Bool) :
    InputForm M w k (List.replicate n (Sum.inl b)) := by
  cases b <;> simp [InputForm]

theorem InputForm.canonical (M : Machine) (w : Word) (k : ℕ) (v : TapeZipper.View M)
    (hi : v.inputHead ≤ w.length + 1) : InputForm M w k (canonical M w k v) :=
  Or.inr (Or.inr ⟨v.inputHead, hi, v.state, row M v.left.reverse v.current v.right, rfl⟩)

theorem InputForm.valid (M : Machine) (w : Word) (k : ℕ) (xs : List (Letter M))
    (hk : w.length + 1 < 2 ^ k) (h : InputForm M w k xs) : ValidInput M w xs := by
  rcases h with h | h | ⟨i, hi, q, tail, rfl⟩
  · rw [list_repeat (Sum.inl false) xs h]
    exact EncodedGraph.special_input M w _ false
  · rw [list_repeat (Sum.inl true) xs h]
    exact EncodedGraph.special_input M w _ true
  · exact validInput_prefix M w k i hi (hi.trans_lt hk) q tail

noncomputable def transitionExpr (M : Machine) (w : Word) (k n : ℕ) {β : Type}
    (xs ys : List (Expr β)) : Expr β :=
  .conj (Expr.any ((graphPatterns M).map (fun p =>
      patternExpr p (pairedSymbols (Payload M) n xs ys))))
    (.conj (inputExpr M w k (codedSymbols (Payload M) n xs))
      (inputExpr M w k (codedSymbols (Payload M) n ys)))

theorem transitionExpr_correct (M : Machine) (w : Word) (k n : ℕ) {β : Type}
    (xs ys : List (Expr β)) (a : β → Bool)
    (hx : xs.length = FiniteCoding.width (Payload M) * n)
    (hy : ys.length = FiniteCoding.width (Payload M) * n) :
    (transitionExpr M w k n xs ys).eval a = true ↔
      (∃ p ∈ graphPatterns M, Matches p
        (List.zip (FiniteCoding.decodeWord (Payload M) (xs.map (Expr.eval a)))
          (FiniteCoding.decodeWord (Payload M) (ys.map (Expr.eval a))))) ∧
      InputForm M w k (FiniteCoding.decodeWord (Payload M) (xs.map (Expr.eval a))) ∧
      InputForm M w k (FiniteCoding.decodeWord (Payload M) (ys.map (Expr.eval a))) := by
  simp only [transitionExpr, Expr.eval, Bool.and_eq_true, inputExpr_correct,
    codedSymbols_correct _ _ _ _ hx, codedSymbols_correct _ _ _ _ hy]
  apply and_congr_left'
  rw [Expr.eval_any]
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
    refine ⟨p, hp, ?_⟩
    simpa only [pairedSymbols_correct _ _ _ _ _ hx hy] using (patternExpr_correct p _ a).mp hv
  · rintro ⟨p, hp, hv⟩
    refine ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, (patternExpr_correct p _ a).mpr ?_⟩
    simpa only [pairedSymbols_correct _ _ _ _ _ hx hy] using hv

end Lax689614Proofs.Quantified
