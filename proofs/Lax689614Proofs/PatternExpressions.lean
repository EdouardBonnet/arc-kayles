import Lax689614Proofs.QuantifiedFormulas
import Lax434930Proofs.SavitchProofs.PatternAutomata

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified

open Lax434930Proofs.SavitchProofs.PatternAutomata

def Expr.any {α : Type} (ps : List (Expr α)) : Expr α := ps.foldr .disj (.constant false)

theorem Expr.eval_any {α : Type} (ps : List (Expr α)) (a : α → Bool) :
    (Expr.any ps).eval a = true ↔ ∃ p ∈ ps, p.eval a = true := by
  induction ps <;> simp_all [Expr.any, Expr.eval]

/-- A finite-alphabet symbol represented by Boolean inputs. -/
structure Symbol (α β : Type) where
  value : (β → Bool) → α
  test : Set α → Expr β
  correct : ∀ S a, (test S).eval a = true ↔ value a ∈ S

def patternExpr {α β : Type} : Pattern α → List (Symbol α β) → Expr β
  | [], xs => .constant (decide (xs.length = 0))
  | .one S :: p, [] => .constant false
  | .one S :: p, x :: xs => .conj (x.test S) (patternExpr p xs)
  | .star S :: p, xs => Expr.any ((List.range (xs.length + 1)).map fun k =>
      .conj (Expr.all ((xs.take k).map fun x => x.test S)) (patternExpr p (xs.drop k)))

theorem matches_star_split {α : Type} (S : Set α) (p : Pattern α) (xs : List α) :
    Matches (.star S :: p) xs ↔
      ∃ k ≤ xs.length, (∀ x ∈ xs.take k, x ∈ S) ∧ Matches p (xs.drop k) := by
  constructor
  · rintro ⟨front, tail, rfl, hf, ht⟩
    exact ⟨front.length, by simp, by simpa using hf, by simpa using ht⟩
  · rintro ⟨k, hk, hf, ht⟩
    exact ⟨xs.take k, xs.drop k, (List.take_append_drop k xs).symm, hf, ht⟩

theorem patternExpr_correct {α β : Type} (p : Pattern α) (xs : List (Symbol α β)) (a : β → Bool) :
    (patternExpr p xs).eval a = true ↔ Matches p (xs.map (fun x => x.value a)) := by
  induction p generalizing xs with
  | nil => simp [patternExpr, Expr.eval, Matches]
  | cons piece p ih =>
    cases piece with
    | one S =>
      cases xs with
      | nil => simp [patternExpr, Expr.eval, Matches]
      | cons x xs => simp [patternExpr, Expr.eval, x.correct, ih, Matches]
    | star S =>
      rw [patternExpr, Expr.eval_any, matches_star_split]
      simp only [List.mem_map, exists_exists_and_eq_and, List.mem_range,
        Expr.eval, Bool.and_eq_true, Expr.eval_all, List.forall_mem_map, Symbol.correct,
        ih, List.length_map, ← List.map_take, ← List.map_drop, List.forall_mem_map]
      constructor
      · rintro ⟨k, hk, hf, ht⟩
        refine ⟨k, by omega, ?_, ht⟩
        rintro x ⟨s, hs, rfl⟩
        exact (s.correct S a).mp (hf (s.test S) ⟨s, hs, rfl⟩)
      · rintro ⟨k, hk, hf, ht⟩
        refine ⟨k, by omega, ?_, ht⟩
        rintro e ⟨s, hs, rfl⟩
        exact (s.correct S a).mpr (hf (s.value a) ⟨s, hs, rfl⟩)

theorem Expr.all_size {β : Type} (ps : List (Expr β)) :
    (Expr.all ps).size = (ps.map Expr.size).sum + ps.length + 1 := by
  induction ps <;> simp_all [Expr.all, Expr.size] <;> omega

theorem Expr.any_size {β : Type} (ps : List (Expr β)) :
    (Expr.any ps).size = (ps.map Expr.size).sum + ps.length + 1 := by
  induction ps <;> simp_all [Expr.any, Expr.size] <;> omega

theorem Expr.all_size_le {β : Type} (ps : List (Expr β)) (b : ℕ)
    (hb : ∀ p ∈ ps, p.size ≤ b) : (Expr.all ps).size ≤ ps.length * (b + 1) + 1 := by
  induction ps with
  | nil => simp [Expr.all, Expr.size]
  | cons p ps ih =>
    have hp := hb p (by simp)
    have ht := ih (fun q hq => hb q (List.mem_cons_of_mem _ hq))
    simp only [Expr.all, List.foldr_cons, Expr.size, List.length_cons]
    change p.size + (Expr.all ps).size + 1 ≤ _
    nlinarith

theorem Expr.any_size_le {β : Type} (ps : List (Expr β)) (b : ℕ)
    (hb : ∀ p ∈ ps, p.size ≤ b) : (Expr.any ps).size ≤ ps.length * (b + 1) + 1 := by
  rw [Expr.any_size, ← Expr.all_size]
  exact Expr.all_size_le ps b hb

/-- The degree depends only on the fixed pattern, not on the word length. -/
theorem patternExpr_size {α β : Type} (p : Pattern α) (xs : List (Symbol α β))
    (n b : ℕ) (hn : xs.length ≤ n) (hb : ∀ x ∈ xs, ∀ S, (x.test S).size ≤ b) :
    (patternExpr p xs).size ≤ (n + 2) ^ p.length * (2 * (n + 1) ^ 2 * (b + 2)) := by
  induction p generalizing xs with
  | nil =>
    simp only [patternExpr, Expr.size, List.length_nil, pow_zero, one_mul]
    have : 0 < 2 * (n + 1) ^ 2 * (b + 2) := by positivity
    omega
  | cons piece p ih =>
    cases piece with
    | one S =>
      cases xs with
      | nil =>
        simp only [patternExpr, Expr.size]
        have : 0 < (n + 2) ^ (List.length (Piece.one S :: p)) * (2 * (n + 1) ^ 2 * (b + 2)) := by positivity
        omega
      | cons x xs =>
        have hx := hb x (by simp) S
        have ht := ih xs (by simp_all; omega) (fun x hx S => hb x (List.mem_cons_of_mem _ hx) S)
        simp only [patternExpr, Expr.size, List.length_cons, pow_succ]
        have hp : 1 ≤ (n + 2) ^ p.length := Nat.one_le_pow _ _ (by omega)
        let B := 2 * (n + 1) ^ 2 * (b + 2)
        let A := (n + 2) ^ p.length * B
        have hBA : B ≤ A := by exact Nat.le_mul_of_pos_left B hp
        have hbB : b + 1 ≤ B := by dsimp [B]; nlinarith [Nat.zero_le (n * n * b)]
        change (x.test S).size + (patternExpr p xs).size + 1 ≤ (n + 2) ^ p.length * (n + 2) * B
        calc
          _ ≤ (n + 2) * A := by change (patternExpr p xs).size ≤ A at ht; nlinarith
          _ = _ := by dsimp [A]; ring
    | star S =>
      have ht (k : ℕ) : (patternExpr p (xs.drop k)).size ≤
          (n + 2) ^ p.length * (2 * (n + 1) ^ 2 * (b + 2)) :=
        ih _ (by simp only [List.length_drop]; omega)
          (fun x hx T => hb x (List.mem_of_mem_drop hx) T)
      have hf (k : ℕ) : (Expr.all ((xs.take k).map fun x => x.test S)).size ≤ n * (b + 1) + 1 := by
        have hh := Expr.all_size_le ((xs.take k).map fun x => x.test S) b (by
          intro e he
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
          exact hb x (List.mem_of_mem_take hx) S)
        simp only [List.length_map, List.length_take] at hh
        exact hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega : min k xs.length ≤ n)) _)
      have hh := Expr.any_size_le ((List.range (xs.length + 1)).map fun k =>
        Expr.conj (Expr.all ((xs.take k).map fun x => x.test S)) (patternExpr p (xs.drop k)))
        (n * (b + 1) + 1 + (n + 2) ^ p.length * (2 * (n + 1) ^ 2 * (b + 2)) + 1) (by
          intro e he
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
          simp only [Expr.size]
          exact Nat.add_le_add_right (Nat.add_le_add (hf k) (ht k)) 1)
      simp only [List.length_map, List.length_range] at hh
      change (Expr.any _).size ≤ _
      apply hh.trans
      simp only [List.length_cons, pow_succ]
      have hp : 1 ≤ (n + 2) ^ p.length := Nat.one_le_pow _ _ (by omega)
      let B := 2 * (n + 1) ^ 2 * (b + 2)
      let A := (n + 2) ^ p.length * B
      have hBA : B ≤ A := Nat.le_mul_of_pos_left B hp
      have hB : (n + 1) * (n * (b + 1) + 3) + 1 ≤ B := by
        dsimp [B]; nlinarith [Nat.zero_le (n * n * b)]
      change (xs.length + 1) * (n * (b + 1) + 1 + A + 1 + 1) + 1 ≤
        (n + 2) ^ p.length * (n + 2) * B
      calc
        _ ≤ (n + 1) * (n * (b + 1) + 1 + A + 1 + 1) + 1 := by gcongr
        _ ≤ (n + 2) * A := by nlinarith
        _ = _ := by dsimp [A]; ring

end Lax689614Proofs.Quantified
