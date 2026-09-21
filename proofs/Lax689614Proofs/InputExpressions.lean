import Lax689614Proofs.ConfigurationExpressions

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified

open Lax434930Proofs.SavitchProofs
open PatternAutomata ConfigurationWords
open Lax434930.SpaceMachines Lax434930.PolynomialTime

/-- The suffix after the prescribed prefix is unrestricted. -/
def prefixExpr {α β : Type} : List (Set α) → List (Symbol α β) → Expr β
  | [], _ => .constant true
  | _ :: _, [] => .constant false
  | S :: ps, x :: xs => .conj (x.test S) (prefixExpr ps xs)

theorem prefixExpr_correct {α β : Type} (ps : List (Set α)) (xs : List (Symbol α β)) (a : β → Bool) :
    (prefixExpr ps xs).eval a = true ↔
      Matches (ps.map Piece.one ++ [.star Set.univ]) (xs.map (fun x => x.value a)) := by
  induction ps generalizing xs with
  | nil => simp [prefixExpr, Expr.eval]
  | cons S ps ih =>
    cases xs with
    | nil => simp [prefixExpr, Expr.eval, Matches]
    | cons x xs => simp [prefixExpr, Expr.eval, x.correct, ih, Matches]

theorem prefixExpr_size {α β : Type} (ps : List (Set α)) (xs : List (Symbol α β))
    (b : ℕ) (hb : ∀ x ∈ xs, ∀ S, (x.test S).size ≤ b) :
    (prefixExpr ps xs).size ≤ ps.length * (b + 1) + 1 := by
  induction ps generalizing xs with
  | nil => simp [prefixExpr, Expr.size]
  | cons S ps ih =>
    cases xs with
    | nil => simp [prefixExpr, Expr.size]
    | cons x xs =>
      have hx := hb x (by simp) S
      have ht := ih xs (fun x hx S => hb x (List.mem_cons_of_mem _ hx) S)
      simp only [prefixExpr, Expr.size, List.length_cons]
      nlinarith

theorem matches_singletons {α : Type} (ys : List α) (p : Pattern α) (xs : List α) :
    Matches (ys.map (fun y => Piece.one {y}) ++ p) xs ↔ ∃ zs, xs = ys ++ zs ∧ Matches p zs := by
  induction ys generalizing xs with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.cons_append, matches_one_single, ih]
    constructor
    · rintro ⟨tail, rfl, zs, rfl, hz⟩
      exact ⟨zs, rfl, hz⟩
    · rintro ⟨zs, rfl, hz⟩
      exact ⟨ys ++ zs, rfl, zs, rfl, hz⟩

noncomputable def inputPrefix (M : Machine) (w : Word) (k i : ℕ) : List (Set (Letter M)) :=
  Set.range (fun q => header M q (readInput w i)) ::
    (BinaryCounter.word k i).map (fun b => {bit M b}) ++ [{split M}]

theorem inputPrefix_correct (M : Machine) (w : Word) (k i : ℕ) {β : Type}
    (xs : List (Symbol (Letter M) β)) (a : β → Bool) :
    (prefixExpr (inputPrefix M w k i) xs).eval a = true ↔
      ∃ q tail, xs.map (fun x => x.value a) =
        header M q (readInput w i) :: ((BinaryCounter.word k i).map (bit M) ++ split M :: tail) := by
  rw [prefixExpr_correct]
  simp only [inputPrefix, List.map_cons, List.map_append, List.map_map, List.cons_append,
    matches_one_range, Function.comp_def, List.map_nil, List.append_assoc]
  have he : (fun b => Piece.one ({bit M b} : Set (Letter M))) =
      (fun x => Piece.one ({x} : Set (Letter M))) ∘ bit M := rfl
  rw [he, ← List.map_map]
  simp_rw [matches_singletons]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, matches_one_single,
    matches_star, Set.mem_univ, implies_true, and_true]
  constructor
  · rintro ⟨q, rest, he, tail, hr, final, hf⟩
    exact ⟨q, final, by rw [he, hr, hf]⟩
  · rintro ⟨q, tail, he⟩
    exact ⟨q, _, he, split M :: tail, rfl, tail, rfl⟩

theorem validInput_prefix (M : Machine) (w : Word) (k i : ℕ)
    (hi : i ≤ w.length + 1) (hik : i < 2 ^ k) (q : M.Q) (tail : List (Letter M)) :
    ValidInput M w (header M q (readInput w i) ::
      ((BinaryCounter.word k i).map (bit M) ++ split M :: tail)) := by
  simp only [ValidInput, inputBits, desiredInput, header, List.head?_cons, List.tail_cons]
  rw [take_input]
  simp only [List.map_map, Function.comp_def, bit]
  simp only [List.map_id', BinaryCounter.word_value, Nat.mod_eq_of_lt hik]
  exact ⟨hi, trivial⟩

noncomputable def inputExpr (M : Machine) (w : Word) (k : ℕ) {β : Type}
    (xs : List (Symbol (Letter M) β)) : Expr β :=
  .disj (Expr.all (xs.map (fun x => x.test {Sum.inl false})))
    (.disj (Expr.all (xs.map (fun x => x.test {Sum.inl true})))
      (Expr.any ((List.range (w.length + 2)).map (fun i => prefixExpr (inputPrefix M w k i) xs))))

theorem inputExpr_sound (M : Machine) (w : Word) (k : ℕ) {β : Type}
    (xs : List (Symbol (Letter M) β)) (a : β → Bool) (hk : w.length + 1 < 2 ^ k)
    (h : (inputExpr M w k xs).eval a = true) : ValidInput M w (xs.map (fun x => x.value a)) := by
  simp only [inputExpr, Expr.eval, Bool.or_eq_true, Expr.eval_all, List.forall_mem_map,
    Symbol.correct, Set.mem_singleton_iff, Expr.eval_any] at h
  rcases h with h | h | h
  · have he : xs.map (fun x => x.value a) = List.replicate xs.length (Sum.inl false) := by
      apply List.eq_replicate_iff.mpr
      exact ⟨by simp, by simpa only [List.forall_mem_map] using h⟩
    rw [he]; exact EncodedGraph.special_input M w _ false
  · have he : xs.map (fun x => x.value a) = List.replicate xs.length (Sum.inl true) := by
      apply List.eq_replicate_iff.mpr
      exact ⟨by simp, by simpa only [List.forall_mem_map] using h⟩
    rw [he]; exact EncodedGraph.special_input M w _ true
  · obtain ⟨e, he, ht⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    have hi' : i ≤ w.length + 1 := by have := List.mem_range.mp hi; omega
    obtain ⟨q, tail, he⟩ := (inputPrefix_correct M w k i xs a).mp ht
    rw [he]
    exact validInput_prefix M w k i hi' (hi'.trans_lt hk) q tail

end Lax689614Proofs.Quantified
