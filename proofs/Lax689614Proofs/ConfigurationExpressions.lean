import Lax689614Proofs.EncodedSymbols
import Lax434930Proofs.SavitchProofs.EncodedGraph

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified

open Lax434930Proofs.SavitchProofs

noncomputable def codedSymbols (α : Type) [Fintype α] [Inhabited α] {β : Type} :
    ℕ → List (Expr β) → List (Symbol (FiniteCoding.Letter α) β)
  | 0, _ => []
  | n + 1, xs => codedSymbol α (blockWires xs 0 (FiniteCoding.width α)) ::
      codedSymbols α n (xs.drop (FiniteCoding.width α))

theorem codedSymbols_length (α : Type) [Fintype α] [Inhabited α] {β : Type}
    (n : ℕ) (xs : List (Expr β)) : (codedSymbols α n xs).length = n := by
  induction n generalizing xs <;> simp_all [codedSymbols]

theorem codedSymbols_correct (α : Type) [Fintype α] [Inhabited α] {β : Type}
    (n : ℕ) (xs : List (Expr β)) (a : β → Bool) (hx : xs.length = FiniteCoding.width α * n) :
    (codedSymbols α n xs).map (fun s => s.value a) =
      FiniteCoding.decodeWord α (xs.map (Expr.eval a)) := by
  induction n generalizing xs with
  | zero =>
    have hxs : xs = [] := by simpa using hx
    simp [hxs, codedSymbols]
  | succ n ih =>
    have hw := FiniteCoding.width_pos α
    have hne : xs.map (Expr.eval a) ≠ [] := by
      intro he
      have := congrArg List.length he
      simp only [List.length_map, List.length_nil] at this
      rw [hx] at this
      have hp : 0 < FiniteCoding.width α * (n + 1) := by positivity
      omega
    rw [codedSymbols, List.map_cons, FiniteCoding.decodeWord, if_neg hne]
    congr 1
    · change FiniteCoding.decodeBlock α (vectorWord (fun i =>
        (blockWires xs 0 (FiniteCoding.width α) i).eval a)) = _
      rw [blockWires_eval xs 0 (FiniteCoding.width α) a (by nlinarith)]
      simp
    · rw [ih _ (by simp only [List.length_drop, hx, Nat.mul_succ, Nat.add_sub_cancel]), List.map_drop]

theorem blockWires_atomic {β : Type} (xs : List (Expr β)) (h : ∀ x ∈ xs, x.size = 1)
    (start width : ℕ) (i : Fin width) : (blockWires xs start width i).size = 1 := by
  unfold blockWires
  cases he : xs[start + i.val]? with
  | none => rfl
  | some x =>
    simp only [Option.getD_some]
    exact h x (List.mem_of_getElem? he)

theorem codedSymbols_test_size (α : Type) [Fintype α] [Inhabited α] {β : Type}
    (n : ℕ) (xs : List (Expr β)) (hx : ∀ x ∈ xs, x.size = 1)
    (s : Symbol (FiniteCoding.Letter α) β) (hs : s ∈ codedSymbols α n xs) (S : Set (FiniteCoding.Letter α)) :
    (s.test S).size = 2 ^ FiniteCoding.width α * (10 * FiniteCoding.width α + 4) + 1 := by
  induction n generalizing xs with
  | zero => simp [codedSymbols] at hs
  | succ n ih =>
    rcases List.mem_cons.mp hs with he | hs
    · subst s
      exact symbolTest_size _ _ (blockWires_atomic xs hx _ _) S
    · exact ih _ (fun x hx' => hx x (List.mem_of_mem_drop hx')) hs

noncomputable def Symbol.pair {α γ β : Type} [Fintype α] [Fintype γ]
    (s : Symbol α β) (t : Symbol γ β) : Symbol (α × γ) β := by
  classical
  refine ⟨fun a => (s.value a, t.value a), fun S => Expr.any
    (Finset.univ.toList.map fun p : α × γ => Expr.conj (.constant (decide (p ∈ S)))
      (.conj (s.test {p.1}) (t.test {p.2}))), ?_⟩
  intro S a
  rw [Expr.eval_any]
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨⟨x, y⟩, _, rfl⟩ := List.mem_map.mp he
    simp only [Expr.eval, Bool.and_eq_true, decide_eq_true_eq, s.correct, t.correct,
      Set.mem_singleton_iff] at hv
    simpa [hv.2.1, hv.2.2] using hv.1
  · intro h
    refine ⟨_, List.mem_map.mpr ⟨(s.value a, t.value a), by simp, rfl⟩, ?_⟩
    simp [Expr.eval, s.correct, t.correct, h]

theorem Symbol.pair_test_size {α γ β : Type} [Fintype α] [Fintype γ]
    (s : Symbol α β) (t : Symbol γ β) (b c : ℕ)
    (hs : ∀ S, (s.test S).size ≤ b) (ht : ∀ T, (t.test T).size ≤ c) (S : Set (α × γ)) :
    ((s.pair t).test S).size ≤ Fintype.card α * Fintype.card γ * (b + c + 4) + 1 := by
  classical
  apply (Expr.any_size_le _ (b + c + 3) ?_).trans
  · simp [Fintype.card_prod]
  · intro e he
    obtain ⟨⟨x, y⟩, _, rfl⟩ := List.mem_map.mp he
    simp only [Expr.size]
    have := hs {x}
    have := ht {y}
    omega

noncomputable def pairedSymbols (α : Type) [Fintype α] [Inhabited α] {β : Type}
    (n : ℕ) (xs ys : List (Expr β)) : List (Symbol (FiniteCoding.Letter α × FiniteCoding.Letter α) β) :=
  (codedSymbols α n xs).zipWith Symbol.pair (codedSymbols α n ys)

theorem pairedSymbols_correct (α : Type) [Fintype α] [Inhabited α] {β : Type}
    (n : ℕ) (xs ys : List (Expr β)) (a : β → Bool)
    (hx : xs.length = FiniteCoding.width α * n) (hy : ys.length = FiniteCoding.width α * n) :
    (pairedSymbols α n xs ys).map (fun s => s.value a) =
      List.zip (FiniteCoding.decodeWord α (xs.map (Expr.eval a)))
        (FiniteCoding.decodeWord α (ys.map (Expr.eval a))) := by
  rw [← codedSymbols_correct α n xs a hx, ← codedSymbols_correct α n ys a hy]
  unfold pairedSymbols
  simp only [List.map_zipWith, Symbol.pair]
  rw [List.zip_map]
  rw [List.map_zip_eq_zipWith]
  rfl

end Lax689614Proofs.Quantified
