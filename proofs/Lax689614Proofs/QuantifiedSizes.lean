import Lax689614Proofs.QuantifiedReachability

namespace Lax689614Proofs.Quantified

theorem Expr.size_iffBit {α : Type} (p q : Expr α) :
    (p.iffBit q).size = 2 * (p.size + q.size) + 5 := by
  simp [Expr.iffBit, Expr.size]; omega

theorem Expr.size_choose {α : Type} (b p q : Expr α) :
    (Expr.choose b p q).size = 2 * b.size + p.size + q.size + 4 := by
  simp [Expr.choose, Expr.size]; omega

theorem Expr.size_all_map {α β : Type} (xs : List α) (f : α → Expr β) (s : ℕ)
    (hs : ∀ i ∈ xs, (f i).size = s) : (Expr.all (xs.map f)).size = xs.length * (s + 1) + 1 := by
  induction xs with
  | nil => simp [Expr.all, Expr.size]
  | cons i xs ih =>
    have hi := hs i List.mem_cons_self
    have hh := ih (fun j hj => hs j (List.mem_cons_of_mem _ hj))
    change (f i).size + (Expr.all (xs.map f)).size + 1 = _
    rw [hi, hh]
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem vectorEq_size {n : ℕ} {α : Type} (xs ys : Wires n α) (r s : ℕ)
    (hx : ∀ i, (xs i).size = r) (hy : ∀ i, (ys i).size = s) :
    (vectorEq xs ys).size = n * (2 * (r + s) + 6) + 1 := by
  rw [vectorEq, Expr.size_all_map _ _ (2 * (r + s) + 5)]
  · simp
  · intro i hi; simp [Expr.size_iffBit, hx, hy]

theorem alignment_size {n : ℕ} {α : Type} (xs ys : Wires n α)
    (hx : ∀ i, (xs i).size = 1) (hy : ∀ i, (ys i).size = 1) :
    (alignment xs ys).size = 48 * n + 3 := by
  unfold alignment
  rw [Expr.size,
    vectorEq_size _ _ 1 8 (by intro i; rfl)
      (by intro i; simp [Expr.size_choose, Expr.size_rename, Expr.size, hx]),
    vectorEq_size _ _ 1 8 (by intro i; rfl)
      (by intro i; simp [Expr.size_choose, Expr.size_rename, Expr.size, hy])]
  omega

theorem reach_matrixSize {n : ℕ} (edge : Expr (Fin n ⊕ Fin n)) (k : ℕ) {α : Type}
    (xs ys : Wires n α) (hx : ∀ i, (xs i).size = 1) (hy : ∀ i, (ys i).size = 1) :
    (reach edge k xs ys).matrixSize = edge.size + 10 * n + 2 + k * (48 * n + 4) := by
  induction k generalizing α with
  | zero =>
    simp only [reach, Formula.matrixSize, Expr.size]
    rw [vectorEq_size xs ys 1 1 hx hy, Expr.size_subst_atomic _ _
      (by intro i; cases i with | inl i => exact hx i | inr i => exact hy i)]
    omega
  | succ k ih =>
    simp only [reach, Formula.matrixSize, Formula.guard_matrixSize]
    rw [alignment_size xs ys hx hy, ih _ _ (by intro i; rfl) (by intro i; rfl)]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

end Lax689614Proofs.Quantified
