import Lax689614Proofs.QuantifiedFormulas
import Lax434930Proofs.SavitchProofs.Reachability

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified

open Lax434930Proofs.SavitchDefinitions.Reachability
open Lax434930Proofs.SavitchProofs (within_one path_splitting)

abbrev Vector (n : ℕ) := Fin n → Bool
abbrev Wires (n : ℕ) (α : Type) := Fin n → Expr α

def vectorEq {n : ℕ} {α : Type} (xs ys : Wires n α) : Expr α :=
  Expr.all ((List.finRange n).map fun i => (xs i).iffBit (ys i))

theorem vectorEq_eval {n : ℕ} {α : Type} (xs ys : Wires n α) (a : α → Bool) :
    (vectorEq xs ys).eval a = true ↔ (fun i => (xs i).eval a) = (fun i => (ys i).eval a) := by
  simp only [vectorEq, Expr.eval_all, List.forall_mem_map, List.mem_finRange, forall_const,
    Expr.eval_iffBit, funext_iff]

abbrev SplitContext (n : ℕ) (α : Type) := Fin n ⊕ (Fin n ⊕ (Fin 1 ⊕ (Fin n ⊕ α)))

def oldIndex {n : ℕ} {α : Type} (i : α) : SplitContext n α := .inr (.inr (.inr (.inr i)))
def midIndex {n : ℕ} {α : Type} (i : Fin n) : SplitContext n α := .inr (.inr (.inr (.inl i)))
def sideIndex {n : ℕ} {α : Type} : SplitContext n α := .inr (.inr (.inl 0))
def leftIndex {n : ℕ} {α : Type} (i : Fin n) : SplitContext n α := .inr (.inl i)
def rightIndex {n : ℕ} {α : Type} (i : Fin n) : SplitContext n α := .inl i

def alignment {n : ℕ} {α : Type} (xs ys : Wires n α) : Expr (SplitContext n α) :=
  .conj
    (vectorEq (fun i => .var (leftIndex i))
      (fun i => Expr.choose (.var sideIndex) ((xs i).rename oldIndex) (.var (midIndex i))))
    (vectorEq (fun i => .var (rightIndex i))
      (fun i => Expr.choose (.var sideIndex) (.var (midIndex i)) ((ys i).rename oldIndex)))

def splitEnv {n : ℕ} {α : Type} (a : α → Bool) (mid : Vector n) (side : Vector 1)
    (left right : Vector n) : SplitContext n α → Bool :=
  Sum.elim right (Sum.elim left (Sum.elim side (Sum.elim mid a)))

theorem alignment_eval {n : ℕ} {α : Type} (xs ys : Wires n α)
    (a : α → Bool) (mid : Vector n) (side : Vector 1) (left right : Vector n) :
    (alignment xs ys).eval (splitEnv a mid side left right) = true ↔
      left = (if side 0 then (fun i => (xs i).eval a) else mid) ∧
      right = (if side 0 then mid else (fun i => (ys i).eval a)) := by
  simp only [alignment, Expr.eval, Bool.and_eq_true, vectorEq_eval,
    Expr.eval_choose, Expr.eval_rename]
  cases hb : side 0 <;>
    simp [splitEnv, leftIndex, rightIndex, sideIndex, oldIndex, midIndex, Expr.eval, hb,
      Function.comp_def]

def reach {n : ℕ} (edge : Expr (Fin n ⊕ Fin n)) :
    (k : ℕ) → {α : Type} → Wires n α → Wires n α → Formula α
  | 0, _, xs, ys => .matrix (.disj (vectorEq xs ys) (edge.subst (Sum.elim xs ys)))
  | k + 1, _, xs, ys => .ex n (.all 1 (.ex n (.ex n
      ((reach edge k (fun i => .var (leftIndex i)) (fun i => .var (rightIndex i))).guard
        (alignment xs ys)))))

def edgeRelation {n : ℕ} (edge : Expr (Fin n ⊕ Fin n)) (x y : Vector n) : Prop :=
  edge.eval (Sum.elim x y) = true

theorem split_quantifiers {n : ℕ} (P : Vector n → Vector n → Prop) (x y : Vector n) :
    (∃ mid : Vector n, ∀ side : Vector 1, ∃ left right : Vector n,
      (left = (if side 0 then x else mid) ∧ right = (if side 0 then mid else y)) ∧ P left right) ↔
      ∃ mid, P x mid ∧ P mid y := by
  constructor
  · rintro ⟨mid, h⟩
    obtain ⟨l, r, ⟨hl, hr⟩, hP⟩ := h (fun _ => true)
    obtain ⟨l', r', ⟨hl', hr'⟩, hP'⟩ := h (fun _ => false)
    simp only [↓reduceIte] at hl hr hl' hr'
    exact ⟨mid, by simpa [hl, hr] using hP, by simpa [hl', hr'] using hP'⟩
  · rintro ⟨mid, hl, hr⟩
    refine ⟨mid, ?_⟩
    intro side
    cases hb : side 0
    · exact ⟨mid, y, by simp [hb], hr⟩
    · exact ⟨x, mid, by simp [hb], hl⟩

theorem holds_reach {n : ℕ} (edge : Expr (Fin n ⊕ Fin n)) (k : ℕ) {α : Type}
    (xs ys : Wires n α) (a : α → Bool) :
    (reach edge k xs ys).Holds a ↔
      Within (edgeRelation edge) (2 ^ k) (fun i => (xs i).eval a) (fun i => (ys i).eval a) := by
  induction k generalizing α with
  | zero =>
    simp only [reach, Formula.Holds, Expr.eval, Bool.or_eq_true, vectorEq_eval,
      Expr.eval_subst, pow_zero, within_one, edgeRelation]
    have he : (fun i => (Sum.elim xs ys i).eval a) =
        Sum.elim (fun i => (xs i).eval a) (fun i => (ys i).eval a) := by
      funext i; cases i <;> rfl
    rw [he]
  | succ k ih =>
    simp only [reach, Formula.Holds, Formula.holds_guard, ih]
    change (∃ mid : Vector n, ∀ side : Vector 1, ∃ left right : Vector n,
      (alignment xs ys).eval (splitEnv a mid side left right) = true ∧
        Within (edgeRelation edge) (2 ^ k) left right) ↔ _
    simp only [alignment_eval, split_quantifiers]
    rw [pow_succ, Nat.mul_two, path_splitting]

theorem reach_variables {n : ℕ} (edge : Expr (Fin n ⊕ Fin n)) (k : ℕ) {α : Type}
    (xs ys : Wires n α) : (reach edge k xs ys).variables = k * (3 * n + 1) := by
  induction k generalizing α with
  | zero => simp [reach, Formula.variables]
  | succ k ih =>
    simp only [reach, Formula.variables, Formula.guard_variables, ih]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

end Lax689614Proofs.Quantified
