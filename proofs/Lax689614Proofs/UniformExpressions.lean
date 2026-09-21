import Lax689614Proofs.VariableFoldCode

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax429075Proofs.CircuitBuilder Lax429075Proofs.Streaming
open Lax434930.PolynomialTime

def fixedFold {I α : Type} (conjunction : Bool) (xs : List α) (f : α → Expression I) : Expression I :=
  xs.foldr (fun x rest => Expression.binary conjunction (f x) rest) (.constant (.constant conjunction))

theorem fixedFold_value {I α : Type} (conjunction : Bool) (xs : List α)
    (f : α → Expression I) (a : I → Word) :
    (fixedFold conjunction xs f).value a = foldExpr conjunction (xs.map (fun x => (f x).value a)) := by
  induction xs with
  | nil => cases conjunction <;> rfl
  | cons x xs ih =>
    cases conjunction <;> simp_all [fixedFold, Expression.binary, foldExpr, anyExpr, allExpr]

theorem fixedFold_false_eval {I α : Type} (xs : List α) (f : α → Expression I)
    (a : I → Word) (ρ : ℕ → Bool) :
    ((fixedFold false xs f).value a).eval ρ = true ↔ ∃ x ∈ xs, ((f x).value a).eval ρ = true := by
  induction xs with
  | nil => simp [fixedFold, Expression.constant, Test.constant, Expr.eval]
  | cons x xs ih =>
    change (((f x).value a).eval ρ || ((fixedFold false xs f).value a).eval ρ) = true ↔ _
    simp [ih]

theorem fixedFold_true_eval {I α : Type} (xs : List α) (f : α → Expression I)
    (a : I → Word) (ρ : ℕ → Bool) :
    ((fixedFold true xs f).value a).eval ρ = true ↔ ∀ x ∈ xs, ((f x).value a).eval ρ = true := by
  induction xs with
  | nil => simp [fixedFold, Expression.constant, Test.constant, Expr.eval]
  | cons x xs ih =>
    change (((f x).value a).eval ρ && ((fixedFold true xs f).value a).eval ρ) = true ↔ _
    simp [ih]

def swapOptions {I : Type} : Option (Option I) → Option (Option I)
  | none => some none
  | some none => none
  | some (some i) => some (some i)

theorem extend_swap {I : Type} (a : I → Word) (x y : Word) :
    extend (extend a x) y ∘ swapOptions = extend (extend a y) x := by
  funext i
  cases i with
  | none => rfl
  | some i => cases i <;> rfl

/-- Bind a computed unary parameter before constructing the expression. -/
def bindExpression {I : Type} (n : Number I) (e : Expression (Option I)) : Expression I where
  value a := e.value (extend a (List.replicate (n.value a) true))
  cost := n.bind e.cost
  output := (n.rename some).bind (e.output.rename swapOptions)
  code := .bind (n.code.rename some) (e.code.rename swapOptions)
  cost_correct a := e.cost_correct _
  output_correct a start := by
    simp only [Number.bind, Number.rename, extend_some, extend_swap]
    exact e.output_correct _ start
  correct a start := by
    simp only [Code.eval, Code.eval_rename, Number.correct, extend_some, extend_swap]
    exact e.correct _ start

def iffExpression {I : Type} (p q : Expression I) : Expression I :=
  (p.neg.disj q).conj (q.neg.disj p)

theorem iffExpression_eval {I : Type} (p q : Expression I) (a : I → Word) (ρ : ℕ → Bool) :
    ((iffExpression p q).value a).eval ρ = true ↔ (p.value a).eval ρ = (q.value a).eval ρ := by
  simp only [iffExpression, Expression.conj, Expression.disj, Expression.binary,
    Expression.neg, Expr.eval, Bool.true_eq, Bool.false_eq_true, ↓reduceIte]
  cases (p.value a).eval ρ <;> cases (q.value a).eval ρ <;> decide

structure UniformSymbol (α I : Type) where
  value : (I → Word) → (ℕ → Bool) → α
  test : Set α → Expression I
  correct : ∀ S a ρ, ((test S).value a).eval ρ = true ↔ value a ρ ∈ S

def UniformSymbol.rename {α I J : Type} (f : I → J) (s : UniformSymbol α I) : UniformSymbol α J where
  value a := s.value (a ∘ f)
  test S := (s.test S).rename f
  correct S a ρ := s.correct S (a ∘ f) ρ

def UniformSymbol.at {α I : Type} (i : Number I) (s : UniformSymbol α (Option I)) : UniformSymbol α I where
  value a := s.value (extend a (List.replicate (i.value a) true))
  test S := bindExpression i (s.test S)
  correct S a ρ := s.correct S _ ρ

noncomputable def uniformSymbol {n : ℕ} {α I : Type} (decode : (Fin n → Bool) → α)
    (wires : Fin n → Number I) : UniformSymbol α I := by
  classical
  refine ⟨fun a ρ => decode (fun i => ρ ((wires i).value a)), fun S =>
    fixedFold false Finset.univ.toList (fun v : Fin n → Bool =>
      (Expression.constant (.constant (decide (decode v ∈ S)))).conj
        (fixedFold true (List.finRange n) (fun i => iffExpression (.wire (wires i))
          (.constant (.constant (v i)))))), ?_⟩
  intro S a ρ
  simp only [fixedFold_false_eval,
    Finset.mem_toList, Finset.mem_univ, true_and, Expression.conj, Expression.binary, Expr.eval,
    Bool.true_eq, ↓reduceIte, Expression.constant, Test.constant, Bool.and_eq_true, decide_eq_true_eq,
    fixedFold_true_eval, List.mem_finRange, forall_const,
    iffExpression_eval, Expression.wire]
  constructor
  · rintro ⟨v, hv, he⟩
    have heq : (fun i => ρ ((wires i).value a)) = v := funext he
    exact heq ▸ hv
  · intro h
    exact ⟨fun i => ρ ((wires i).value a), h, fun _ => rfl⟩

noncomputable def UniformSymbol.pair {α γ I : Type} [Fintype α] [Fintype γ]
    (s : UniformSymbol α I) (t : UniformSymbol γ I) : UniformSymbol (α × γ) I := by
  classical
  refine ⟨fun a ρ => (s.value a ρ, t.value a ρ), fun S =>
    fixedFold false Finset.univ.toList (fun p : α × γ =>
      (Expression.constant (.constant (decide (p ∈ S)))).conj
        ((s.test {p.1}).conj (t.test {p.2}))), ?_⟩
  intro S a ρ
  simp only [fixedFold_false_eval, Finset.mem_toList,
    Finset.mem_univ, true_and, Expression.conj, Expression.binary, Bool.true_eq, ↓reduceIte,
    Expr.eval, Expression.constant, Test.constant, Bool.and_eq_true, decide_eq_true_eq,
    s.correct, t.correct, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨x, y⟩, hp, hx, hy⟩; simpa [hx, hy] using hp
  · intro h; exact ⟨(s.value a ρ, t.value a ρ), h, rfl, rfl⟩

end Lax689614Proofs.CircuitStreaming
