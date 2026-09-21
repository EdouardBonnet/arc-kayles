import Lax689614Proofs.UniformValidation

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax429075Proofs.CircuitBuilder Lax429075Proofs.Streaming
open Lax434930.PolynomialTime
open Lax434930Proofs.SavitchProofs.PatternAutomata

@[simp] theorem constant_bounded {I : Type} (t : Test I) (a : I → Word) (b : ℕ) :
    ((Expression.constant t).value a).Bounded b := trivial

@[simp] theorem wire_bounded {I : Type} (i : Number I) (a : I → Word) (b : ℕ) :
    ((Expression.wire i).value a).Bounded b ↔ i.value a < b := Iff.rfl

@[simp] theorem neg_bounded {I : Type} (p : Expression I) (a : I → Word) (b : ℕ) :
    (p.neg.value a).Bounded b ↔ (p.value a).Bounded b := Iff.rfl

@[simp] theorem conj_bounded {I : Type} (p q : Expression I) (a : I → Word) (b : ℕ) :
    ((p.conj q).value a).Bounded b ↔ (p.value a).Bounded b ∧ (q.value a).Bounded b := Iff.rfl

@[simp] theorem disj_bounded {I : Type} (p q : Expression I) (a : I → Word) (b : ℕ) :
    ((p.disj q).value a).Bounded b ↔ (p.value a).Bounded b ∧ (q.value a).Bounded b := Iff.rfl

theorem choose_bounded {I : Type} (t : Test I) (p q : Expression I) (a : I → Word) (b : ℕ)
    (hp : (p.value a).Bounded b) (hq : (q.value a).Bounded b) :
    ((Expression.choose t p q).value a).Bounded b := by
  simp only [Expression.choose]; split_ifs <;> assumption

theorem fold_bounded (c : Bool) (xs : List Expr) (b : ℕ)
    (h : ∀ e ∈ xs, e.Bounded b) : (foldExpr c xs).Bounded b := by
  cases c
  · exact anyExpr_bounded xs b h
  · exact allExpr_bounded xs b h

theorem fixedFold_bounded {I α : Type} (c : Bool) (xs : List α) (f : α → Expression I)
    (a : I → Word) (b : ℕ) (h : ∀ x ∈ xs, ((f x).value a).Bounded b) :
    ((fixedFold c xs f).value a).Bounded b := by
  rw [fixedFold_value]
  apply fold_bounded
  simpa only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using h

theorem variableFold_bounded {I : Type} (c : Bool) (count : Number I) (term : Expression (Option I))
    (a : I → Word) (b : ℕ)
    (h : ∀ i < count.value a, (term.value (extend a (List.replicate i true))).Bounded b) :
    ((variableFold c count term).value a).Bounded b := by
  apply fold_bounded
  simpa only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using h

theorem iffExpression_bounded {I : Type} (p q : Expression I) (a : I → Word) (b : ℕ)
    (hp : (p.value a).Bounded b) (hq : (q.value a).Bounded b) :
    ((iffExpression p q).value a).Bounded b := by simp [iffExpression, hp, hq]

def UniformSymbol.Bounded {α I : Type} (s : UniformSymbol α I) (a : I → Word) (b : ℕ) : Prop :=
  ∀ S, ((s.test S).value a).Bounded b

theorem uniformSymbol_bounded {n : ℕ} {α I : Type} (decode : (Fin n → Bool) → α)
    (wires : Fin n → Number I) (a : I → Word) (b : ℕ) (h : ∀ i, (wires i).value a < b) :
    (uniformSymbol decode wires).Bounded a b := by
  intro S
  apply fixedFold_bounded
  intro v hv
  apply (conj_bounded _ _ _ _).mpr
  refine ⟨trivial, ?_⟩
  apply fixedFold_bounded
  intro i hi
  exact iffExpression_bounded _ _ _ _ (h i) trivial

theorem pair_bounded {α γ I : Type} [Fintype α] [Fintype γ]
    (s : UniformSymbol α I) (t : UniformSymbol γ I) (a : I → Word) (b : ℕ)
    (hs : s.Bounded a b) (ht : t.Bounded a b) : (s.pair t).Bounded a b := by
  intro S
  apply fixedFold_bounded
  intro p hp
  exact ⟨trivial, hs _, ht _⟩

theorem segmentExpression_bounded {α I : Type} (S : Set α) (count start : Number I)
    (source : UniformSymbol α (Option I)) (a : I → Word) (b : ℕ)
    (h : ∀ j < count.value a,
      source.Bounded (extend a (List.replicate (start.value a + j) true)) b) :
    ((segmentExpression S count start source).value a).Bounded b := by
  apply variableFold_bounded
  intro j hj
  simpa only [UniformSymbol.at, UniformSymbol.rename, bindExpression, Expression.rename,
    Number.add, Number.rename, Number.length, extend_some, extend_skip, extend,
    Option.elim_none, List.length_replicate] using h j hj S

theorem patternExpression_bounded {α I : Type} (p : Pattern α) (count start : Number I)
    (source : UniformSymbol α (Option I)) (a : I → Word) (b : ℕ)
    (hle : start.value a ≤ count.value a)
    (h : ∀ j < count.value a, source.Bounded (extend a (List.replicate j true)) b) :
    ((patternExpression p count start source).value a).Bounded b := by
  induction p generalizing I with
  | nil => exact trivial
  | cons piece p ih =>
    cases piece with
    | one S =>
      by_cases hl : start.value a < count.value a
      · simp only [patternExpression, Expression.choose, Test.lt, hl, decide_true, ↓reduceIte]
        apply (conj_bounded _ _ _ _).mpr
        refine ⟨h _ hl S, ih _ _ _ _ ?_ h⟩
        simp only [Number.add, Number.constant]; omega
      · simp only [patternExpression, Expression.choose, Test.lt, hl, decide_false, ↓reduceIte]
        exact trivial
    | star S =>
      apply variableFold_bounded
      intro j hj
      have hj' : j ≤ count.value a - start.value a := by
        simpa only [Number.add, Number.sub, Number.constant, Nat.lt_succ_iff] using hj
      apply (conj_bounded _ _ _ _).mpr
      constructor
      · apply segmentExpression_bounded
        intro u hu
        simp only [Number.length, extend, Option.elim_none, List.length_replicate] at hu
        simpa only [UniformSymbol.Bounded, UniformSymbol.rename, Expression.rename,
          Number.rename, extend_some, extend_skip] using h (start.value a + u) (by omega)
      · apply ih
        · simp only [Number.add, Number.rename, Number.length, extend_some, extend,
            Option.elim_none, List.length_replicate]; omega
        · intro u hu
          simp only [Number.rename, extend_some] at hu
          simpa only [UniformSymbol.Bounded, UniformSymbol.rename, Expression.rename,
            extend_skip] using h u hu

end Lax689614Proofs.CircuitStreaming
