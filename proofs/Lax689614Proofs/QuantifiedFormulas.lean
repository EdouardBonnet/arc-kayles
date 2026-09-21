import Mathlib.Tactic

/-!
Auxiliary quantified Boolean syntax for the hardness proof. Quantifiers
bind finite Boolean vectors. Bound and free variables are separated by a
sum, so the construction cannot accidentally capture an endpoint variable.
-/

namespace Lax689614Proofs.Quantified

inductive Expr (α : Type) where
  | var (i : α)
  | constant (b : Bool)
  | neg (p : Expr α)
  | conj (p q : Expr α)
  | disj (p q : Expr α)

def Expr.eval {α : Type} (a : α → Bool) : Expr α → Bool
  | .var i => a i
  | .constant b => b
  | .neg p => !p.eval a
  | .conj p q => p.eval a && q.eval a
  | .disj p q => p.eval a || q.eval a

def Expr.rename {α β : Type} (f : α → β) : Expr α → Expr β
  | .var i => .var (f i)
  | .constant b => .constant b
  | .neg p => .neg (p.rename f)
  | .conj p q => .conj (p.rename f) (q.rename f)
  | .disj p q => .disj (p.rename f) (q.rename f)

theorem Expr.eval_rename {α β : Type} (f : α → β) (p : Expr α) (a : β → Bool) :
    (p.rename f).eval a = p.eval (a ∘ f) := by
  induction p <;> simp_all [Expr.rename, Expr.eval]

def Expr.size {α : Type} : Expr α → ℕ
  | .var _ | .constant _ => 1
  | .neg p => p.size + 1
  | .conj p q | .disj p q => p.size + q.size + 1

theorem Expr.size_rename {α β : Type} (f : α → β) (p : Expr α) :
    (p.rename f).size = p.size := by
  induction p <;> simp_all [Expr.rename, Expr.size]

def Expr.subst {α β : Type} (f : α → Expr β) : Expr α → Expr β
  | .var i => f i
  | .constant b => .constant b
  | .neg p => .neg (p.subst f)
  | .conj p q => .conj (p.subst f) (q.subst f)
  | .disj p q => .disj (p.subst f) (q.subst f)

theorem Expr.eval_subst {α β : Type} (f : α → Expr β) (p : Expr α) (a : β → Bool) :
    (p.subst f).eval a = p.eval (fun i => (f i).eval a) := by
  induction p <;> simp_all [Expr.subst, Expr.eval]

theorem Expr.size_subst_atomic {α β : Type} (f : α → Expr β) (p : Expr α)
    (hf : ∀ i, (f i).size = 1) : (p.subst f).size = p.size := by
  induction p <;> simp_all [Expr.subst, Expr.size]

def Expr.iffBit {α : Type} (p q : Expr α) : Expr α :=
  .conj (.disj (.neg p) q) (.disj (.neg q) p)

theorem Expr.eval_iffBit {α : Type} (p q : Expr α) (a : α → Bool) :
    (p.iffBit q).eval a = true ↔ p.eval a = q.eval a := by
  simp only [Expr.iffBit, Expr.eval]
  cases p.eval a <;> cases q.eval a <;> decide

def Expr.all {α : Type} (ps : List (Expr α)) : Expr α := ps.foldr .conj (.constant true)

theorem Expr.eval_all {α : Type} (ps : List (Expr α)) (a : α → Bool) :
    (Expr.all ps).eval a = true ↔ ∀ p ∈ ps, p.eval a = true := by
  induction ps <;> simp_all [Expr.all, Expr.eval]

def Expr.choose {α : Type} (b p q : Expr α) : Expr α :=
  .disj (.conj b p) (.conj (.neg b) q)

theorem Expr.eval_choose {α : Type} (b p q : Expr α) (a : α → Bool) :
    (Expr.choose b p q).eval a = if b.eval a then p.eval a else q.eval a := by
  simp only [Expr.choose, Expr.eval]
  cases b.eval a <;> simp

inductive Formula : Type → Type 1 where
  | matrix {α : Type} (p : Expr α) : Formula α
  | ex {α : Type} (n : ℕ) (body : Formula (Fin n ⊕ α)) : Formula α
  | all {α : Type} (n : ℕ) (body : Formula (Fin n ⊕ α)) : Formula α

def Formula.Holds {α : Type} : Formula α → (α → Bool) → Prop
  | .matrix p, a => p.eval a = true
  | .ex _ p, a => ∃ v, p.Holds (Sum.elim v a)
  | .all _ p, a => ∀ v, p.Holds (Sum.elim v a)

def Formula.variables {α : Type} : Formula α → ℕ
  | .matrix _ => 0
  | .ex n p | .all n p => n + p.variables

def Formula.matrixSize {α : Type} : Formula α → ℕ
  | .matrix p => p.size
  | .ex _ p | .all _ p => p.matrixSize

def Formula.guard {α : Type} (g : Expr α) : Formula α → Formula α
  | .matrix p => .matrix (.conj g p)
  | .ex n p => .ex n (p.guard (g.rename Sum.inr))
  | .all n p => .all n (p.guard (g.rename Sum.inr))

theorem Formula.holds_guard {α : Type} (g : Expr α) (p : Formula α) (a : α → Bool) :
    (p.guard g).Holds a ↔ g.eval a = true ∧ p.Holds a := by
  induction p with
  | matrix p => simp [Formula.guard, Formula.Holds, Expr.eval]
  | ex n p ih =>
    simp only [Formula.guard, Formula.Holds, ih, Expr.eval_rename]
    change (∃ v, g.eval a = true ∧ p.Holds (Sum.elim v a)) ↔ _
    exact exists_and_left
  | all n p ih =>
    simp only [Formula.guard, Formula.Holds, ih, Expr.eval_rename]
    change (∀ v, g.eval a = true ∧ p.Holds (Sum.elim v a)) ↔ _
    constructor
    · intro h; exact ⟨(h (fun _ => false)).1, fun v => (h v).2⟩
    · rintro ⟨hg, hp⟩ v; exact ⟨hg, hp v⟩

theorem Formula.guard_variables {α : Type} (g : Expr α) (p : Formula α) :
    (p.guard g).variables = p.variables := by
  induction p <;> simp_all [Formula.guard, Formula.variables]

theorem Formula.guard_matrixSize {α : Type} (g : Expr α) (p : Formula α) :
    (p.guard g).matrixSize = g.size + p.matrixSize + 1 := by
  induction p <;> simp_all [Formula.guard, Formula.matrixSize, Expr.size, Expr.size_rename]

end Lax689614Proofs.Quantified
