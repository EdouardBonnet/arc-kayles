import Lax689614Proofs.AlternatingNormalization

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified

open Lax429075
open Lax429075Proofs.CircuitBuilder (compile compile_ordered compile_output compile_length)

theorem gateClauses_bounded (r i : ℕ) (g : Circuits.Gate) (hi : i < r)
    (hg : ∀ j ∈ g.inputs, j < r) : CNFBounded r (Tseitin.gateClauses i g) := by
  cases g <;> simp_all [CNFBounded, Tseitin.gateClauses, Tseitin.positive,
    Tseitin.negative, Circuits.Gate.inputs]

theorem fragmentCNF_bounded (start : ℕ) (e : Lax429075Proofs.CircuitBuilder.Expr)
    (he : e.Bounded start) : CNFBounded (start + (compile start e).gates.length) (fragmentCNF start e) := by
  intro C hC l hl
  rcases List.mem_append.mp hC with hC | hC
  · simp only [List.mem_singleton] at hC
    subst C
    simp only [List.mem_singleton] at hl
    subst l
    exact compile_output start e he
  · obtain ⟨⟨g, i⟩, hgi, hC⟩ := List.mem_flatMap.mp hC
    have hi : i < start + (compile start e).gates.length := by
      have := List.snd_lt_of_mem_zipIdx hgi
      omega
    exact gateClauses_bounded _ i g hi
      (fun j hj => (compile_ordered start e he g i hgi j hj).trans hi) C hC l hl

theorem Prefix.expand_cons (q : Bool) (k : ℕ) (qs : Prefix) :
    (Prefix.expand ((q, k) :: qs)).length = k + (Prefix.expand qs).length := by
  simp [Prefix.expand]

theorem Formula.toCNF_bounded {α : Type} (p : Formula α) (index : α → ℕ)
    (start : ℕ) (h : ∀ i, index i < start) :
    CNFBounded (start + (Prefix.expand (p.toCNF index start).1).length) (p.toCNF index start).2 := by
  induction p generalizing start with
  | matrix p =>
    simpa [Formula.toCNF, Prefix.expand] using
      fragmentCNF_bounded start (p.toCircuit index) (p.toCircuit_bounded index start h)
  | ex k p ih | all k p ih =>
    simpa only [Formula.toCNF, Prefix.expand_cons, Nat.add_assoc] using
      ih (bindIndex start index) (start + k) (bindIndex_bounded start index k h)

theorem Expr.toCircuit_cost_le {α : Type} (p : Expr α) (index : α → ℕ) :
    (p.toCircuit index).cost ≤ p.size := by
  induction p <;> simp_all [Expr.toCircuit, Lax429075Proofs.CircuitBuilder.Expr.cost, Expr.size]
  all_goals omega

theorem Formula.toCNF_variables_le {α : Type} (p : Formula α) (index : α → ℕ) (start : ℕ) :
    (Prefix.expand (p.toCNF index start).1).length ≤ p.variables + p.matrixSize := by
  induction p generalizing start with
  | matrix p =>
    simpa [Formula.toCNF, Prefix.expand, Formula.variables, Formula.matrixSize, compile_length] using
      p.toCircuit_cost_le index
  | ex k p ih | all k p ih =>
    simp only [Formula.toCNF, Prefix.expand_cons, Formula.variables, Formula.matrixSize]
    have := ih (bindIndex start index) (start + k)
    omega

/-- A closed quantified formula is converted to a positive-CNF game. This is
    the semantic map; the word-level polynomial-time certificate is separate. -/
def Formula.toPositive (p : Formula Empty) : Lax689614.PositiveCNF.Formula :=
  let c := p.toCNF Empty.elim 0
  let qs := Prefix.expand c.1
  Byskov.positiveFormula (signedFormula qs.length (fun i => qs[i.val]) c.2)

theorem Formula.toPositive_correct (p : Formula Empty) :
    Lax689614.PositiveCNF.FirstWins p.toPositive ↔ p.Holds Empty.elim := by
  have hb := p.toCNF_bounded Empty.elim 0 (fun i => Empty.elim i)
  simp only [Nat.zero_add] at hb
  rw [Formula.toPositive, blockCNF_positive_correct _ _ hb,
    Formula.toCNF_correct _ _ _ (fun i => Empty.elim i)]
  have he : (fun _ : ℕ => false) ∘ (Empty.elim : Empty → ℕ) = Empty.elim := by
    funext i; exact Empty.elim i
  rw [he]

theorem Formula.toPositive_variables_le (p : Formula Empty) :
    p.toPositive.nvars ≤ 9 * (p.variables + p.matrixSize) + 1 := by
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 9 (p.toCNF_variables_le Empty.elim 0)) 1

end Lax689614Proofs.Quantified
