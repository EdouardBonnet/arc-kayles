import Lax689614Proofs.QuantifiedCNF
import Lax689614Proofs.AlternatingCNF

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified

open Lax429075

/-- A single quantifier; `true` denotes a universal quantifier. -/
def quantify {α : Type} (all : Bool) (p : α → Prop) : Prop :=
  if all then ∀ x, p x else ∃ x, p x

theorem quantify_congr {α : Type} (all : Bool) {p q : α → Prop}
    (h : ∀ x, p x ↔ q x) : quantify all p ↔ quantify all q := by
  cases all <;> simp only [quantify, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
  · exact exists_congr h
  · exact forall_congr' h

theorem quantify_vector_succ (all : Bool) (n : ℕ) (p : Vector (n + 1) → Prop) :
    quantify all p ↔ quantify all (fun b => quantify all (fun v => p (Fin.cons b v))) := by
  cases all <;> simp only [quantify, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
  · constructor
    · rintro ⟨v, hv⟩
      exact ⟨v 0, Fin.tail v, by simpa using hv⟩
    · rintro ⟨b, v, hv⟩; exact ⟨Fin.cons b v, hv⟩
  · constructor
    · intro h b v; exact h _
    · intro h v; simpa using h (v 0) (Fin.tail v)

theorem assignBlock_zero (start : ℕ) (v : Vector 0) (a : CNF.Assignment) :
    assignBlock start 0 v a = a := by
  funext j
  simp [assignBlock, show ¬(start ≤ j ∧ j < start + 0) by omega]

theorem assignBlock_succ (start n : ℕ) (b : Bool) (v : Vector n) (a : CNF.Assignment) :
    assignBlock start (n + 1) (Fin.cons b v) a =
      assignBlock (start + 1) n v (Function.update a start b) := by
  funext j
  by_cases hj : j = start
  · subst j
    simp [assignBlock, Fin.cons_zero]
  · by_cases hi : start + 1 ≤ j ∧ j < start + 1 + n
    · have hi' : start ≤ j ∧ j < start + (n + 1) := by omega
      simp only [assignBlock, dif_pos hi, dif_pos hi']
      have he : (⟨j - start, by omega⟩ : Fin (n + 1)) =
          (⟨j - (start + 1), by omega⟩ : Fin n).succ := by
        apply Fin.ext; simp; omega
      rw [he, Fin.cons_succ]
    · have hi' : ¬(start ≤ j ∧ j < start + (n + 1)) := by omega
      simp only [assignBlock, dif_neg hi, dif_neg hi', Function.update_of_ne hj]

def singleHolds (cs : CNF.Formula) : List Bool → ℕ → CNF.Assignment → Prop
  | [], _, a => CNF.eval cs a = true
  | q :: qs, start, a => quantify q (fun b => singleHolds cs qs (start + 1) (Function.update a start b))

def Prefix.expand (qs : Prefix) : List Bool :=
  qs.flatMap fun q => List.replicate q.2 q.1

theorem singleHolds_replicate (cs : CNF.Formula) (q : Bool) (k : ℕ)
    (qs : List Bool) (start : ℕ) (a : CNF.Assignment) :
    singleHolds cs (List.replicate k q ++ qs) start a ↔
      quantify q (fun v : Vector k => singleHolds cs qs (start + k) (assignBlock start k v a)) := by
  induction k generalizing start a with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.add_zero, assignBlock_zero]
    cases q <;> simp [quantify]
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, singleHolds, quantify_vector_succ]
    apply quantify_congr; intro b
    rw [ih]
    apply quantify_congr; intro v
    rw [assignBlock_succ]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem Prefix.expand_correct (cs : CNF.Formula) (qs : Prefix) (start : ℕ) (a : CNF.Assignment) :
    singleHolds cs (Prefix.expand qs) start a ↔ qs.Holds cs start a := by
  induction qs generalizing start a with
  | nil => rfl
  | cons q qs ih =>
    rcases q with ⟨q, k⟩
    rw [Prefix.expand, List.flatMap_cons]
    change singleHolds cs (List.replicate k q ++ Prefix.expand qs) start a ↔ _
    rw [singleHolds_replicate]
    change quantify q _ ↔ quantify q _
    exact quantify_congr q (fun v => ih _ _)

end Lax689614Proofs.Quantified
