import Lax689614Proofs.CNFStrategyComparison

namespace Lax689614Proofs

open Lax689614 PositiveCNF

/-- Only terminal assignments drawn from the available board matter. -/
theorem cnf_payoff_congr_on (n : ℕ) (cs ds : List (Finset (Fin n)))
    (U T T' : Finset (Fin n)) (turn : Bool)
    (h : ∀ S ⊆ U, Satisfied ⟨n, cs⟩ (T ∪ S) ↔ Satisfied ⟨n, ds⟩ (T' ∪ S)) :
    TrueWins ⟨n, cs⟩ U T turn ↔ TrueWins ⟨n, ds⟩ U T' turn := by
  induction hn : U.card using Nat.strong_induction_on generalizing U T T' turn with
  | h m ih =>
    by_cases he : U = ∅
    · subst U
      rw [cnf_empty, cnf_empty]
      simpa using h ∅ (Finset.empty_subset _)
    · cases turn
      · rw [cnf_false _ _ _ he, cnf_false _ _ _ he]
        apply forall_congr'; intro x
        apply forall_congr'; intro hx
        exact ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) _ _ _ true
          (fun S hS => h S (hS.trans (Finset.erase_subset _ _))) rfl
      · rw [cnf_true _ _ _ he, cnf_true _ _ _ he]
        apply exists_congr; intro x
        apply and_congr_right; intro hx
        apply ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) _ _ _ false ?_ rfl
        intro S hS
        have hi : insert x S ⊆ U := Finset.insert_subset hx (hS.trans (Finset.erase_subset _ _))
        simpa only [Finset.insert_union, Finset.union_insert] using h (insert x S) hi

end Lax689614Proofs
