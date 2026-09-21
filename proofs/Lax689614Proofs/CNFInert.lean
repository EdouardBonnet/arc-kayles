import Lax689614Proofs.CNFStrategyComparison

namespace Lax689614Proofs

open Lax689614 PositiveCNF

def PayoffIrrelevant (φ : Formula) (T : Finset (Fin φ.nvars)) (d : Fin φ.nvars) : Prop :=
  ∀ S, Satisfied φ (insert d (T ∪ S)) ↔ Satisfied φ (T ∪ S)

theorem PayoffIrrelevant.after_insert {φ : Formula} {T : Finset (Fin φ.nvars)} {d : Fin φ.nvars}
    (h : PayoffIrrelevant φ T d) (x : Fin φ.nvars) : PayoffIrrelevant φ (insert x T) d := by
  intro S
  simpa only [Finset.insert_union, Finset.union_insert] using h (insert x S)

theorem PayoffIrrelevant.assigned {φ : Formula} {T : Finset (Fin φ.nvars)} {d : Fin φ.nvars}
    (h : PayoffIrrelevant φ T d) (U : Finset (Fin φ.nvars)) (turn : Bool) :
    TrueWins φ U (insert d T) turn ↔ TrueWins φ U T turn := by
  constructor
  · exact cnf_payoff_mono φ U (insert d T) T turn (fun S hs => (h S).mp (by
      simpa only [Finset.insert_union] using hs))
  · exact cnf_mono φ U T (insert d T) turn (Finset.subset_insert _ _)

theorem cnf_ignore_inert (φ : Formula) (U T : Finset (Fin φ.nvars)) (d : Fin φ.nvars)
    (hd : d ∉ U) (h : PayoffIrrelevant φ T d) (turn : Bool) :
    TrueWins φ (insert d U) T turn ↔ TrueWins φ U T turn := by
  induction hn : U.card using Nat.strong_induction_on generalizing U T turn with
  | h n ih =>
    have smaller (x : Fin φ.nvars) (hx : x ∈ U) :=
      ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) (U.erase x)
    have hne : insert d U ≠ ∅ := Finset.insert_ne_empty _ _
    by_cases he : U = ∅
    · subst U
      rw [cnf_empty]
      cases turn
      · rw [cnf_false φ _ T hne]
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false, forall_eq, Finset.erase_singleton]
        rw [Finset.erase_insert (by simp)]
        exact cnf_empty φ T true
      · rw [cnf_true φ _ T hne]
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false, exists_eq_left, Finset.erase_singleton]
        rw [Finset.erase_insert (by simp), cnf_empty]
        simpa using h ∅
    · cases turn
      · rw [cnf_false φ _ T hne, cnf_false φ U T he]
        constructor
        · intro hw x hx
          have hxd : x ≠ d := fun hh => hd (hh ▸ hx)
          have ht := hw x (Finset.mem_insert_of_mem hx)
          rw [Finset.erase_insert_of_ne (Ne.symm hxd)] at ht
          exact (smaller x hx T (by simp [hd]) h true rfl).mp ht
        · intro hw x hx
          rcases Finset.mem_insert.mp hx with hxd | hx
          · subst x
            rw [Finset.erase_insert hd]
            exact (cnf_strategy_stealing φ U T).2.2 ((cnf_false φ U T he).mpr hw)
          · have hxd : x ≠ d := fun hh => hd (hh ▸ hx)
            rw [Finset.erase_insert_of_ne (Ne.symm hxd)]
            exact (smaller x hx T (by simp [hd]) h true rfl).mpr (hw x hx)
      · rw [cnf_true φ _ T hne, cnf_true φ U T he]
        constructor
        · rintro ⟨x, hx, hw⟩
          rcases Finset.mem_insert.mp hx with hxd | hx
          · subst x
            rw [Finset.erase_insert hd] at hw
            have hh := (h.assigned U false).mp hw
            exact (cnf_true φ U T he).mp ((cnf_strategy_stealing φ U T).2.2 hh)
          · have hxd : x ≠ d := fun hh => hd (hh ▸ hx)
            rw [Finset.erase_insert_of_ne (Ne.symm hxd)] at hw
            exact ⟨x, hx, (smaller x hx (insert x T) (by simp [hd]) (h.after_insert x) false rfl).mp hw⟩
        · rintro ⟨x, hx, hw⟩
          have hxd : x ≠ d := fun hh => hd (hh ▸ hx)
          refine ⟨x, Finset.mem_insert_of_mem hx, ?_⟩
          rw [Finset.erase_insert_of_ne (Ne.symm hxd)]
          exact (smaller x hx (insert x T) (by simp [hd]) (h.after_insert x) false rfl).mpr hw

theorem irrelevant_of_hit_clauses (φ : Formula) (T : Finset (Fin φ.nvars)) (d : Fin φ.nvars)
    (h : ∀ C ∈ φ.clauses, d ∈ C → ∃ x ∈ C, x ∈ T) : PayoffIrrelevant φ T d := by
  intro S
  constructor
  · intro hs C hC
    obtain ⟨x, hx, ht⟩ := hs C hC
    rcases Finset.mem_insert.mp ht with rfl | ht
    · obtain ⟨y, hy, hyT⟩ := h C hC hx
      exact ⟨y, hy, Finset.mem_union_left _ hyT⟩
    · exact ⟨x, hx, ht⟩
  · exact satisfied_mono φ (Finset.subset_insert _ _)

end Lax689614Proofs
