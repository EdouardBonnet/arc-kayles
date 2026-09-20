import Lax689614Proofs.PositiveCNF

namespace Lax689614Proofs

open Lax689614 PositiveCNF

theorem passes_empty (φ : Formula) (T : Finset (Fin φ.nvars)) (turn : Bool) (p : ℕ) :
    Passes.TrueWins φ ∅ T turn p ↔ Satisfied φ T := by
  rw [Passes.TrueWins]
  simp

theorem passes_true (φ : Formula) (U T : Finset (Fin φ.nvars)) (p : ℕ) (hne : U ≠ ∅) :
    Passes.TrueWins φ U T true p ↔
      (∃ x ∈ U, ∃ b : Bool,
        Passes.TrueWins φ (U.erase x) (if b then insert x T else T) false p) ∨
      (0 < p ∧ Passes.TrueWins φ U T false (p - 1)) := by
  rw [Passes.TrueWins]
  simp [hne]

theorem passes_false (φ : Formula) (U T : Finset (Fin φ.nvars)) (p : ℕ) (hne : U ≠ ∅) :
    Passes.TrueWins φ U T false p ↔
      (∀ x ∈ U, ∀ b : Bool,
        Passes.TrueWins φ (U.erase x) (if b then insert x T else T) true p) ∧
      (0 < p → Passes.TrueWins φ U T true (p - 1)) := by
  rw [Passes.TrueWins]
  simp [hne]

theorem passes_equivalence (φ : Formula) (U T : Finset (Fin φ.nvars))
    (turn : Bool) (p : ℕ) :
    Passes.TrueWins φ U T turn p ↔ PositiveCNF.TrueWins φ U T turn := by
  induction hn : U.card + p using Nat.strong_induction_on generalizing U T turn p with
  | h n ih =>
    have assign (x : Fin φ.nvars) (hx : x ∈ U) (T' : Finset (Fin φ.nvars)) (turn' : Bool) :
        Passes.TrueWins φ (U.erase x) T' turn' p ↔
          PositiveCNF.TrueWins φ (U.erase x) T' turn' := by
      apply ih ((U.erase x).card + p)
      · have := Finset.card_erase_lt_of_mem hx
        omega
      · rfl
    have pass (hp : 0 < p) (turn' : Bool) :
        Passes.TrueWins φ U T turn' (p - 1) ↔ PositiveCNF.TrueWins φ U T turn' := by
      apply ih (U.card + (p - 1))
      · omega
      · rfl
    by_cases he : U = ∅
    · subst U
      rw [passes_empty, cnf_empty]
    · cases turn
      · rw [passes_false φ U T p he, cnf_false φ U T he]
        constructor
        · rintro ⟨hw, _⟩ x hx
          exact (assign x hx T true).mp (hw x hx false)
        · intro hw
          constructor
          · intro x hx b
            apply (assign x hx _ true).mpr
            cases b
            · exact hw x hx
            · exact cnf_mono φ (U.erase x) T (insert x T) true
                (Finset.subset_insert _ _) (hw x hx)
          · intro hp
            apply (pass hp true).mpr
            exact (cnf_strategy_stealing φ U T).2.2 ((cnf_false φ U T he).mpr hw)
      · rw [passes_true φ U T p he, cnf_true φ U T he]
        constructor
        · rintro (⟨x, hx, b, hw⟩ | ⟨hp, hw⟩)
          · refine ⟨x, hx, ?_⟩
            have hchild := (assign x hx _ false).mp hw
            cases b
            · exact cnf_mono φ (U.erase x) T (insert x T) false
                (Finset.subset_insert _ _) hchild
            · exact hchild
          · apply (cnf_true φ U T he).mp
            exact (cnf_strategy_stealing φ U T).2.2 ((pass hp false).mp hw)
        · rintro ⟨x, hx, hw⟩
          left
          exact ⟨x, hx, true, (assign x hx (insert x T) false).mpr hw⟩

/--
---
conclusion: Lax689614.Passes.outcome_equivalent
---
Strategy stealing shows that moving first cannot hurt True, and assigning
an additional variable to True cannot hurt True. Induction on unassigned
variables plus the pass supply eliminates passes and assignments benefiting
the opponent.
-/
theorem outcome_equivalent (φ : Formula) (U T : Finset (Fin φ.nvars))
    (_hd : Disjoint U T) (turn : Bool) (passes : ℕ) :
    Passes.TrueWins φ U T turn passes ↔ PositiveCNF.TrueWins φ U T turn :=
  passes_equivalence φ U T turn passes

end Lax689614Proofs
