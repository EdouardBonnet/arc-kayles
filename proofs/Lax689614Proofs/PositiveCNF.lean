import Lax689614.Passes
import Mathlib.Tactic

namespace Lax689614Proofs

open Lax689614 PositiveCNF

theorem satisfied_mono (φ : Formula) {T T' : Finset (Fin φ.nvars)}
    (h : T ⊆ T') (hs : Satisfied φ T) : Satisfied φ T' := by
  intro C hC
  obtain ⟨x, hx, ht⟩ := hs C hC
  exact ⟨x, hx, h ht⟩

theorem cnf_empty (φ : Formula) (T : Finset (Fin φ.nvars)) (turn : Bool) :
    PositiveCNF.TrueWins φ ∅ T turn ↔ Satisfied φ T := by
  rw [PositiveCNF.TrueWins]
  simp

theorem cnf_true (φ : Formula) (U T : Finset (Fin φ.nvars)) (hne : U ≠ ∅) :
    PositiveCNF.TrueWins φ U T true ↔
      ∃ x ∈ U, PositiveCNF.TrueWins φ (U.erase x) (insert x T) false := by
  rw [PositiveCNF.TrueWins]
  simp [hne]

theorem cnf_false (φ : Formula) (U T : Finset (Fin φ.nvars)) (hne : U ≠ ∅) :
    PositiveCNF.TrueWins φ U T false ↔
      ∀ x ∈ U, PositiveCNF.TrueWins φ (U.erase x) T true := by
  rw [PositiveCNF.TrueWins]
  simp [hne]

theorem cnf_of_satisfied (φ : Formula) (U T : Finset (Fin φ.nvars))
    (turn : Bool) (hs : Satisfied φ T) : PositiveCNF.TrueWins φ U T turn := by
  induction hn : U.card using Nat.strong_induction_on generalizing U T turn with
  | h n ih =>
    by_cases he : U = ∅
    · subst U
      exact (cnf_empty φ T turn).mpr hs
    · cases turn
      · apply (cnf_false φ U T he).mpr
        intro x hx
        exact ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) _ _ _ hs rfl
      · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
        apply (cnf_true φ U T he).mpr
        refine ⟨x, hx, ?_⟩
        exact ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) _ _ _
          (satisfied_mono φ (Finset.subset_insert _ _) hs) rfl

theorem cnf_mono (φ : Formula) (U T T' : Finset (Fin φ.nvars))
    (turn : Bool) (hTT : T ⊆ T')
    (hw : PositiveCNF.TrueWins φ U T turn) : PositiveCNF.TrueWins φ U T' turn := by
  induction hn : U.card using Nat.strong_induction_on generalizing U T T' turn with
  | h n ih =>
    by_cases he : U = ∅
    · subst U
      exact (cnf_empty φ T' turn).mpr (satisfied_mono φ hTT ((cnf_empty φ T turn).mp hw))
    · cases turn
      · apply (cnf_false φ U T' he).mpr
        intro x hx
        exact ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) _ _ _ _ hTT
          ((cnf_false φ U T he).mp hw x hx) rfl
      · obtain ⟨x, hx, hw⟩ := (cnf_true φ U T he).mp hw
        apply (cnf_true φ U T' he).mpr
        refine ⟨x, hx, ?_⟩
        exact ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) _ _ _ _
          (Finset.insert_subset_insert x hTT) hw rfl

/-- Giving a variable to True cannot hurt True; giving one to False cannot
help True; and changing the next player from False to True cannot hurt True. -/
theorem cnf_strategy_stealing (φ : Formula) (U T : Finset (Fin φ.nvars)) :
    (∀ x ∈ U, ∀ turn : Bool, PositiveCNF.TrueWins φ U T turn →
      PositiveCNF.TrueWins φ (U.erase x) (insert x T) turn) ∧
    (∀ x ∈ U, ∀ turn : Bool, PositiveCNF.TrueWins φ (U.erase x) T turn →
      PositiveCNF.TrueWins φ U T turn) ∧
    (PositiveCNF.TrueWins φ U T false → PositiveCNF.TrueWins φ U T true) := by
  induction hn : U.card using Nat.strong_induction_on generalizing U T with
  | h n ih =>
    have smaller (x : Fin φ.nvars) (hx : x ∈ U) (T' : Finset (Fin φ.nvars)) :=
      ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) (U.erase x) T' rfl
    have giveTrue : ∀ x ∈ U, ∀ turn : Bool, PositiveCNF.TrueWins φ U T turn →
        PositiveCNF.TrueWins φ (U.erase x) (insert x T) turn := by
      intro x hx turn hw
      have hne : U ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩
      cases turn
      · by_cases he : U.erase x = ∅
        · have hchild := (cnf_false φ U T hne).mp hw x hx
          rw [he] at hchild ⊢
          exact (cnf_empty φ _ false).mpr
            (satisfied_mono φ (Finset.subset_insert _ _) ((cnf_empty φ _ true).mp hchild))
        · apply (cnf_false φ (U.erase x) (insert x T) he).mpr
          intro y hy
          obtain ⟨hyx, hyU⟩ := Finset.mem_erase.mp hy
          have hx' : x ∈ U.erase y := Finset.mem_erase.mpr ⟨Ne.symm hyx, hx⟩
          have hchild := (cnf_false φ U T hne).mp hw y hyU
          have hwin := (smaller y hyU T).1 x hx' true hchild
          simpa only [Finset.erase_right_comm] using hwin
      · obtain ⟨y, hy, hw⟩ := (cnf_true φ U T hne).mp hw
        by_cases hyx : y = x
        · subst y
          exact (smaller x hx (insert x T)).2.2 hw
        · have hy' : y ∈ U.erase x := Finset.mem_erase.mpr ⟨hyx, hy⟩
          have hx' : x ∈ U.erase y := Finset.mem_erase.mpr ⟨Ne.symm hyx, hx⟩
          have he : U.erase x ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨y, hy'⟩
          apply (cnf_true φ (U.erase x) (insert x T) he).mpr
          refine ⟨y, hy', ?_⟩
          have hwin := (smaller y hy (insert y T)).1 x hx' false hw
          simpa only [Finset.erase_right_comm, Finset.insert_comm] using hwin
    have giveFalse : ∀ x ∈ U, ∀ turn : Bool, PositiveCNF.TrueWins φ (U.erase x) T turn →
        PositiveCNF.TrueWins φ U T turn := by
      intro x hx turn hw
      have hne : U ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩
      by_cases he : U.erase x = ∅
      · rw [he] at hw
        exact cnf_of_satisfied φ U T turn ((cnf_empty φ T turn).mp hw)
      · cases turn
        · apply (cnf_false φ U T hne).mpr
          intro y hy
          by_cases hyx : y = x
          · subst y
            exact (smaller x hx T).2.2 hw
          · have hy' : y ∈ U.erase x := Finset.mem_erase.mpr ⟨hyx, hy⟩
            have hx' : x ∈ U.erase y := Finset.mem_erase.mpr ⟨Ne.symm hyx, hx⟩
            have hchild := (cnf_false φ (U.erase x) T he).mp hw y hy'
            apply (smaller y hy T).2.1 x hx' true
            simpa only [Finset.erase_right_comm] using hchild
        · obtain ⟨y, hy, hchild⟩ := (cnf_true φ (U.erase x) T he).mp hw
          obtain ⟨hyx, hyU⟩ := Finset.mem_erase.mp hy
          have hx' : x ∈ U.erase y := Finset.mem_erase.mpr ⟨Ne.symm hyx, hx⟩
          apply (cnf_true φ U T hne).mpr
          refine ⟨y, hyU, ?_⟩
          apply (smaller y hyU (insert y T)).2.1 x hx' false
          simpa only [Finset.erase_right_comm] using hchild
    refine ⟨giveTrue, giveFalse, ?_⟩
    intro hw
    by_cases he : U = ∅
    · subst U
      exact (cnf_empty φ T true).mpr ((cnf_empty φ T false).mp hw)
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
      exact (cnf_true φ U T he).mpr ⟨x, hx, giveTrue x hx false hw⟩

end Lax689614Proofs
