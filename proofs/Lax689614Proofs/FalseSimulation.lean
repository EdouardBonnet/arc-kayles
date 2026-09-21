import Lax689614Proofs.MoveEffects
import Lax689614.Reduction

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles

theorem false_simulation {φ : Formula} (hm : φ.clauses.length % 2 = 1)
    (S : Finset (Vertex φ)) (hS : VertexReachable φ S)
    (hf : ¬ TrueWins φ (pending S) (trueVars S) true)
    (hr : φ.clauses.length + 2 * (pending S).card + 2 ≤ (liveV S).card)
    (hk : (pending S).card + 2 ≤ (liveY S).card)
    (hp : ((liveV S).card + (liveY S).card) % 2 = 1) :
    ¬ Winning (vertexGraph φ) S := by
  classical
  generalize hn : (pending S).card = n
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    intro hw
    obtain ⟨u, hu, w, hw, he, hlose⟩ := (winning_iff_move _ _).mp hw
    apply hlose
    have hInv := regular_invariant S hS
    by_cases hreg : vertexRegular u w
    · let D := remove S u w
      have hD : VertexReachable φ D := .step hS hu hw he hreg
      have hDI := regular_invariant D hD
      have heff : RegularEffect S D := regular_effect S hS u w hu hw hreg
      have hfalse := false_after_regular heff hf
      obtain ⟨hrD, hkD, hpD⟩ := false_resources_after_regular heff hr hk hp
      by_cases hex : ∃ j : Fin φ.clauses.length, ∀ i ∈ φ.clauses[j], Vertex.f i ∉ D
      · obtain ⟨j, hj⟩ := hex
        apply (winning_iff_move _ D).mpr
        refine ⟨.s, hDI.s_mem, .a j, hDI.a_mem j,
          (adj_s (.a j)).mpr (Or.inr (Or.inl ⟨j, rfl⟩)), ?_⟩
        exact (regular_exceptional_losing D hD hm (by omega) j hj).mpr hpD
      · have hne : pending D ≠ ∅ := by
          intro hempty
          apply hex
          apply exhausted_after_assignment D hempty
          intro hs
          apply hfalse
          rw [hempty]
          exact (cnf_empty φ _ false).mpr hs
        rw [cnf_false φ _ _ hne] at hfalse
        push Not at hfalse
        obtain ⟨i, hi, hfi⟩ := hfalse
        have hiv : Vertex.v (varIndex i) ∈ D := (Finset.mem_filter.mp hi).2
        have hif : Vertex.f i ∈ D := regular_vf D hD i hiv
        have hie : (vertexGraph φ).Adj (.v (varIndex i)) (.f i) := by
          simp [vertexGraph, vertexEdge, varIndex]
          exact (varIndex i).isLt
        have hir : vertexRegular (.v (varIndex i)) (.f i) :=
          Or.inr (Or.inl ⟨i, Or.inl ⟨rfl, rfl⟩⟩)
        let E := remove D (.v (varIndex i)) (.f i)
        have hE : VertexReachable φ E := .step hD hiv hif hie hir
        have hUE : pending E = (pending D).erase i := pending_false_move D i
        have hTE : trueVars E = trueVars D := trueVars_false_move D i hiv
        have hcard : (pending E).card + 1 = (pending D).card := by
          rw [hUE]; exact Finset.card_erase_add_one hi
        have hVE : (liveV E).card + 1 = (liveV D).card := by
          have hv : liveV E = (liveV D).erase (varIndex i) := by
            ext j; simp [E, liveV, remove]
          rw [hv]
          exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiv⟩)
        have hYE : (liveY E).card = (liveY D).card := by
          congr 1; ext j; simp [E, liveY, remove]
        have hle := effect_pending_le heff
        have hEloss : ¬ Winning (vertexGraph φ) E := by
          apply ih (pending E).card (by omega) E hE
          · simpa only [hUE, hTE] using hfi
          · omega
          · omega
          · omega
          · rfl
        exact (winning_iff_move _ D).mpr ⟨_, hiv, _, hif, hie, hEloss⟩
    · by_cases hx : vertexExceptional S u w
      · obtain ⟨j, hsame, hj⟩ := hx
        rcases hsame with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · by_contra hl
          have hz := (regular_exceptional_losing S hS hm (by omega) j hj).mp hl
          omega
        · rw [remove_swap]
          by_contra hl
          have hz := (regular_exceptional_losing S hS hm (by omega) j hj).mp hl
          omega
      · exact regular_deviation_wins S hS hm (by omega) (by omega) u w hu hw he hreg hx

/--
---
conclusion: Lax689614.Reduction.false_strategy
---
False responds to each regular move by following a winning CNF strategy.
An exhausted clause supplies a zero-valued exceptional reply. Nonregular
moves are losing deviations, including the exceptional move at odd parity.
-/
theorem false_strategy (φ : Formula) (hm : φ.clauses.length % 2 = 1)
    (h : ¬ FirstWins φ) : ¬ Winning (Construction.graph φ) (Construction.board φ) := by
  classical
  rw [board_eq_image φ,
    winning_image (vertexGraph φ) (Construction.graph φ) label (label_injective φ) label_adj]
  apply false_simulation hm Finset.univ .initial
  · simpa [pending, trueVars, FirstWins] using h
  · simp only [pending, liveV, Finset.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    unfold Construction.R; omega
  · simp only [pending, liveY, Finset.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    unfold Construction.K; omega
  · simp only [liveV, liveY, Finset.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    unfold Construction.R Construction.K; omega

end Lax689614Proofs
