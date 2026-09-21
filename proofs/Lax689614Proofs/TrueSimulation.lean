import Lax689614Proofs.SatisfiedPhase

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles

theorem true_simulation {φ : Formula} (hm : φ.clauses.length % 2 = 1)
    (S : Finset (Vertex φ)) (hS : VertexReachable φ S)
    (hf : TrueWins φ (pending S) (trueVars S) true)
    (hr : φ.clauses.length + 2 * (pending S).card + 2 ≤ (liveV S).card)
    (hb : (liveV S).card ≤ φ.clauses.length + (liveY S).card)
    (hp : ((liveV S).card + (liveY S).card) % 2 = 1) :
    Winning (vertexGraph φ) S := by
  classical
  generalize hn : (pending S).card = n
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hsat : Satisfied φ (trueVars S)
    · exact satisfied_phase S hS hsat hm (by omega) hb hp
    have hne : pending S ≠ ∅ := by
      intro hempty
      rw [hempty, cnf_empty] at hf
      exact hsat hf
    obtain ⟨i, hi, hfi⟩ := (cnf_true φ _ _ hne).mp hf
    have hiv : Vertex.v (varIndex i) ∈ S := (Finset.mem_filter.mp hi).2
    have hInv := regular_invariant S hS
    have hif := regular_vf S hS i hiv
    let D := remove S (.v (varIndex i)) (.vt (varIndex i))
    have hreg : vertexRegular (.v (varIndex i)) (.vt (varIndex i)) :=
      Or.inl ⟨varIndex i, Or.inl ⟨rfl, rfl⟩⟩
    have hD : VertexReachable φ D := .step hS hiv (hInv.vt_mem _ hiv) (adjacent_vt _) hreg
    have hDI := regular_invariant D hD
    have hUD : pending D = (pending S).erase i := pending_true_move S i
    have hTD : trueVars D = insert i (trueVars S) := trueVars_true_move S i hif
    have hcnfD : TrueWins φ (pending D) (trueVars D) false := by rwa [hUD, hTD]
    have huc : (pending D).card + 1 = (pending S).card := by
      rw [hUD]; exact Finset.card_erase_add_one hi
    have hvc : (liveV D).card + 1 = (liveV S).card := by
      rw [liveV_remove_vt]
      exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiv⟩)
    have hyc : (liveY D).card = (liveY S).card := by
      congr 1; ext j; simp [D, liveY, remove]
    apply (winning_iff_move _ _).mpr
    refine ⟨_, hiv, _, hInv.vt_mem _ hiv, adjacent_vt _, ?_⟩
    intro hw
    obtain ⟨x, hx, z, hz, hxe, hlose⟩ := (winning_iff_move _ D).mp hw
    apply hlose
    by_cases hxreg : vertexRegular x z
    · let E := remove D x z
      have hE : VertexReachable φ E := .step hD hx hz hxe hxreg
      have heff : RegularEffect D E := regular_effect D hD x z hx hz hxreg
      have hcnfE := true_after_regular heff hcnfD
      have hle := effect_pending_le heff
      have hcounts := effect_counts heff
      apply ih (pending E).card (by omega) E hE hcnfE
      · rcases hcounts with h | h <;> omega
      · rcases hcounts with h | h <;> omega
      · rcases hcounts with h | h <;> omega
      · rfl
    · apply regular_deviation_wins D hD hm (by omega) (by omega) x z hx hz hxe hxreg
      rintro ⟨j, _, hj⟩
      obtain ⟨k, hk, hkf⟩ := cnf_winning_no_exhausted D hD false hcnfD j
      exact hj k hk hkf

/--
---
conclusion: Lax689614.Reduction.true_strategy
---
Simulate True's CNF strategy until the formula is satisfied, then consume
the remaining regular moves. The last phase uses paired replies on a
protected biclique with surviving literal witnesses for every clause.
-/
theorem true_strategy (φ : Formula) (hm : φ.clauses.length % 2 = 1)
    (h : FirstWins φ) : Winning (Construction.graph φ) (Construction.board φ) := by
  classical
  rw [board_eq_image φ,
    winning_image (vertexGraph φ) (Construction.graph φ) label (label_injective φ) label_adj]
  apply true_simulation hm Finset.univ .initial
  · simpa [pending, trueVars, FirstWins] using h
  · simp only [pending, liveV, Finset.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    unfold Construction.R; omega
  · simp only [liveV, liveY, Finset.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    unfold Construction.R Construction.K; omega
  · simp only [liveV, liveY, Finset.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
    unfold Construction.R Construction.K; omega

end Lax689614Proofs
