import Lax689614Proofs.Endgame

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles

theorem regular_wait_choice {φ : Formula} (S : Finset (Vertex φ))
    (hS : VertexReachable φ S) (hm : φ.clauses.length % 2 = 1)
    (hr : φ.clauses.length ≤ (liveV S).card)
    (hb : (liveV S).card ≤ φ.clauses.length + (liveY S).card)
    (hp : ((liveV S).card + (liveY S).card) % 2 = 1)
    (hend : ¬ ((liveV S).card = φ.clauses.length ∧ liveY S = ∅)) :
    ∃ u ∈ S, ∃ w ∈ S, (vertexGraph φ).Adj u w ∧ vertexRegular u w ∧
      φ.clauses.length ≤ (liveV (remove S u w)).card ∧
      0 < (liveY (remove S u w)).card ∧
      (liveV (remove S u w)).card < φ.clauses.length + (liveY (remove S u w)).card := by
  have h := regular_invariant S hS
  by_cases hgt : φ.clauses.length < (liveV S).card
  · obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (liveV S).card by omega)
    have hiv := (Finset.mem_filter.mp hi).2
    have hc := Finset.card_erase_add_one hi
    have hy : liveY (remove S (.v i) (.vt i)) = liveY S := by ext j; simp [liveY, remove]
    refine ⟨_, hiv, _, h.vt_mem i hiv, adjacent_vt i,
      Or.inl ⟨i, Or.inl ⟨rfl, rfl⟩⟩, ?_⟩
    rw [liveV_remove_vt, hy]; omega
  · have hreq : (liveV S).card = φ.clauses.length := by omega
    have hk : liveY S ≠ ∅ := fun hz => hend ⟨hreq, hz⟩
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hk
    have hiy := (Finset.mem_filter.mp hi).2
    have hc := Finset.card_erase_add_one hi
    have hy : liveY (remove S (.y i) (.z i)) = (liveY S).erase i := by ext j; simp [liveY, remove]
    have hv : liveV (remove S (.y i) (.z i)) = liveV S := by ext j; simp [liveV, remove]
    refine ⟨_, hiy, _, (h.yz_mem i).mp hiy, (adj_y i _).mpr (Or.inr rfl),
      Or.inr (Or.inr ⟨i, Or.inl ⟨rfl, rfl⟩⟩), ?_⟩
    rw [hy, hv]; omega

theorem satisfied_phase {φ : Formula} (S : Finset (Vertex φ)) (hS : VertexReachable φ S)
    (hs : Satisfied φ (trueVars S)) (hm : φ.clauses.length % 2 = 1)
    (hr : φ.clauses.length ≤ (liveV S).card)
    (hb : (liveV S).card ≤ φ.clauses.length + (liveY S).card)
    (hp : ((liveV S).card + (liveY S).card) % 2 = 1) : Winning (vertexGraph φ) S := by
  classical
  generalize hn : (liveV S).card + (liveY S).card = n
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hend : (liveV S).card = φ.clauses.length ∧ liveY S = ∅
    · exact satisfied_endgame S hS hs hm hend.1 hend.2
    obtain ⟨u, hu, w, hw, he, hreg, hrD, hkD, hbD⟩ :=
      regular_wait_choice S hS hm hr hb hp hend
    let D := remove S u w
    change φ.clauses.length ≤ (liveV D).card at hrD
    change 0 < (liveY D).card at hkD
    change (liveV D).card < φ.clauses.length + (liveY D).card at hbD
    have hD : VertexReachable φ D := .step hS hu hw he hreg
    have hDI := regular_invariant D hD
    have heff : RegularEffect S D := regular_effect S hS u w hu hw hreg
    have hsat := effect_satisfied heff hs
    have hcount := effect_counts heff
    have hsum : (liveV D).card + (liveY D).card + 1 = n := by rcases hcount with h | h <;> omega
    apply (winning_iff_move _ _).mpr
    refine ⟨u, hu, w, hw, he, ?_⟩
    intro hwin
    obtain ⟨x, hx, z, hz, hxe, hlose⟩ := (winning_iff_move _ _).mp hwin
    apply hlose
    by_cases hxreg : vertexRegular x z
    · let E := remove D x z
      have hE : VertexReachable φ E := .step hD hx hz hxe hxreg
      have hEI := regular_invariant E hE
      have heffE : RegularEffect D E := regular_effect D hD x z hx hz hxreg
      have hsatE := effect_satisfied heffE hsat
      have hcountE := effect_counts heffE
      by_cases hrE : φ.clauses.length ≤ (liveV E).card
      · apply ih ((liveV E).card + (liveY E).card)
          (by rcases hcountE with h | h <;> omega) E hE hsatE hrE
        · rcases hcountE with h | h <;> omega
        · rcases hcountE with h | h <;> omega
        · rfl
      · apply central_reply_wins E (regular_protected E hEI) hEI.s_mem hEI.t_mem
        · rcases hcountE with h | h <;> omega
        · rw [liveB_regular E hEI, Finset.card_univ, Fintype.card_fin]
          rcases hcountE with h | h <;> omega
    · apply regular_deviation_wins D hD hm hrD hkD x z hx hz hxe hxreg
      rintro ⟨j, _, hj⟩
      obtain ⟨i, hi, hiT⟩ := hsat φ.clauses[j] (List.getElem_mem _)
      exact hj i hi (Finset.mem_filter.mp hiT).2.2

end Lax689614Proofs
