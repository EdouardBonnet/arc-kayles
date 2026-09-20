import Lax689614Proofs.EndgamePositions

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles Grundy Biclique

theorem endgame_bsmall_wins {φ : Formula} (S : Finset (Vertex φ)) (h : EndgamePosition S)
    (hb : (liveB S).card % 2 = 1) (hv : (liveV S).card % 2 = 0)
    (j : Fin φ.clauses.length) (hj : Vertex.b j ∈ S)
    (x : Vertex φ) (hx : x = .a j ∨ ∃ i, x = .f i) :
    Winning (vertexGraph φ) (remove S (.b j) x) := by
  have hp : Protected (remove S (.b j) x) := by
    rcases hx with rfl | ⟨i, rfl⟩ <;> apply protects_remove S h.guarded <;> simp
  have hs : Vertex.s ∈ remove S (.b j) x := by
    rcases hx with rfl | ⟨i, rfl⟩ <;> simpa [remove] using h.s_mem
  have ht : Vertex.t ∈ remove S (.b j) x := by
    rcases hx with rfl | ⟨i, rfl⟩ <;> simpa [remove] using h.t_mem
  have hB : liveB (remove S (.b j) x) = (liveB S).erase j := by
    rcases hx with rfl | ⟨i, rfl⟩ <;> (ext k; simp [liveB, remove])
  have hV : liveV (remove S (.b j) x) = liveV S := by
    rcases hx with rfl | ⟨i, rfl⟩ <;> (ext k; simp [liveV, remove])
  have hY : liveY (remove S (.b j) x) = ∅ := by
    rcases hx with rfl | ⟨i, rfl⟩ <;> (ext k; simp [liveY, remove, h.noY])
  have hcard : ((liveB S).erase j).card + 1 = (liveB S).card :=
    Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  apply winning_of_zero_reply _ _ .s .t hs ht ((adj_s .t).mpr (Or.inl rfl))
  rw [central_t_value _ hp, hB, hV, hY]
  have hg : g ((liveB S).erase j).card (liveV S).card = 0 := by unfold g; omega
  simp only [hg, Finset.card_empty, Nat.zero_mod]; decide

theorem endgame_central_wins {φ : Formula} (S : Finset (Vertex φ)) (h : EndgamePosition S)
    (hb : (liveB S).card % 2 = 1) (hv : (liveV S).card % 2 = 0)
    (hlt : (liveV S).card < (liveB S).card) :
    Winning (vertexGraph φ) (remove S .s .t) := by
  apply winning_of_value_ne_zero
  rw [central_t_value S h.guarded, h.liveY_empty]
  have hg : g (liveB S).card (liveV S).card = 1 := by unfold g; omega
  simp only [hg, Finset.card_empty, Nat.zero_mod]; decide

theorem endgame_clause_wins {φ : Formula} (S : Finset (Vertex φ)) (h : EndgamePosition S)
    (hb : (liveB S).card % 2 = 1) (hv : (liveV S).card % 2 = 0)
    (hlt : (liveV S).card < (liveB S).card) (j : Fin φ.clauses.length) :
    Winning (vertexGraph φ) (remove S .s (.a j)) := by
  by_cases hj : Vertex.b j ∈ S
  · obtain ⟨i, hi, hif, _⟩ := h.covered j hj
    have hjD : Vertex.b j ∈ remove S .s (.a j) := by simp [remove, hj]
    have hiD : Vertex.f i ∈ remove S .s (.a j) := by simp [remove, hif]
    apply winning_of_zero_reply _ _ (.b j) (.f i) hjD hiD
      ((adj_b j _).mpr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))
    rw [clause_reply_f_value S h.guarded, h.liveY_empty]
    have hcard : ((liveB S).erase j).card + 1 = (liveB S).card :=
      Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
    have hg : g ((liveB S).erase j).card (liveV S).card = 0 := by unfold g; omega
    simp only [hg, Finset.card_empty, Nat.zero_mod]; decide
  · have hp : Protected (remove S .s (.a j)) := by
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        have hkS := (remove_subset S .s (.a j)) hk
        have hkj : k ≠ j := by rintro rfl; exact hj hkS
        simpa [remove, hkj] using h.guarded.clause k hkS
      · intro i hi
        have hiS := (remove_subset S .s (.a j)) hi
        simpa [remove] using h.guarded.varLeaf i hiS
      · intro i hi
        exact False.elim (h.noY i ((remove_subset S .s (.a j)) hi))
    have hB : liveB (remove S .s (.a j)) = liveB S := by ext k; simp [liveB, remove]
    have hV : liveV (remove S .s (.a j)) = liveV S := by ext k; simp [liveV, remove]
    have hY : liveY (remove S .s (.a j)) = ∅ := by ext k; simp [liveY, remove, h.noY]
    apply winning_of_value_ne_zero
    rw [protected_value _ hp (by simp [remove]), hB, hV, hY]
    have hg : g (liveB S).card (liveV S).card = 1 := by unfold g; omega
    simp only [hg, Finset.card_empty, Nat.zero_mod]; decide

end Lax689614Proofs
