import Lax689614Proofs.EndgameResponses

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles

theorem endgame_losing {φ : Formula} (S : Finset (Vertex φ)) (h : EndgamePosition S)
    (hb : (liveB S).card % 2 = 1) (hv : (liveV S).card % 2 = 0)
    (hlt : (liveV S).card < (liveB S).card) : ¬ Winning (vertexGraph φ) S := by
  classical
  generalize hn : (liveV S).card = n
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    have reply_v (D : Finset (Vertex φ)) (hD : EndgamePosition D)
        (hB : (liveB D).card = (liveB S).card)
        (hV : (liveV D).card + 1 = (liveV S).card) : Winning (vertexGraph φ) D := by
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (liveV D).card by omega)
      have hiS : Vertex.v i ∈ D := (Finset.mem_filter.mp hi).2
      have hcard := Finset.card_erase_add_one hi
      apply (winning_iff_move _ _).mpr
      refine ⟨_, hiS, _, hD.guarded.varLeaf i hiS, adjacent_vt i, ?_⟩
      apply ih ((liveV D).erase i).card (by omega) _ (hD.remove_vt i)
      · rwa [liveB_remove_vt, hB]
      · rw [liveV_remove_vt]; omega
      · rw [liveV_remove_vt, liveB_remove_vt]; omega
      · rw [liveV_remove_vt]
    have reply_bv (D : Finset (Vertex φ)) (hD : EndgamePosition D)
        (hB : (liveB D).card + 1 = (liveB S).card)
        (hV : (liveV D).card + 1 = (liveV S).card) : Winning (vertexGraph φ) D := by
      obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (liveV D).card by omega)
      obtain ⟨j, hj⟩ := Finset.card_pos.mp (show 0 < (liveB D).card by omega)
      have hiS : Vertex.v i ∈ D := (Finset.mem_filter.mp hi).2
      have hjS : Vertex.b j ∈ D := (Finset.mem_filter.mp hj).2
      have hcv := Finset.card_erase_add_one hi
      have hcb := Finset.card_erase_add_one hj
      apply (winning_iff_move _ _).mpr
      refine ⟨_, hjS, _, hiS, adjacent_bv j i, ?_⟩
      apply ih ((liveV D).erase i).card (by omega) _ (hD.remove_bv j i)
      · rw [liveB_remove_bv]; omega
      · rw [liveV_remove_bv]; omega
      · rw [liveV_remove_bv, liveB_remove_bv]; omega
      · rw [liveV_remove_bv]
    have forward (u w : Vertex φ) (hu : u ∈ S) (hw : w ∈ S)
        (he : vertexEdge φ u w) : Winning (vertexGraph φ) (remove S u w) := by
      rcases he with ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩ | ⟨j, rfl, rfl⟩ |
        ⟨j, i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, hir, rfl, rfl⟩ |
        ⟨j, i, hi, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩
      · exact endgame_central_wins S h hb hv hlt
      · exact endgame_clause_wins S h hb hv hlt j
      · rw [remove_swap]
        exact endgame_bsmall_wins S h hb hv j hw (.a j) (Or.inl rfl)
      · apply reply_bv _ (h.remove_bv j i)
        · rw [liveB_remove_bv]
          exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
        · rw [liveV_remove_bv]
          exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩)
      · apply reply_v _ (h.remove_vt i)
        · rw [liveB_remove_vt]
        · rw [liveV_remove_vt]
          exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
      · apply reply_v _ (h.remove_vf i hu)
        · rw [liveB_remove_vf]
        · rw [liveV_remove_vf]
          exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
      · exact endgame_bsmall_wins S h hb hv j hu (.f i) (Or.inr ⟨i, rfl⟩)
      · exact False.elim (h.noY i hw)
      · exact False.elim (h.noY i hu)
    intro hw
    obtain ⟨u, hu, w, hw, he, hlose⟩ := (winning_iff_move _ _).mp hw
    apply hlose
    rcases ((SimpleGraph.fromRel_adj _ _ _).mp he).2 with he | he
    · exact forward u w hu hw he
    · rw [remove_swap]; exact forward w u hw hu he

theorem satisfied_endgame {φ : Formula} (S : Finset (Vertex φ)) (hS : VertexReachable φ S)
    (hs : Satisfied φ (trueVars S)) (hm : φ.clauses.length % 2 = 1)
    (hr : (liveV S).card = φ.clauses.length) (hk : liveY S = ∅) :
    Winning (vertexGraph φ) S := by
  have h := regular_invariant S hS
  have hE : EndgamePosition S := by
    refine ⟨regular_protected S h, h.s_mem, h.t_mem, ?_, ?_⟩
    · intro i hi
      have hm : i ∈ liveY S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      simpa [hk] using hm
    · intro j _
      obtain ⟨i, hi, hT⟩ := hs φ.clauses[j] (List.getElem_mem _)
      have hT' := (Finset.mem_filter.mp hT).2
      exact ⟨i, hi, hT'.2, hT'.1⟩
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (liveV S).card by omega)
  have hiv : Vertex.v i ∈ S := (Finset.mem_filter.mp hi).2
  have hcv := Finset.card_erase_add_one hi
  apply (winning_iff_move _ _).mpr
  refine ⟨_, hiv, _, h.vt_mem i hiv, adjacent_vt i, ?_⟩
  apply endgame_losing _ (hE.remove_vt i)
  · rw [liveB_remove_vt, liveB_regular S h, Finset.card_univ, Fintype.card_fin]; exact hm
  · rw [liveV_remove_vt]; omega
  · rw [liveV_remove_vt, liveB_remove_vt, liveB_regular S h,
      Finset.card_univ, Fintype.card_fin]; omega

end Lax689614Proofs
