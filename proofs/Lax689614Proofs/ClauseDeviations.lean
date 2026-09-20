import Lax689614Proofs.CentralResponses

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles Grundy Biclique

theorem liveV_remove_b_lower {φ : Formula} (S : Finset (Vertex φ))
    (j : Fin φ.clauses.length) (x : Vertex φ) :
    (liveV S).card - 1 ≤ (liveV (remove S (.b j) x)).card := by
  have hcases : liveV (remove S (.b j) x) = liveV S ∨
      ∃ i, liveV (remove S (.b j) x) = (liveV S).erase i := by
    cases x
    case v i =>
      right
      refine ⟨i, ?_⟩
      ext q; simp [liveV, remove]
    all_goals left; ext i; simp [liveV, remove]
  rcases hcases with h | ⟨i, h⟩
  · rw [h]; omega
  · rw [h]; exact Finset.pred_card_le_card_erase

theorem protected_remove_b {φ : Formula} (S : Finset (Vertex φ)) (h : Protected S)
    (j : Fin φ.clauses.length) (x : Vertex φ) (he : (vertexGraph φ).Adj (.b j) x) :
    Protected (remove S (.b j) x) := by
  rcases (adj_b j x).mp he with rfl | ⟨i, rfl⟩ | ⟨i, _, rfl⟩
  all_goals apply protects_remove S h <;> simp

theorem clause_deviation_winning {φ : Formula} (S : Finset (Vertex φ))
    (h : RegularInvariant S) (hm : φ.clauses.length % 2 = 1)
    (hr : φ.clauses.length ≤ (liveV S).card) (hk : 0 < (liveY S).card)
    (j : Fin φ.clauses.length) (x : Vertex φ) (he : (vertexGraph φ).Adj (.b j) x) :
    Winning (vertexGraph φ) (remove S (.b j) x) := by
  have hp := protected_remove_b S (regular_protected S h) j x he
  have hlow := liveV_remove_b_lower S j x
  have hs : Vertex.s ∈ remove S (.b j) x := by
    rcases (adj_b j x).mp he with rfl | ⟨i, rfl⟩ | ⟨i, _, rfl⟩ <;>
      simpa [remove] using h.s_mem
  have ht : Vertex.t ∈ remove S (.b j) x := by
    rcases (adj_b j x).mp he with rfl | ⟨i, rfl⟩ | ⟨i, _, rfl⟩ <;>
      simpa [remove] using h.t_mem
  have hb : liveB (remove S (.b j) x) = Finset.univ.erase j := by
    rcases (adj_b j x).mp he with rfl | ⟨i, rfl⟩ | ⟨i, _, rfl⟩ <;>
      (ext q; simp [liveB, remove, h.b_mem])
  have hy : liveY (remove S (.b j) x) = liveY S := by
    rcases (adj_b j x).mp he with rfl | ⟨i, rfl⟩ | ⟨i, _, rfl⟩ <;>
      (ext q; simp [liveY, remove])
  apply central_reply_wins _ hp hs ht
  · rwa [hy]
  · rw [hb]
    have hcard : (Finset.univ.erase j).card = φ.clauses.length - 1 := by simp
    rw [hcard]
    omega

end Lax689614Proofs
