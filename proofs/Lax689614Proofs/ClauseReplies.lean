import Lax689614Proofs.ClauseDeviations

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles Grundy Biclique

theorem clause_reply_f_value {φ : Formula} (S : Finset (Vertex φ)) (h : Protected S)
    (j : Fin φ.clauses.length) (i : Fin φ.nvars) :
    value (vertexGraph φ) (remove (remove S .s (.a j)) (.b j) (.f i)) =
      Nat.xor (g ((liveB S).erase j).card (liveV S).card) ((liveY S).card % 2) := by
  let D := remove (remove S Vertex.s (Vertex.a j)) (Vertex.b j) (Vertex.f i)
  have horder : D = remove (remove S (.a j) (.b j)) .s (.f i) := by
    simp only [D, remove, Finset.erase_right_comm]
  have hp : Protected D := by
    rw [horder]
    have hbase : Protected (remove S (.a j) (.b j)) := by
      apply protects_remove S h <;> simp
    apply protects_remove _ hbase <;> simp
  have hs : Vertex.s ∉ D := by simp [D, remove]
  have hb : liveB D = (liveB S).erase j := by ext q; simp [liveB, D, remove]
  have hv : liveV D = liveV S := by ext q; simp [liveV, D, remove]
  have hy : liveY D = liveY S := by ext q; simp [liveY, D, remove]
  change value (vertexGraph φ) D = _
  rw [protected_value _ hp hs, hb, hv, hy]

theorem clause_reply_v_value {φ : Formula} (S : Finset (Vertex φ)) (h : Protected S)
    (j : Fin φ.clauses.length) (i : Fin (Construction.R φ)) :
    value (vertexGraph φ) (remove (remove S .s (.a j)) (.b j) (.v i)) =
      Nat.xor (g ((liveB S).erase j).card ((liveV S).erase i).card) ((liveY S).card % 2) := by
  let D := remove (remove S Vertex.s (Vertex.a j)) (Vertex.b j) (Vertex.v i)
  have horder : D = remove (remove S (.a j) (.b j)) .s (.v i) := by
    simp only [D, remove, Finset.erase_right_comm]
  have hp : Protected D := by
    rw [horder]
    have hbase : Protected (remove S (.a j) (.b j)) := by
      apply protects_remove S h <;> simp
    apply protects_remove _ hbase <;> simp
  have hs : Vertex.s ∉ D := by simp [D, remove]
  have hb : liveB D = (liveB S).erase j := by ext q; simp [liveB, D, remove]
  have hv : liveV D = (liveV S).erase i := by ext q; simp [liveV, D, remove]
  have hy : liveY D = liveY S := by ext q; simp [liveY, D, remove]
  change value (vertexGraph φ) D = _
  rw [protected_value _ hp hs, hb, hv, hy]

theorem liveB_regular {φ : Formula} (S : Finset (Vertex φ)) (h : RegularInvariant S) :
    liveB S = Finset.univ := by ext j; simp [liveB, h.b_mem]

theorem clause_escape_winning {φ : Formula} (S : Finset (Vertex φ)) (h : RegularInvariant S)
    (hm : φ.clauses.length % 2 = 1) (hr : φ.clauses.length ≤ (liveV S).card)
    (j : Fin φ.clauses.length) (i : Fin φ.nvars) (hi : i ∈ φ.clauses[j])
    (hiS : Vertex.f i ∈ S) :
    Winning (vertexGraph φ) (remove S .s (.a j)) := by
  have hp := regular_protected S h
  have hjB : j ∈ liveB S := by simp [liveB, h.b_mem]
  have hbcard : ((liveB S).erase j).card = φ.clauses.length - 1 := by
    rw [liveB_regular S h]
    simp
  have hbr : g (φ.clauses.length - 1) (liveV S).card = (liveV S).card % 2 := by
    unfold g; omega
  have hbr' : g (φ.clauses.length - 1) ((liveV S).card - 1) =
      ((liveV S).card - 1) % 2 := by unfold g; omega
  have hjD : Vertex.b j ∈ remove S .s (.a j) := by simp [remove, h.b_mem]
  by_cases hz : ((liveV S).card + (liveY S).card) % 2 = 0
  · have hiD : Vertex.f i ∈ remove S .s (.a j) := by simp [remove, hiS]
    apply winning_of_zero_reply (vertexGraph φ) _ (.b j) (.f i) hjD hiD
      ((adj_b j (.f i)).mpr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))
    rw [clause_reply_f_value S hp j i, hbcard, hbr, parity_xor]
    exact hz
  · have hvpos : 0 < (liveV S).card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hvpos
    have hvS : Vertex.v v ∈ S := (Finset.mem_filter.mp hv).2
    have hvD : Vertex.v v ∈ remove S .s (.a j) := by simp [remove, hvS]
    apply winning_of_zero_reply (vertexGraph φ) _ (.b j) (.v v) hjD hvD
      ((adj_b j (.v v)).mpr (Or.inr (Or.inl ⟨v, rfl⟩)))
    rw [clause_reply_v_value S hp j v, hbcard, Finset.card_erase_of_mem hv, hbr', parity_xor]
    omega

end Lax689614Proofs
