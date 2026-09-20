import Lax689614Proofs.ClauseReplies

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles Grundy Biclique

def vertexExceptional {φ : Formula} (S : Finset (Vertex φ)) (u w : Vertex φ) : Prop :=
  ∃ j, sameVertexEdge u w .s (.a j) ∧ ∀ i ∈ φ.clauses[j], Vertex.f i ∉ S

theorem sameVertexEdge_swap {φ : Formula} (u w x y : Vertex φ) :
    sameVertexEdge u w x y ↔ sameVertexEdge w u x y := by
  unfold sameVertexEdge
  tauto

theorem vertexRegular_swap {φ : Formula} (u w : Vertex φ) :
    vertexRegular u w ↔ vertexRegular w u := by
  simp only [vertexRegular, sameVertexEdge_swap u w]

theorem vertexExceptional_swap {φ : Formula} (S : Finset (Vertex φ)) (u w : Vertex φ) :
    vertexExceptional S u w ↔ vertexExceptional S w u := by
  simp only [vertexExceptional, sameVertexEdge_swap u w]

theorem remove_swap {V : Type} [DecidableEq V] (S : Finset V) (u w : V) :
    remove S u w = remove S w u := Finset.erase_right_comm

theorem vertex_deviation_wins {φ : Formula} (S : Finset (Vertex φ)) (h : RegularInvariant S)
    (hm : φ.clauses.length % 2 = 1) (hr : φ.clauses.length ≤ (liveV S).card)
    (hk : 0 < (liveY S).card) (u w : Vertex φ)
    (he : (vertexGraph φ).Adj u w) (hn : ¬ vertexRegular u w)
    (hx : ¬ vertexExceptional S u w) : Winning (vertexGraph φ) (remove S u w) := by
  classical
  have hp := regular_protected S h
  have hmin : min (liveB S).card (liveV S).card % 2 = 1 := by
    rw [liveB_regular S h, Finset.card_univ, Fintype.card_fin]
    omega
  have forward (u w : Vertex φ) (he : vertexEdge φ u w)
      (hn : ¬ vertexRegular u w) (hx : ¬ vertexExceptional S u w) :
      Winning (vertexGraph φ) (remove S u w) := by
    rcases he with ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩ | ⟨j, rfl, rfl⟩ |
      ⟨j, i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, hir, rfl, rfl⟩ |
      ⟨j, i, hi, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩
    · exact central_t_winning S hp hmin
    · have hnot : ¬ ∀ i ∈ φ.clauses[j], Vertex.f i ∉ S := by
        intro hall
        exact hx ⟨j, Or.inl ⟨rfl, rfl⟩, hall⟩
      push_neg at hnot
      obtain ⟨i, hi, hiS⟩ := hnot
      exact clause_escape_winning S h hm hr j i hi hiS
    · rw [remove_swap]
      exact clause_deviation_winning S h hm hr hk j (.a j) ((adj_b j (.a j)).mpr (Or.inl rfl))
    · exact clause_deviation_winning S h hm hr hk j (.v i)
        ((adj_b j (.v i)).mpr (Or.inr (Or.inl ⟨i, rfl⟩)))
    · exact False.elim (hn (Or.inl ⟨i, Or.inl ⟨rfl, rfl⟩⟩))
    · exact False.elim (hn (Or.inr (Or.inl ⟨i, Or.inl ⟨rfl, rfl⟩⟩)))
    · exact clause_deviation_winning S h hm hr hk j (.f i)
        ((adj_b j (.f i)).mpr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))
    · exact central_y_winning S hp i hmin
    · exact False.elim (hn (Or.inr (Or.inr ⟨i, Or.inl ⟨rfl, rfl⟩⟩)))
  rcases ((SimpleGraph.fromRel_adj _ _ _).mp he).2 with he | he
  · exact forward u w he hn hx
  · rw [remove_swap]
    exact forward w u he (fun hh => hn ((vertexRegular_swap w u).mp hh))
      (fun hh => hx ((vertexExceptional_swap S w u).mp hh))

theorem mem_label_image {φ : Formula} (A : Finset (Vertex φ)) (x : Vertex φ) :
    label x ∈ A.image label ↔ x ∈ A := by
  simp only [Finset.mem_image, label_inj, exists_eq_right]

/--
---
conclusion: Lax689614.RegularPlay.deviation_loses
---
Classify the nonregular edges. Removing the central vertex directly leaves
a nonzero value. A move incident to a clause vertex permits a zero-valued
central reply. Opening a clause with a surviving literal permits one of
two zero-valued replies, according to parity.
-/
theorem deviation_loses (φ : Formula) (hm : φ.clauses.length % 2 = 1)
    (S : Finset ℕ) (hS : RegularPlay.Reachable φ S)
    (hr : φ.clauses.length ≤ RegularPlay.remainingV φ S) (hk : 1 ≤ RegularPlay.remainingY φ S)
    (u w : ℕ) (hu : u ∈ S) (hw : w ∈ S) (he : (Construction.graph φ).Adj u w)
    (hn : ¬ RegularPlay.RegularMove φ u w) (hx : ¬ RegularPlay.Exceptional φ S u w) :
    Winning (Construction.graph φ) (remove S u w) := by
  obtain ⟨A, hA, rfl⟩ := reachable_image S hS
  obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
  rw [remainingV_image] at hr
  rw [remainingY_image] at hk
  rw [← remove_image label (label_injective φ),
    winning_image (vertexGraph φ) (Construction.graph φ) label (label_injective φ) label_adj]
  apply vertex_deviation_wins A (regular_invariant A hA) hm hr (by omega) u' w'
    ((label_adj u' w').mp he) (fun hh => hn ((label_regular u' w').mpr hh))
  rintro ⟨j, hs, hj⟩
  apply hx
  refine ⟨j, (label_same_edge u' w' .s (.a j)).mpr hs, ?_⟩
  intro i hi hmem
  exact hj i hi ((mem_label_image A (.f i)).mp hmem)

end Lax689614Proofs
