import Lax689614Proofs.FalseSimulation

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles

structure EndgamePosition {φ : Formula} (S : Finset (Vertex φ)) : Prop where
  guarded : Protected S
  s_mem : Vertex.s ∈ S
  t_mem : Vertex.t ∈ S
  noY : ∀ i, Vertex.y i ∉ S
  covered : ∀ j, Vertex.b j ∈ S →
    ∃ i ∈ φ.clauses[j], Vertex.f i ∈ S ∧ Vertex.v (varIndex i) ∉ S

theorem EndgamePosition.liveY_empty {φ : Formula} {S : Finset (Vertex φ)}
    (h : EndgamePosition S) : liveY S = ∅ := by
  ext i; simp [liveY, h.noY]

theorem EndgamePosition.remove_vt {φ : Formula} {S : Finset (Vertex φ)}
    (h : EndgamePosition S) (i : Fin (Construction.R φ)) :
    EndgamePosition (remove S (.v i) (.vt i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply protects_remove S h.guarded <;> simp
  · simpa [remove] using h.s_mem
  · simpa [remove] using h.t_mem
  · intro j; simp [remove, h.noY]
  · intro j hj
    have hjS := (remove_subset S (.v i) (.vt i)) hj
    obtain ⟨k, hk, hf, hv⟩ := h.covered j hjS
    exact ⟨k, hk, by simpa [remove] using hf,
      fun hm => hv ((remove_subset S (.v i) (.vt i)) hm)⟩

theorem EndgamePosition.remove_vf {φ : Formula} {S : Finset (Vertex φ)}
    (h : EndgamePosition S) (i : Fin φ.nvars) (hi : Vertex.v (varIndex i) ∈ S) :
    EndgamePosition (remove S (.v (varIndex i)) (.f i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply protects_remove S h.guarded <;> simp
  · simpa [remove] using h.s_mem
  · simpa [remove] using h.t_mem
  · intro j; simp [remove, h.noY]
  · intro j hj
    have hjS := (remove_subset S (.v (varIndex i)) (.f i)) hj
    obtain ⟨k, hk, hf, hv⟩ := h.covered j hjS
    have hki : k ≠ i := by rintro rfl; exact hv hi
    exact ⟨k, hk, by simpa [remove, hki] using hf,
      fun hm => hv ((remove_subset S (.v (varIndex i)) (.f i)) hm)⟩

theorem EndgamePosition.remove_bv {φ : Formula} {S : Finset (Vertex φ)}
    (h : EndgamePosition S) (j : Fin φ.clauses.length) (i : Fin (Construction.R φ)) :
    EndgamePosition (remove S (.b j) (.v i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply protects_remove S h.guarded <;> simp
  · simpa [remove] using h.s_mem
  · simpa [remove] using h.t_mem
  · intro k; simp [remove, h.noY]
  · intro k hk
    have hkS := (remove_subset S (.b j) (.v i)) hk
    obtain ⟨l, hl, hf, hv⟩ := h.covered k hkS
    exact ⟨l, hl, by simpa [remove] using hf,
      fun hm => hv ((remove_subset S (.b j) (.v i)) hm)⟩

theorem liveV_remove_vt {φ : Formula} (S : Finset (Vertex φ)) (i : Fin (Construction.R φ)) :
    liveV (remove S (.v i) (.vt i)) = (liveV S).erase i := by
  ext j; simp [liveV, remove]

theorem liveB_remove_vt {φ : Formula} (S : Finset (Vertex φ)) (i : Fin (Construction.R φ)) :
    liveB (remove S (.v i) (.vt i)) = liveB S := by
  ext j; simp [liveB, remove]

theorem liveV_remove_vf {φ : Formula} (S : Finset (Vertex φ)) (i : Fin φ.nvars) :
    liveV (remove S (.v (varIndex i)) (.f i)) = (liveV S).erase (varIndex i) := by
  ext j; simp [liveV, remove]

theorem liveB_remove_vf {φ : Formula} (S : Finset (Vertex φ)) (i : Fin φ.nvars) :
    liveB (remove S (.v (varIndex i)) (.f i)) = liveB S := by
  ext j; simp [liveB, remove]

theorem liveV_remove_bv {φ : Formula} (S : Finset (Vertex φ))
    (j : Fin φ.clauses.length) (i : Fin (Construction.R φ)) :
    liveV (remove S (.b j) (.v i)) = (liveV S).erase i := by
  ext k; simp [liveV, remove]

theorem liveB_remove_bv {φ : Formula} (S : Finset (Vertex φ))
    (j : Fin φ.clauses.length) (i : Fin (Construction.R φ)) :
    liveB (remove S (.b j) (.v i)) = (liveB S).erase j := by
  ext k; simp [liveB, remove]

theorem adjacent_vt {φ : Formula} (i : Fin (Construction.R φ)) :
    (vertexGraph φ).Adj (.v i) (.vt i) := by
  exact ((adj_vt i (.v i)).mpr rfl).symm

theorem adjacent_vf {φ : Formula} (i : Fin φ.nvars) :
    (vertexGraph φ).Adj (.v (varIndex i)) (.f i) := by
  simp [vertexGraph, vertexEdge, varIndex]
  exact (varIndex i).isLt

theorem adjacent_bv {φ : Formula} (j : Fin φ.clauses.length) (i : Fin (Construction.R φ)) :
    (vertexGraph φ).Adj (.b j) (.v i) :=
  (adj_b j _).mpr (Or.inr (Or.inl ⟨i, rfl⟩))

end Lax689614Proofs
