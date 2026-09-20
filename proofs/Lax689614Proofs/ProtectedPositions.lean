import Lax689614Proofs.ExceptionalMove

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles Grundy Biclique
open scoped Classical

noncomputable section

def liveB {φ : Formula} (S : Finset (Vertex φ)) : Finset (Fin φ.clauses.length) :=
  Finset.univ.filter fun j => Vertex.b j ∈ S

def liveZ {φ : Formula} (S : Finset (Vertex φ)) : Finset (Fin (Construction.K φ)) :=
  Finset.univ.filter fun i => Vertex.z i ∈ S

structure Protected {φ : Formula} (S : Finset (Vertex φ)) : Prop where
  clause : ∀ j, Vertex.b j ∈ S → Vertex.a j ∈ S
  varLeaf : ∀ i, Vertex.v i ∈ S → Vertex.vt i ∈ S
  pass : ∀ i, Vertex.y i ∈ S → Vertex.z i ∈ S

theorem regular_protected {φ : Formula} (S : Finset (Vertex φ)) (h : RegularInvariant S) :
    Protected S := ⟨fun j _ => h.a_mem j, h.vt_mem, fun i => (h.yz_mem i).mp⟩

theorem protects_remove {φ : Formula} (S : Finset (Vertex φ)) (h : Protected S)
    (u w : Vertex φ)
    (ha : ∀ j, Vertex.a j = u ∨ Vertex.a j = w → Vertex.b j = u ∨ Vertex.b j = w)
    (ht : ∀ i, Vertex.vt i = u ∨ Vertex.vt i = w → Vertex.v i = u ∨ Vertex.v i = w)
    (hz : ∀ i, Vertex.z i = u ∨ Vertex.z i = w → Vertex.y i = u ∨ Vertex.y i = w) :
    Protected (remove S u w) := by
  have keep {J : Type} (node leaf : J → Vertex φ)
      (hkeep : ∀ i, node i ∈ S → leaf i ∈ S)
      (hdel : ∀ i, leaf i = u ∨ leaf i = w → node i = u ∨ node i = w) :
      ∀ i, node i ∈ remove S u w → leaf i ∈ remove S u w := by
    intro i hi
    obtain ⟨hiw, hiu, hiS⟩ := (remove_mem S u w _).mp hi
    apply (remove_mem S u w _).mpr
    refine ⟨?_, ?_, hkeep i hiS⟩
    · intro he
      rcases hdel i (Or.inr he) with he' | he'
      · exact hiu he'
      · exact hiw he'
    · intro he
      rcases hdel i (Or.inl he) with he' | he'
      · exact hiu he'
      · exact hiw he'
  exact ⟨keep Vertex.b Vertex.a h.clause ha, keep Vertex.v Vertex.vt h.varLeaf ht,
    keep Vertex.y Vertex.z h.pass hz⟩

theorem tail_value_of_protected {φ : Formula} (S : Finset (Vertex φ))
    (hp : ∀ i, Vertex.y i ∈ S → Vertex.z i ∈ S) :
    value (vertexGraph φ) (tail S) = (liveY S).card % 2 := by
  have hpart : Partition (vertexGraph φ) (tail S)
      ((liveY S).image Vertex.y) ∅ ((liveZ S).image Vertex.z) := by
    constructor
    · ext x
      cases x <;> simp [tail, isTail, liveY, liveZ]
    · simp
    · apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      simp at hx'
    · simp
    · intro x hx w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
      simp [vertexGraph, vertexEdge]
    · simp
    · intro x hx w hw
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
      simp [vertexGraph, vertexEdge]
    · simp
    · intro x hx
      simp only [Finset.union_empty] at hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hiS : Vertex.y i ∈ S := (Finset.mem_filter.mp hi).2
      refine ⟨.z i, ?_, (adj_y i (.z i)).mpr (Or.inr rfl), ?_⟩
      · exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp i hiS⟩)
      · intro w _ he
        exact (adj_z i w).mp he
  have h := biclique_value (vertexGraph φ) _ _ _ _ hpart
  simpa [g, Finset.card_image_of_injective (liveY S) (fun _ _ h => Vertex.y.inj h)] using h

theorem protected_value {φ : Formula} (S : Finset (Vertex φ)) (h : Protected S)
    (hs : Vertex.s ∉ S) :
    value (vertexGraph φ) S = Nat.xor (g (liveB S).card (liveV S).card) ((liveY S).card % 2) := by
  have hQ : ∀ j ∈ liveB S, Vertex.b j ∈ S ∧ Vertex.a j ∈ S := by
    intro j hj
    have hb := (Finset.mem_filter.mp hj).2
    exact ⟨hb, h.clause j hb⟩
  have ho : ∀ j, Vertex.b j ∈ S → j ∉ liveB S →
      Vertex.a j ∉ S ∧ ∀ i ∈ φ.clauses[j], Vertex.f i ∉ S := by
    intro j hj hn
    exact False.elim (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩))
  rw [split_value S hs, core_value S (liveB S) hs hQ h.varLeaf ho,
    tail_value_of_protected S h.pass]

theorem central_t_value {φ : Formula} (S : Finset (Vertex φ)) (h : Protected S) :
    value (vertexGraph φ) (remove S .s .t) =
      Nat.xor (g (liveB S).card (liveV S).card) ((liveY S).card % 2) := by
  have hp : Protected (remove S .s .t) := by
    apply protects_remove S h <;> simp
  have hs : Vertex.s ∉ remove S .s .t := by simp [remove]
  have hb : liveB (remove S .s .t) = liveB S := by ext j; simp [liveB, remove]
  have hv : liveV (remove S .s .t) = liveV S := by ext j; simp [liveV, remove]
  have hy : liveY (remove S .s .t) = liveY S := by ext j; simp [liveY, remove]
  rw [protected_value _ hp hs, hb, hv, hy]

theorem central_y_value {φ : Formula} (S : Finset (Vertex φ)) (h : Protected S)
    (i : Fin (Construction.K φ)) :
    value (vertexGraph φ) (remove S .s (.y i)) =
      Nat.xor (g (liveB S).card (liveV S).card) (((liveY S).erase i).card % 2) := by
  have hp : Protected (remove S .s (.y i)) := by
    apply protects_remove S h <;> simp
  have hs : Vertex.s ∉ remove S .s (.y i) := by simp [remove]
  have hb : liveB (remove S .s (.y i)) = liveB S := by ext j; simp [liveB, remove]
  have hv : liveV (remove S .s (.y i)) = liveV S := by ext j; simp [liveV, remove]
  have hy : liveY (remove S .s (.y i)) = (liveY S).erase i := by ext j; simp [liveY, remove]
  rw [protected_value _ hp hs, hb, hv, hy]

end
end Lax689614Proofs
