import Lax689614Proofs.Vertices
import Lax689614Proofs.Relabeling
import Lax689614Proofs.Biclique

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles

def varIndex {φ : Formula} (i : Fin φ.nvars) : Fin (Construction.R φ) :=
  ⟨i.val, by unfold Construction.R; have := i.isLt; omega⟩

def sameVertexEdge {φ : Formula} (x w u v : Vertex φ) : Prop :=
  (x = u ∧ w = v) ∨ (x = v ∧ w = u)

def vertexRegular {φ : Formula} (x w : Vertex φ) : Prop :=
  (∃ i, sameVertexEdge x w (.v i) (.vt i)) ∨
  (∃ i, sameVertexEdge x w (.v (varIndex i)) (.f i)) ∨
  (∃ i, sameVertexEdge x w (.y i) (.z i))

theorem label_same_edge {φ : Formula} (x w u v : Vertex φ) :
    RegularPlay.SameEdge (label x) (label w) (label u) (label v) ↔
      sameVertexEdge x w u v := by
  simp only [RegularPlay.SameEdge, sameVertexEdge, label_inj]

theorem label_regular {φ : Formula} (x w : Vertex φ) :
    RegularPlay.RegularMove φ (label x) (label w) ↔ vertexRegular x w := by
  constructor
  · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩ | ⟨i, hi, h⟩)
    · exact Or.inl ⟨⟨i, hi⟩, (label_same_edge x w _ _).mp h⟩
    · exact Or.inr (Or.inl ⟨⟨i, hi⟩, (label_same_edge x w _ _).mp h⟩)
    · exact Or.inr (Or.inr ⟨⟨i, hi⟩, (label_same_edge x w _ _).mp h⟩)
  · rintro (⟨i, h⟩ | ⟨i, h⟩ | ⟨i, h⟩)
    · exact Or.inl ⟨i.val, i.isLt, (label_same_edge x w _ _).mpr h⟩
    · exact Or.inr (Or.inl ⟨i.val, i.isLt, (label_same_edge x w _ _).mpr h⟩)
    · exact Or.inr (Or.inr ⟨i.val, i.isLt, (label_same_edge x w _ _).mpr h⟩)

inductive VertexReachable (φ : Formula) : Finset (Vertex φ) → Prop
  | initial : VertexReachable φ Finset.univ
  | step {S : Finset (Vertex φ)} {u w : Vertex φ} : VertexReachable φ S →
      u ∈ S → w ∈ S → (vertexGraph φ).Adj u w → vertexRegular u w →
      VertexReachable φ (remove S u w)

theorem reachable_image {φ : Formula} (S : Finset ℕ) (h : RegularPlay.Reachable φ S) :
    ∃ A : Finset (Vertex φ), VertexReachable φ A ∧ A.image label = S := by
  induction h with
  | initial => exact ⟨Finset.univ, .initial, (board_eq_image φ).symm⟩
  | @step S u w h hu hw he hr ih =>
    obtain ⟨A, hA, rfl⟩ := ih
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨w', hw', rfl⟩ := Finset.mem_image.mp hw
    refine ⟨remove A u' w', .step hA hu' hw' ((label_adj u' w').mp he)
      ((label_regular u' w').mp hr), ?_⟩
    exact remove_image label (label_injective φ) A u' w'

structure RegularInvariant {φ : Formula} (S : Finset (Vertex φ)) : Prop where
  s_mem : Vertex.s ∈ S
  t_mem : Vertex.t ∈ S
  a_mem : ∀ j, Vertex.a j ∈ S
  b_mem : ∀ j, Vertex.b j ∈ S
  vt_mem : ∀ i, Vertex.v i ∈ S → Vertex.vt i ∈ S
  yz_mem : ∀ i, Vertex.y i ∈ S ↔ Vertex.z i ∈ S

theorem regular_invariant {φ : Formula} (S : Finset (Vertex φ))
    (h : VertexReachable φ S) : RegularInvariant S := by
  induction h with
  | initial => constructor <;> simp
  | @step S u w h hu hw he hr ih =>
    rcases hr with ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ <;>
      rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      constructor
      · simpa [remove] using ih.s_mem
      · simpa [remove] using ih.t_mem
      · intro j; simpa [remove] using ih.a_mem j
      · intro j; simpa [remove] using ih.b_mem j
      · intro j hj
        simp only [remove_mem] at hj ⊢
        have hm := ih.vt_mem j hj.2.2
        simp_all
      · intro j
        simp only [remove_mem]
        have hm := ih.yz_mem j
        simp_all

theorem adj_s {φ : Formula} (w : Vertex φ) :
    (vertexGraph φ).Adj .s w ↔ w = .t ∨ (∃ j, w = .a j) ∨ (∃ i, w = .y i) := by
  cases w <;> simp [vertexGraph, vertexEdge, eq_comm]

theorem adj_t {φ : Formula} (w : Vertex φ) :
    (vertexGraph φ).Adj .t w ↔ w = .s := by
  cases w <;> simp [vertexGraph, vertexEdge, eq_comm]

theorem adj_a {φ : Formula} (j : Fin φ.clauses.length) (w : Vertex φ) :
    (vertexGraph φ).Adj (.a j) w ↔ w = .s ∨ w = .b j := by
  cases w <;> simp [vertexGraph, vertexEdge, eq_comm]

theorem adj_b {φ : Formula} (j : Fin φ.clauses.length) (w : Vertex φ) :
    (vertexGraph φ).Adj (.b j) w ↔ w = .a j ∨ (∃ i, w = .v i) ∨
      (∃ i ∈ φ.clauses[j], w = .f i) := by
  cases w <;> simp [vertexGraph, vertexEdge, eq_comm]

theorem adj_vt {φ : Formula} (i : Fin (Construction.R φ)) (w : Vertex φ) :
    (vertexGraph φ).Adj (.vt i) w ↔ w = .v i := by
  cases w <;> simp [vertexGraph, vertexEdge, eq_comm]

theorem adj_y {φ : Formula} (i : Fin (Construction.K φ)) (w : Vertex φ) :
    (vertexGraph φ).Adj (.y i) w ↔ w = .s ∨ w = .z i := by
  cases w <;> simp [vertexGraph, vertexEdge, eq_comm]

theorem adj_z {φ : Formula} (i : Fin (Construction.K φ)) (w : Vertex φ) :
    (vertexGraph φ).Adj (.z i) w ↔ w = .y i := by
  cases w <;> simp [vertexGraph, vertexEdge, eq_comm]

end Lax689614Proofs
