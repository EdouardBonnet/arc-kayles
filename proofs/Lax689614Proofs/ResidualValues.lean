import Lax689614Proofs.RegularPositions
import Lax689614Proofs.DisjointUnion

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles Grundy Biclique
open scoped Classical

noncomputable section

def isTail {φ : Formula} : Vertex φ → Prop
  | .y _ | .z _ => True
  | _ => False

def core {φ : Formula} (S : Finset (Vertex φ)) : Finset (Vertex φ) :=
  S.filter fun x => ¬ isTail x

def tail {φ : Formula} (S : Finset (Vertex φ)) : Finset (Vertex φ) := S.filter isTail

def liveV {φ : Formula} (S : Finset (Vertex φ)) : Finset (Fin (Construction.R φ)) :=
  Finset.univ.filter fun i => Vertex.v i ∈ S

def liveY {φ : Formula} (S : Finset (Vertex φ)) : Finset (Fin (Construction.K φ)) :=
  Finset.univ.filter fun i => Vertex.y i ∈ S

def coreB {φ : Formula} (Q : Finset (Fin φ.clauses.length)) : Finset (Vertex φ) := Q.image Vertex.b

def coreV {φ : Formula} (S : Finset (Vertex φ)) : Finset (Vertex φ) := (liveV S).image Vertex.v

def coreI {φ : Formula} (S : Finset (Vertex φ)) (Q : Finset (Fin φ.clauses.length)) :
    Finset (Vertex φ) := S.filter fun x => match x with
  | .t | .a _ | .vt _ | .f _ => True
  | .b j => j ∉ Q
  | _ => False

theorem core_partition {φ : Formula} (S : Finset (Vertex φ)) (Q : Finset (Fin φ.clauses.length))
    (hs : Vertex.s ∉ S)
    (hQ : ∀ j ∈ Q, Vertex.b j ∈ S ∧ Vertex.a j ∈ S)
    (hv : ∀ i, Vertex.v i ∈ S → Vertex.vt i ∈ S)
    (ho : ∀ j, Vertex.b j ∈ S → j ∉ Q →
      Vertex.a j ∉ S ∧ ∀ i ∈ φ.clauses[j], Vertex.f i ∉ S) :
    Partition (vertexGraph φ) (core S) (coreB Q) (coreV S) (coreI S Q) := by
  classical
  constructor
  · ext x
    simp only [core, coreB, coreV, coreI, liveV, Finset.mem_union,
      Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    cases x <;> simp [isTail, hs]
    case b j =>
      by_cases hj : j ∈ Q
      · simp [hj, (hQ j hj).1]
      · simp [hj]
  · apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    simp [coreV] at hx'
  · apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    simp [coreI, hj] at hx'
  · apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    simp [coreI] at hx'
  · intro x hx w hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
    simp [vertexGraph, vertexEdge]
  · intro x hx w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hw
    simp [vertexGraph, vertexEdge]
  · intro x hx w hw he
    simp only [coreI, Finset.mem_filter] at hx hw
    clear hQ hv hs
    cases x <;> simp at hx
    all_goals cases w <;> simp at hw
    all_goals simp [vertexGraph, vertexEdge] at he
    all_goals first
      | exact (ho _ hx.1 hx.2).2 _ he hw
      | exact (ho _ hw.1 hw.2).2 _ he hx
      | aesop
  · intro x hx w hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    simp [vertexGraph, vertexEdge]
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      refine ⟨.a j, ?_, ?_, ?_⟩
      · simp [coreI, (hQ j hj).2]
      · exact ((adj_a j (.b j)).mpr (Or.inr rfl)).symm
      · intro w hw he
        rcases (adj_a j w).mp he with rfl | h
        · exact False.elim (hs (Finset.mem_filter.mp hw).1)
        · exact h
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hiS : Vertex.v i ∈ S := (Finset.mem_filter.mp hi).2
      refine ⟨.vt i, ?_, ?_, ?_⟩
      · simp [coreI, hv i hiS]
      · exact ((adj_vt i (.v i)).mpr rfl).symm
      · intro w _ he
        exact (adj_vt i w).mp he

theorem core_value {φ : Formula} (S : Finset (Vertex φ)) (Q : Finset (Fin φ.clauses.length))
    (hs : Vertex.s ∉ S)
    (hQ : ∀ j ∈ Q, Vertex.b j ∈ S ∧ Vertex.a j ∈ S)
    (hv : ∀ i, Vertex.v i ∈ S → Vertex.vt i ∈ S)
    (ho : ∀ j, Vertex.b j ∈ S → j ∉ Q →
      Vertex.a j ∉ S ∧ ∀ i ∈ φ.clauses[j], Vertex.f i ∉ S) :
    value (vertexGraph φ) (core S) = g Q.card (liveV S).card := by
  have h := biclique_value (vertexGraph φ) _ _ _ _ (core_partition S Q hs hQ hv ho)
  simpa only [coreB, coreV,
    Finset.card_image_of_injective Q (fun _ _ h => Vertex.b.inj h),
    Finset.card_image_of_injective (liveV S) (fun _ _ h => Vertex.v.inj h)] using h

theorem tail_value {φ : Formula} (S : Finset (Vertex φ))
    (hp : ∀ i, Vertex.y i ∈ S ↔ Vertex.z i ∈ S) :
    value (vertexGraph φ) (tail S) = (liveY S).card % 2 := by
  classical
  have hpart : Partition (vertexGraph φ) (tail S)
      ((liveY S).image Vertex.y) ∅ ((liveY S).image Vertex.z) := by
    constructor
    · ext x
      cases x <;> simp [tail, isTail, liveY, hp]
    · simp
    · apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      simpa using hx'
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
      refine ⟨.z i, Finset.mem_image_of_mem _ hi, (adj_y i (.z i)).mpr (Or.inr rfl), ?_⟩
      intro w _ he
      exact (adj_z i w).mp he
  have h := biclique_value (vertexGraph φ) _ _ _ _ hpart
  simpa [g, Finset.card_image_of_injective (liveY S) (fun _ _ h => Vertex.y.inj h)] using h

theorem core_tail_union {φ : Formula} (S : Finset (Vertex φ)) : core S ∪ tail S = S := by
  classical
  ext x
  simp only [core, tail, Finset.mem_union, Finset.mem_filter]
  tauto

theorem split_value {φ : Formula} (S : Finset (Vertex φ))
    (hs : Vertex.s ∉ S) :
    value (vertexGraph φ) S = Nat.xor (value (vertexGraph φ) (core S))
      (value (vertexGraph φ) (tail S)) := by
  conv_lhs => rw [← core_tail_union S]
  apply disjoint_union
  · apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx').2
  · intro x hx w hw he
    simp only [core, tail, Finset.mem_filter] at hx hw
    cases x <;> cases w <;> simp_all [isTail, vertexGraph, vertexEdge]

end
end Lax689614Proofs
