import Lax689614.RegularPlay
import Lax689614Proofs.Grundy
import Mathlib.Tactic.DeriveFintype

namespace Lax689614Proofs

open Lax689614 PositiveCNF

inductive Vertex (φ : Formula)
  | s | t
  | a : Fin φ.clauses.length → Vertex φ
  | b : Fin φ.clauses.length → Vertex φ
  | v : Fin (Construction.R φ) → Vertex φ
  | vt : Fin (Construction.R φ) → Vertex φ
  | f : Fin φ.nvars → Vertex φ
  | y : Fin (Construction.K φ) → Vertex φ
  | z : Fin (Construction.K φ) → Vertex φ
  deriving DecidableEq, Fintype

def label {φ : Formula} : Vertex φ → ℕ
  | .s => Construction.s
  | .t => Construction.t
  | .a j => Construction.a φ j
  | .b j => Construction.b φ j
  | .v i => Construction.v φ i
  | .vt i => Construction.vt φ i
  | .f i => Construction.f φ i
  | .y i => Construction.y φ i
  | .z i => Construction.z φ i

theorem label_injective (φ : Formula) : Function.Injective (@label φ) := by
  intro x y he
  cases x <;> cases y <;>
    simp only [label, Construction.s, Construction.t, Construction.a, Construction.b,
      Construction.v, Construction.vt, Construction.f, Construction.y, Construction.z,
      Construction.R, Construction.K] at he
  all_goals first | rfl | omega | (congr 1; apply Fin.ext; omega)

@[simp] theorem label_inj {φ : Formula} (x y : Vertex φ) : label x = label y ↔ x = y :=
  (label_injective φ).eq_iff

theorem label_mem_board {φ : Formula} (x : Vertex φ) : label x ∈ Construction.board φ := by
  cases x <;>
    simp only [label, Construction.board, Finset.mem_range, Construction.size,
      Construction.s, Construction.t, Construction.a, Construction.b, Construction.v,
      Construction.vt, Construction.f, Construction.y, Construction.z,
      Construction.R, Construction.K]
  all_goals omega

def vertexEdge (φ : Formula) (x w : Vertex φ) : Prop :=
  (x = .s ∧ w = .t) ∨
  (∃ j, x = .s ∧ w = .a j) ∨
  (∃ j, x = .a j ∧ w = .b j) ∨
  (∃ j i, x = .b j ∧ w = .v i) ∨
  (∃ i, x = .v i ∧ w = .vt i) ∨
  (∃ i : Fin φ.nvars, ∃ h : i.val < Construction.R φ,
    x = .v ⟨i.val, h⟩ ∧ w = .f i) ∨
  (∃ j : Fin φ.clauses.length, ∃ i ∈ φ.clauses[j], x = .b j ∧ w = .f i) ∨
  (∃ i, x = .s ∧ w = .y i) ∨
  (∃ i, x = .y i ∧ w = .z i)

def vertexGraph (φ : Formula) : SimpleGraph (Vertex φ) := SimpleGraph.fromRel (vertexEdge φ)

theorem label_edge {φ : Formula} (x w : Vertex φ) :
    Construction.Edge φ (label x) (label w) ↔ vertexEdge φ x w := by
  have inj := label_injective φ
  constructor
  · rintro (hst | hsa | hab | hbv | hvt | hvf | hbf | hsy | hyz)
    · exact Or.inl ⟨inj hst.1, inj hst.2⟩
    · obtain ⟨j, hj, hx, hw⟩ := hsa
      exact Or.inr (Or.inl ⟨⟨j, hj⟩, inj hx, inj hw⟩)
    · obtain ⟨j, hj, hx, hw⟩ := hab
      exact Or.inr (Or.inr (Or.inl ⟨⟨j, hj⟩, inj hx, inj hw⟩))
    · obtain ⟨j, hj, i, hi, hx, hw⟩ := hbv
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨j, hj⟩, ⟨i, hi⟩, inj hx, inj hw⟩)))
    · obtain ⟨i, hi, hx, hw⟩ := hvt
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨i, hi⟩, inj hx, inj hw⟩))))
    · obtain ⟨i, hi, hx, hw⟩ := hvf
      have hir : i < Construction.R φ := by unfold Construction.R; omega
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨i, hi⟩, hir, inj hx, inj hw⟩)))))
    · obtain ⟨j, i, hi, hx, hw⟩ := hbf
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, i, hi, inj hx, inj hw⟩))))))
    · obtain ⟨i, hi, hx, hw⟩ := hsy
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨i, hi⟩, inj hx, inj hw⟩)))))))
    · obtain ⟨i, hi, hx, hw⟩ := hyz
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨i, hi⟩, inj hx, inj hw⟩)))))))
  · rintro (hst | hsa | hab | hbv | hvt | hvf | hbf | hsy | hyz)
    · exact Or.inl ⟨congrArg label hst.1, congrArg label hst.2⟩
    · obtain ⟨j, hx, hw⟩ := hsa
      exact Or.inr (Or.inl ⟨j.val, j.isLt, congrArg label hx, congrArg label hw⟩)
    · obtain ⟨j, hx, hw⟩ := hab
      exact Or.inr (Or.inr (Or.inl ⟨j.val, j.isLt, congrArg label hx, congrArg label hw⟩))
    · obtain ⟨j, i, hx, hw⟩ := hbv
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j.val, j.isLt, i.val, i.isLt, congrArg label hx, congrArg label hw⟩)))
    · obtain ⟨i, hx, hw⟩ := hvt
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i.val, i.isLt, congrArg label hx, congrArg label hw⟩))))
    · obtain ⟨i, _, hx, hw⟩ := hvf
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i.val, i.isLt, congrArg label hx, congrArg label hw⟩)))))
    · obtain ⟨j, i, hi, hx, hw⟩ := hbf
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, i, hi, congrArg label hx, congrArg label hw⟩))))))
    · obtain ⟨i, hx, hw⟩ := hsy
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i.val, i.isLt, congrArg label hx, congrArg label hw⟩)))))))
    · obtain ⟨i, hx, hw⟩ := hyz
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i.val, i.isLt, congrArg label hx, congrArg label hw⟩)))))))

theorem label_adj {φ : Formula} (x w : Vertex φ) :
    (Construction.graph φ).Adj (label x) (label w) ↔ (vertexGraph φ).Adj x w := by
  simp only [Construction.graph, vertexGraph, SimpleGraph.fromRel_adj, ne_eq, label_inj, label_edge]

theorem board_eq_image (φ : Formula) :
    Construction.board φ = Finset.univ.image (@label φ) := by
  ext x
  constructor
  · intro hx
    simp only [Construction.board, Finset.mem_range, Construction.size] at hx
    apply Finset.mem_image.mpr
    by_cases hs : x = 0
    · exact ⟨.s, Finset.mem_univ _, hs.symm⟩
    by_cases ht : x = 1
    · exact ⟨.t, Finset.mem_univ _, ht.symm⟩
    by_cases ha : x < 2 + φ.clauses.length
    · refine ⟨.a ⟨x - 2, by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp [label, Construction.a]; omega
    by_cases hb : x < 2 + 2 * φ.clauses.length
    · refine ⟨.b ⟨x - (2 + φ.clauses.length), by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp [label, Construction.b]; omega
    by_cases hv : x < 2 + 2 * φ.clauses.length + Construction.R φ
    · refine ⟨.v ⟨x - (2 + 2 * φ.clauses.length), by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp [label, Construction.v]; omega
    by_cases hvt : x < 2 + 2 * φ.clauses.length + 2 * Construction.R φ
    · refine ⟨.vt ⟨x - (2 + 2 * φ.clauses.length + Construction.R φ), by omega⟩,
        Finset.mem_univ _, ?_⟩
      dsimp [label, Construction.vt]; omega
    by_cases hf : x < 2 + 2 * φ.clauses.length + 2 * Construction.R φ + φ.nvars
    · refine ⟨.f ⟨x - (2 + 2 * φ.clauses.length + 2 * Construction.R φ), by omega⟩,
        Finset.mem_univ _, ?_⟩
      dsimp [label, Construction.f]; omega
    by_cases hy : x < 2 + 2 * φ.clauses.length + 2 * Construction.R φ + φ.nvars + Construction.K φ
    · refine ⟨.y ⟨x - (2 + 2 * φ.clauses.length + 2 * Construction.R φ + φ.nvars), by omega⟩,
        Finset.mem_univ _, ?_⟩
      dsimp [label, Construction.y]; omega
    · refine ⟨.z ⟨x - (2 + 2 * φ.clauses.length + 2 * Construction.R φ + φ.nvars + Construction.K φ),
        by omega⟩, Finset.mem_univ _, ?_⟩
      dsimp [label, Construction.z]; omega
  · rintro hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact label_mem_board v

end Lax689614Proofs
