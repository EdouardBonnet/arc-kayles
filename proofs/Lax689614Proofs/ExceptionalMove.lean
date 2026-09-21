import Lax689614Proofs.ResidualValues
import Mathlib.Data.Fintype.Fin

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles Grundy Biclique
open scoped Classical

theorem remainingV_image {φ : Formula} (A : Finset (Vertex φ)) :
    RegularPlay.remainingV φ (A.image label) = (liveV A).card := by
  unfold RegularPlay.remainingV
  rw [← Finset.image_fin_univ, Finset.filter_image,
    Finset.card_image_of_injective _ Fin.val_injective]
  change (Finset.univ.filter fun i : Fin (Construction.R φ) =>
    label (.v i) ∈ A.image label).card = (liveV A).card
  simp only [liveV, Finset.mem_image, label_inj, exists_eq_right]

theorem remainingY_image {φ : Formula} (A : Finset (Vertex φ)) :
    RegularPlay.remainingY φ (A.image label) = (liveY A).card := by
  unfold RegularPlay.remainingY
  rw [← Finset.image_fin_univ, Finset.filter_image,
    Finset.card_image_of_injective _ Fin.val_injective]
  change (Finset.univ.filter fun i : Fin (Construction.K φ) =>
    label (.y i) ∈ A.image label).card = (liveY A).card
  simp only [liveY, Finset.mem_image, label_inj, exists_eq_right]

theorem parity_xor (r k : ℕ) : Nat.xor (r % 2) (k % 2) = (r + k) % 2 := by
  rw [Nat.add_mod]
  have hr : r % 2 = 0 ∨ r % 2 = 1 := by omega
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hr with hr | hr <;> rcases hk with hk | hk <;> rw [hr, hk] <;> decide

theorem exceptional_value {φ : Formula} (A : Finset (Vertex φ)) (hA : RegularInvariant A)
    (j : Fin φ.clauses.length) (hj : ∀ i ∈ φ.clauses[j], Vertex.f i ∉ A)
    (hm : φ.clauses.length % 2 = 1) (hr : φ.clauses.length ≤ (liveV A).card) :
    value (vertexGraph φ) (remove A .s (.a j)) = ((liveV A).card + (liveY A).card) % 2 := by
  let D := remove A Vertex.s (Vertex.a j)
  let Q : Finset (Fin φ.clauses.length) := Finset.univ.erase j
  have hs : Vertex.s ∉ D := by simp [D, remove]
  have hQ : ∀ q ∈ Q, Vertex.b q ∈ D ∧ Vertex.a q ∈ D := by
    intro q hq
    have hqj : q ≠ j := (Finset.mem_erase.mp hq).1
    simp [D, remove, hA.b_mem q, hA.a_mem q, hqj]
  have hv : ∀ i, Vertex.v i ∈ D → Vertex.vt i ∈ D := by
    intro i hi
    have hiA := remove_subset A Vertex.s (Vertex.a j) hi
    simp [D, remove, hA.vt_mem i hiA]
  have ho : ∀ q, Vertex.b q ∈ D → q ∉ Q →
      Vertex.a q ∉ D ∧ ∀ i ∈ φ.clauses[q], Vertex.f i ∉ D := by
    intro q _ hq
    have hqj : q = j := by simpa [Q] using hq
    subst q
    constructor
    · simp [D, remove]
    · intro i hi hmem
      exact hj i hi (remove_subset A Vertex.s (Vertex.a j) hmem)
  have hp : ∀ i, Vertex.y i ∈ D ↔ Vertex.z i ∈ D := by
    intro i
    simpa [D, remove] using hA.yz_mem i
  have hvset : liveV D = liveV A := by ext i; simp [liveV, D, remove]
  have hyset : liveY D = liveY A := by ext i; simp [liveY, D, remove]
  have hc := core_value D Q hs hQ hv ho
  have ht := tail_value D hp
  have hqc : Q.card = φ.clauses.length - 1 := by simp [Q]
  have hg : g (φ.clauses.length - 1) (liveV A).card = (liveV A).card % 2 := by
    unfold g
    omega
  change value (vertexGraph φ) D = _
  rw [split_value D hs, hc, ht, hqc, hvset, hyset, hg, parity_xor]

/--
---
conclusion: Lax689614.RegularPlay.exceptional_parity
---
After playing the central-clause edge, omit that clause vertex from the
biclique and place it in the independent set. Its literal neighbors are
absent. The biclique formula and the disjoint pass edges give value
`(r + k) mod 2`.
-/
theorem exceptional_parity (φ : Formula) (hm : φ.clauses.length % 2 = 1)
    (S : Finset ℕ) (hS : RegularPlay.Reachable φ S)
    (hr : φ.clauses.length ≤ RegularPlay.remainingV φ S)
    (j : Fin φ.clauses.length) (hj : RegularPlay.Exhausted φ S j) :
    ¬ Winning (Construction.graph φ) (remove S Construction.s (Construction.a φ j)) ↔
      (RegularPlay.remainingV φ S + RegularPlay.remainingY φ S) % 2 = 0 := by
  obtain ⟨A, hA, rfl⟩ := reachable_image S hS
  have hex : ∀ i ∈ φ.clauses[j], Vertex.f i ∉ A := by
    intro i hi hmem
    exact hj i hi (Finset.mem_image_of_mem label hmem)
  rw [remainingV_image] at hr
  rw [remainingV_image, remainingY_image]
  have hrem := remove_image label (label_injective φ) A Vertex.s (Vertex.a j)
  change (remove A Vertex.s (Vertex.a j)).image label =
    remove (A.image label) Construction.s (Construction.a φ j) at hrem
  rw [← hrem, winning_image (vertexGraph φ) (Construction.graph φ) label
    (label_injective φ) label_adj, GrundyProperties.losing_iff_zero,
    exceptional_value A (regular_invariant A hA) j hex hm hr]

end Lax689614Proofs
