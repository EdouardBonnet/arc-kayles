import Lax689614Proofs.Deviations
import Lax689614Proofs.Passes

/-!
Transport the public regular-play statements to the finite vertex encoding
used in the strategy simulations. These bridges deliberately use statement
axioms, so the archive records Claims 7 and 8 as proof-network dependencies.
-/

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles

theorem vertex_reachable_image {φ : Formula} (S : Finset (Vertex φ))
    (hS : VertexReachable φ S) : RegularPlay.Reachable φ (S.image label) := by
  induction hS with
  | initial => rw [← board_eq_image]; exact .initial
  | @step S u w hS hu hw he hr ih =>
    rw [remove_image label (label_injective φ)]
    exact .step ih (Finset.mem_image_of_mem label hu) (Finset.mem_image_of_mem label hw)
      ((label_adj u w).mpr he) ((label_regular u w).mpr hr)

theorem regular_deviation_wins {φ : Formula} (S : Finset (Vertex φ))
    (hS : VertexReachable φ S) (hm : φ.clauses.length % 2 = 1)
    (hr : φ.clauses.length ≤ (liveV S).card) (hk : 0 < (liveY S).card)
    (u w : Vertex φ) (hu : u ∈ S) (hw : w ∈ S)
    (he : (vertexGraph φ).Adj u w) (hn : ¬ vertexRegular u w)
    (hx : ¬ vertexExceptional S u w) : Winning (vertexGraph φ) (remove S u w) := by
  have h := RegularPlay.deviation_loses φ hm (S.image label) (vertex_reachable_image S hS)
    (by simpa only [remainingV_image] using hr)
    (by rw [remainingY_image]; omega) (label u) (label w)
    (Finset.mem_image_of_mem label hu) (Finset.mem_image_of_mem label hw)
    ((label_adj u w).mpr he) (fun h => hn ((label_regular u w).mp h))
    (by
      rintro ⟨j, hj, hex⟩
      apply hx
      refine ⟨j, (label_same_edge u w .s (.a j)).mp hj, ?_⟩
      intro i hi himem
      exact hex i hi (Finset.mem_image_of_mem label himem))
  rwa [← remove_image label (label_injective φ),
    winning_image (vertexGraph φ) (Construction.graph φ) label (label_injective φ) label_adj] at h

theorem regular_exceptional_losing {φ : Formula} (S : Finset (Vertex φ))
    (hS : VertexReachable φ S) (hm : φ.clauses.length % 2 = 1)
    (hr : φ.clauses.length ≤ (liveV S).card) (j : Fin φ.clauses.length)
    (hj : ∀ i ∈ φ.clauses[j], Vertex.f i ∉ S) :
    ¬ Winning (vertexGraph φ) (remove S .s (.a j)) ↔
      ((liveV S).card + (liveY S).card) % 2 = 0 := by
  have h := RegularPlay.exceptional_parity φ hm (S.image label) (vertex_reachable_image S hS)
    (by simpa only [remainingV_image] using hr) j
    (by intro i hi himem; exact hj i hi ((mem_label_image S (.f i)).mp himem))
  have hrem := remove_image label (label_injective φ) S Vertex.s (Vertex.a j)
  change (remove S Vertex.s (Vertex.a j)).image label =
    remove (S.image label) Construction.s (Construction.a φ j) at hrem
  rwa [← hrem, winning_image (vertexGraph φ) (Construction.graph φ) label
    (label_injective φ) label_adj, remainingV_image, remainingY_image] at h

/-- Passing once transfers a winning second-player position to the first
player; the public pass-equivalence statement removes the extra move. -/
theorem cnf_turn_from_pass (φ : Formula) (U T : Finset (Fin φ.nvars))
    (hd : Disjoint U T) (hw : TrueWins φ U T false) : TrueWins φ U T true := by
  by_cases he : U = ∅
  · subst U
    exact (cnf_empty φ T true).mpr ((cnf_empty φ T false).mp hw)
  · apply (Passes.outcome_equivalent φ U T hd true 1).mp
    apply (passes_true φ U T 1 he).mpr
    exact Or.inr ⟨by decide, (Passes.outcome_equivalent φ U T hd false 0).mpr hw⟩

end Lax689614Proofs
