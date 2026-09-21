import Lax689614Proofs.Grundy

namespace Lax689614Proofs

open Lax689614 ArcKayles Grundy

theorem remove_image {V W : Type} [DecidableEq V] [DecidableEq W]
    (f : V → W) (hf : Function.Injective f) (S : Finset V) (u v : V) :
    (remove S u v).image f = remove (S.image f) (f u) (f v) := by
  simp only [remove, Finset.image_erase hf]

theorem value_image {V W : Type} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W) (hf : Function.Injective f)
    (he : ∀ u v, H.Adj (f u) (f v) ↔ G.Adj u v) (S : Finset V) :
    value H (S.image f) = value G S := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    have child (u v : V) (hu : u ∈ S) :
        value H (remove (S.image f) (f u) (f v)) = value G (remove S u v) := by
      rw [← remove_image f hf]
      apply ih (remove S u v).card
      · rw [← hn]
        exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hu)
      · rfl
    rw [value_eq_mex, value_eq_mex]
    congr 1
    ext i
    rw [option_mem, option_mem]
    constructor
    · rintro ⟨u, hu, v, hv, huv, hi⟩
      obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
      exact ⟨u', hu', v', hv', (he u' v').mp huv, (child u' v' hu').symm.trans hi⟩
    · rintro ⟨u, hu, v, hv, huv, hi⟩
      exact ⟨f u, Finset.mem_image_of_mem f hu, f v, Finset.mem_image_of_mem f hv,
        (he u v).mpr huv, (child u v hu).trans hi⟩

theorem winning_image {V W : Type} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W) (hf : Function.Injective f)
    (he : ∀ u v, H.Adj (f u) (f v) ↔ G.Adj u v) (S : Finset V) :
    Winning H (S.image f) ↔ Winning G S := by
  classical
  have h := value_image G H f hf he S
  have hnot : ¬ Winning H (S.image f) ↔ ¬ Winning G S := by
    rw [GrundyProperties.losing_iff_zero, GrundyProperties.losing_iff_zero, h]
  exact not_iff_not.mp hnot

end Lax689614Proofs
