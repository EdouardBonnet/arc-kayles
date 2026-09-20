import Lax689614.Biclique
import Lax689614Proofs.Grundy

namespace Lax689614Proofs

open Lax689614 ArcKayles Grundy Biclique

def countOptions (a b : ℕ) : Finset ℕ :=
  (if 0 < a then {g (a - 1) b} else ∅) ∪
  (if 0 < b then {g a (b - 1)} else ∅) ∪
  (if 0 < a ∧ 0 < b then {g (a - 1) (b - 1)} else ∅)

theorem countOptions_mem (a b i : ℕ) : i ∈ countOptions a b ↔
    (0 < a ∧ g (a - 1) b = i) ∨ (0 < b ∧ g a (b - 1) = i) ∨
    (0 < a ∧ 0 < b ∧ g (a - 1) (b - 1) = i) := by
  simp only [countOptions, Finset.mem_union]
  split_ifs <;> simp_all <;> aesop

theorem biclique_recurrence (a b : ℕ) : mex (countOptions a b) = g a b := by
  apply mex_eq
  · rw [countOptions_mem]
    simp only [g]
    omega
  · intro i hi
    rw [countOptions_mem]
    simp only [g] at *
    omega

theorem remove_subset {V : Type} [DecidableEq V] (S : Finset V) (u v : V) :
    remove S u v ⊆ S :=
  Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _)

theorem remove_mem {V : Type} [DecidableEq V] (S : Finset V) (u v w : V) :
    w ∈ remove S u v ↔ w ≠ v ∧ w ≠ u ∧ w ∈ S := by
  simp [remove]

theorem partition_after_move {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S L R I : Finset V) (h : Partition G S L R I)
    (u v : V) (hu : u ∈ S) (hv : v ∈ S) (he : G.Adj u v) :
    Partition G (remove S u v) (remove L u v) (remove R u v) (remove I u v) := by
  classical
  constructor
  · ext w
    simp only [remove_mem, Finset.mem_union, h.cover]
    aesop
  · exact h.left_right.mono (remove_subset L u v) (remove_subset R u v)
  · exact h.left_independent.mono (remove_subset L u v) (remove_subset I u v)
  · exact h.right_independent.mono (remove_subset R u v) (remove_subset I u v)
  · intro x hx y hy
    exact h.left_stable x (remove_subset L u v hx) y (remove_subset L u v hy)
  · intro x hx y hy
    exact h.right_stable x (remove_subset R u v hx) y (remove_subset R u v hy)
  · intro x hx y hy
    exact h.independent_stable x (remove_subset I u v hx) y (remove_subset I u v hy)
  · intro x hx y hy
    exact h.complete x (remove_subset L u v hx) y (remove_subset R u v hy)
  · intro w hw
    have hw' : (w ≠ v ∧ w ≠ u ∧ w ∈ L) ∨ (w ≠ v ∧ w ≠ u ∧ w ∈ R) := by
      simpa only [Finset.mem_union, remove_mem] using hw
    have hne : w ≠ v ∧ w ≠ u := by
      exact hw'.elim
        (fun hx => ⟨hx.1, hx.2.1⟩) (fun hx => ⟨hx.1, hx.2.1⟩)
    have hwold : w ∈ L ∪ R := by
      apply Finset.mem_union.mpr
      exact hw'.elim
        (fun hx => Or.inl hx.2.2) (fun hx => Or.inr hx.2.2)
    obtain ⟨p, hp, hwp, hprivate⟩ := h.pendant w hwold
    have hpu : p ≠ u := by
      intro hh
      subst p
      exact hne.1 (hprivate v hv he).symm
    have hpv : p ≠ v := by
      intro hh
      subst p
      exact hne.2 (hprivate u hu he.symm).symm
    refine ⟨p, (remove_mem I u v p).mpr ⟨hpv, hpu, hp⟩, hwp, ?_⟩
    intro x hx hpx
    exact hprivate x (remove_subset S u v hx) hpx

theorem count_after_move {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S L R I : Finset V) (h : Partition G S L R I)
    (u v : V) (hu : u ∈ S) (hv : v ∈ S) (he : G.Adj u v) :
    g (remove L u v).card (remove R u v).card ∈ countOptions L.card R.card := by
  have hLR := Finset.disjoint_left.mp h.left_right
  have hLI := Finset.disjoint_left.mp h.left_independent
  have hRI := Finset.disjoint_left.mp h.right_independent
  have huv : u ≠ v := G.ne_of_adj he
  have hvu : v ≠ u := huv.symm
  rw [h.cover, Finset.mem_union, Finset.mem_union] at hu hv
  rw [countOptions_mem]
  rcases hu with (huL | huR) | huI <;> rcases hv with (hvL | hvR) | hvI
  · exact False.elim (h.left_stable u huL v hvL he)
  · have huR : u ∉ R := hLR huL
    have hvL : v ∉ L := fun hh => hLR hh hvR
    right; right
    refine ⟨Finset.card_pos.mpr ⟨u, huL⟩, Finset.card_pos.mpr ⟨v, hvR⟩, ?_⟩
    simp [remove, Finset.card_erase_eq_ite, huL, huR, hvL, hvR, huv, hvu]
  · have huR : u ∉ R := hLR huL
    have hvL : v ∉ L := fun hh => hLI hh hvI
    have hvR : v ∉ R := fun hh => hRI hh hvI
    left
    refine ⟨Finset.card_pos.mpr ⟨u, huL⟩, ?_⟩
    simp [remove, Finset.card_erase_eq_ite, huL, huR, hvL, hvR, huv, hvu]
  · have huL : u ∉ L := fun hh => hLR hh huR
    have hvR : v ∉ R := hLR hvL
    right; right
    refine ⟨Finset.card_pos.mpr ⟨v, hvL⟩, Finset.card_pos.mpr ⟨u, huR⟩, ?_⟩
    simp [remove, Finset.card_erase_eq_ite, huL, huR, hvL, hvR, huv, hvu]
  · exact False.elim (h.right_stable u huR v hvR he)
  · have huL : u ∉ L := fun hh => hLR hh huR
    have hvL : v ∉ L := fun hh => hLI hh hvI
    have hvR : v ∉ R := fun hh => hRI hh hvI
    right; left
    refine ⟨Finset.card_pos.mpr ⟨u, huR⟩, ?_⟩
    simp [remove, Finset.card_erase_eq_ite, huL, huR, hvL, hvR, huv, hvu]
  · have huL : u ∉ L := fun hh => hLI hh huI
    have huR : u ∉ R := fun hh => hRI hh huI
    have hvR : v ∉ R := hLR hvL
    left
    refine ⟨Finset.card_pos.mpr ⟨v, hvL⟩, ?_⟩
    simp [remove, Finset.card_erase_eq_ite, huL, huR, hvL, hvR, huv, hvu]
  · have huL : u ∉ L := fun hh => hLI hh huI
    have huR : u ∉ R := fun hh => hRI hh huI
    have hvL : v ∉ L := fun hh => hLR hh hvR
    right; left
    refine ⟨Finset.card_pos.mpr ⟨v, hvR⟩, ?_⟩
    simp [remove, Finset.card_erase_eq_ite, huL, huR, hvL, hvR, huv, hvu]
  · exact False.elim (h.independent_stable u huI v hvI he)

theorem count_option_realized {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S L R I : Finset V) (h : Partition G S L R I)
    (i : ℕ) (hi : i ∈ countOptions L.card R.card) :
    ∃ u ∈ S, ∃ v ∈ S, G.Adj u v ∧
      g (remove L u v).card (remove R u v).card = i := by
  have hLR := Finset.disjoint_left.mp h.left_right
  have hLI := Finset.disjoint_left.mp h.left_independent
  have hRI := Finset.disjoint_left.mp h.right_independent
  have hLS : L ⊆ S := by rw [h.cover]; exact Finset.subset_union_left.trans Finset.subset_union_left
  have hRS : R ⊆ S := by rw [h.cover]; exact Finset.subset_union_right.trans Finset.subset_union_left
  have hIS : I ⊆ S := by rw [h.cover]; exact Finset.subset_union_right
  rcases (countOptions_mem _ _ _).mp hi with ⟨ha, rfl⟩ | ⟨hb, rfl⟩ | ⟨ha, hb, rfl⟩
  · obtain ⟨u, huL⟩ := Finset.card_pos.mp ha
    obtain ⟨v, hvI, he, _⟩ := h.pendant u (Finset.mem_union_left R huL)
    have huR : u ∉ R := hLR huL
    have hvL : v ∉ L := fun hh => hLI hh hvI
    have hvR : v ∉ R := fun hh => hRI hh hvI
    refine ⟨u, hLS huL, v, hIS hvI, he, ?_⟩
    simp [remove, Finset.card_erase_eq_ite, huL, huR, hvL, hvR]
  · obtain ⟨u, huR⟩ := Finset.card_pos.mp hb
    obtain ⟨v, hvI, he, _⟩ := h.pendant u (Finset.mem_union_right L huR)
    have huL : u ∉ L := fun hh => hLR hh huR
    have hvL : v ∉ L := fun hh => hLI hh hvI
    have hvR : v ∉ R := fun hh => hRI hh hvI
    refine ⟨u, hRS huR, v, hIS hvI, he, ?_⟩
    simp [remove, Finset.card_erase_eq_ite, huL, huR, hvL, hvR]
  · obtain ⟨u, huL⟩ := Finset.card_pos.mp ha
    obtain ⟨v, hvR⟩ := Finset.card_pos.mp hb
    have huR : u ∉ R := hLR huL
    have hvL : v ∉ L := fun hh => hLR hh hvR
    have hvu : v ≠ u := by intro hh; subst v; exact huR hvR
    refine ⟨u, hLS huL, v, hRS hvR, h.complete u huL v hvR, ?_⟩
    simp [remove, Finset.card_erase_eq_ite, huL, huR, hvL, hvR, hvu]

/--
---
conclusion: Lax689614.Biclique.value_eq
---
Deleting an edge preserves the partition and private-neighbor condition.
The reachable pairs of biclique-side sizes are precisely the one-side and
two-side decrements. Their minimum excluded value is the stated formula.
-/
theorem biclique_value {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S L R I : Finset V) (h : Partition G S L R I) :
    value G S = g L.card R.card := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S L R I with
  | h n ih =>
    have child (u v : V) (hu : u ∈ S) (hv : v ∈ S) (he : G.Adj u v) :
        value G (remove S u v) = g (remove L u v).card (remove R u v).card := by
      apply ih (remove S u v).card
      · rw [← hn]
        exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hu)
      · exact partition_after_move G S L R I h u v hu hv he
      · rfl
    rw [value_eq_mex]
    have hopts : optionValues G S = countOptions L.card R.card := by
      ext i
      constructor
      · intro hi
        obtain ⟨u, hu, v, hv, he, hi⟩ := (option_mem G S i).mp hi
        rw [child u v hu hv he] at hi
        rw [← hi]
        exact count_after_move G S L R I h u v hu hv he
      · intro hi
        obtain ⟨u, hu, v, hv, he, hi⟩ := count_option_realized G S L R I h i hi
        apply (option_mem G S i).mpr
        exact ⟨u, hu, v, hv, he, (child u v hu hv he).trans hi⟩
    rw [hopts, biclique_recurrence]

end Lax689614Proofs
