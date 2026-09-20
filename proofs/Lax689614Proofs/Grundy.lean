import Lax689614.GrundyProperties
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace Lax689614Proofs

open Lax689614 ArcKayles Grundy

theorem mex_not_mem (S : Finset ℕ) : mex S ∉ S :=
  Nat.sInf_mem S.exists_notMem

theorem mem_of_lt_mex (S : Finset ℕ) {i : ℕ} (h : i < mex S) : i ∈ S := by
  by_contra hn
  exact (not_le_of_gt h) (Nat.sInf_le hn)

theorem mex_eq (S : Finset ℕ) (n : ℕ) (hn : n ∉ S)
    (hi : ∀ i < n, i ∈ S) : mex S = n := by
  apply Nat.le_antisymm (Nat.sInf_le hn)
  by_contra h
  exact mex_not_mem S (hi _ (Nat.lt_of_not_ge h))

theorem move_mem {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v : V) :
    (u, v) ∈ moves G S ↔ u ∈ S ∧ v ∈ S ∧ G.Adj u v := by
  classical
  simp [moves, and_assoc]

noncomputable def optionValues {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset ℕ :=
  (moves G S).attach.image fun e => value G (remove S e.val.1 e.val.2)

theorem value_eq_mex {V : Type} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    value G S = mex (optionValues G S) := by
  rw [value]
  rfl

theorem option_mem {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (i : ℕ) :
    i ∈ optionValues G S ↔
      ∃ u ∈ S, ∃ v ∈ S, G.Adj u v ∧ value G (remove S u v) = i := by
  classical
  simp only [optionValues, Finset.mem_image, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨⟨⟨u, v⟩, he⟩, hv⟩
    obtain ⟨hu, hw, ha⟩ := (move_mem G S u v).mp he
    exact ⟨u, hu, v, hw, ha, hv⟩
  · rintro ⟨u, hu, v, hv, he, hi⟩
    exact ⟨⟨(u, v), (move_mem G S u v).mpr ⟨hu, hv, he⟩⟩, hi⟩

/--
---
conclusion: Lax689614.GrundyProperties.smaller_reachable
---
Every natural number below a minimum excluded value belongs to the option set.
-/
theorem smaller_reachable {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (i : ℕ) (h : i < value G S) :
    ∃ u ∈ S, ∃ v ∈ S, G.Adj u v ∧ value G (remove S u v) = i := by
  apply (option_mem G S i).mp
  apply mem_of_lt_mex
  rwa [← value_eq_mex]

/--
---
conclusion: Lax689614.GrundyProperties.value_not_reachable
---
A minimum excluded value does not belong to the option set.
-/
theorem value_not_reachable {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v : V) (hu : u ∈ S) (hv : v ∈ S) (he : G.Adj u v) :
    value G (remove S u v) ≠ value G S := by
  intro h
  have hm := (option_mem G S _).mpr ⟨u, hu, v, hv, he, h⟩
  rw [value_eq_mex G S] at hm
  exact mex_not_mem _ hm

theorem winning_iff_move {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) : Winning G S ↔
      ∃ u ∈ S, ∃ v ∈ S, G.Adj u v ∧ ¬ Winning G (remove S u v) := by
  rw [Winning]
  constructor
  · rintro ⟨⟨⟨u, v⟩, he⟩, hn⟩
    obtain ⟨hu, hv, ha⟩ := (move_mem G S u v).mp he
    exact ⟨u, hu, v, hv, ha, hn⟩
  · rintro ⟨u, hu, v, hv, he, hn⟩
    exact ⟨⟨(u, v), (move_mem G S u v).mpr ⟨hu, hv, he⟩⟩, hn⟩

/--
---
conclusion: Lax689614.GrundyProperties.losing_iff_zero
---
Backward induction: a winning move leads to value zero, and every
positive value has such a move.
-/
theorem losing_iff_zero {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) : ¬ Winning G S ↔ value G S = 0 := by
  classical
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    have child (u v : V) (hu : u ∈ S) :
        ¬ Winning G (remove S u v) ↔ value G (remove S u v) = 0 := by
      apply ih (remove S u v).card
      · rw [← hn]
        exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hu)
      · rfl
    constructor
    · intro hnot
      by_contra hne
      obtain ⟨u, hu, v, hv, he, hz⟩ := smaller_reachable G S 0 (Nat.pos_of_ne_zero hne)
      exact hnot ((winning_iff_move G S).mpr ⟨u, hu, v, hv, he, (child u v hu).mpr hz⟩)
    · intro hz hw
      obtain ⟨u, hu, v, hv, he, hl⟩ := (winning_iff_move G S).mp hw
      exact value_not_reachable G S u v hu hv he ((child u v hu).mp hl |>.trans hz.symm)

end Lax689614Proofs
