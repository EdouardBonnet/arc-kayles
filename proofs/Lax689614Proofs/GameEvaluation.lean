import Lax689614Proofs.GraphParser
import Lax689614Proofs.WordReduction

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs

open Lax689614 ArcKayles

def edgeList (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u, v)

theorem mem_edgeList {n : ℕ} (e : Fin n × Fin n) : e ∈ edgeList n := by
  simp [edgeList]

theorem edgeList_length (n : ℕ) : (edgeList n).length = n * n := by
  simp [edgeList, List.length_flatMap]

def legalEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (e : Fin n × Fin n) : Bool :=
  decide (e.1 ∈ S ∧ e.2 ∈ S ∧ G.Adj e.1 e.2)

def winEval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) : ℕ → Bool
  | 0 => false
  | fuel + 1 => (edgeList n).any fun e => legalEdge G S e && !winEval G (remove S e.1 e.2) fuel

theorem remove_card_lt {V : Type} [DecidableEq V] (S : Finset V) (u v : V) (hu : u ∈ S) :
    (remove S u v).card < S.card :=
  lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hu)

theorem winEval_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (fuel : ℕ) (hf : S.card ≤ fuel) :
    winEval G S fuel = true ↔ Winning G S := by
  induction fuel generalizing S with
  | zero =>
    have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst S
    simp [winEval, winning_empty]
  | succ fuel ih =>
    rw [winEval, List.any_eq_true, winning_iff_move]
    constructor
    · rintro ⟨⟨u, v⟩, _, he⟩
      simp only [Bool.and_eq_true, legalEdge, decide_eq_true_eq, Bool.not_eq_true'] at he
      obtain ⟨⟨hu, hv, hadj⟩, hchild⟩ := he
      refine ⟨u, hu, v, hv, hadj, ?_⟩
      intro hw
      have hh := (ih (remove S u v) (by have := remove_card_lt S u v hu; omega)).mpr hw
      simp [hchild] at hh
    · rintro ⟨u, hu, v, hv, hadj, hchild⟩
      refine ⟨(u, v), mem_edgeList _, ?_⟩
      have hh : winEval G (remove S u v) fuel ≠ true := by
        intro hw
        exact hchild ((ih _ (by have := remove_card_lt S u v hu; omega)).mp hw)
      simp [legalEdge, hu, hv, hadj, Bool.eq_false_iff.mpr hh]

noncomputable def decideArcKayles (w : List Bool) : Bool := by
  classical
  exact match parseGraph w with
    | none => false
    | some G => winEval G.graph Finset.univ G.vertices

theorem decideArcKayles_correct (w : List Bool) : decideArcKayles w = true ↔ w ∈ Encoding.arcKayles := by
  classical
  rw [parseGraph_mem]
  cases hp : parseGraph w with
  | none => simp [decideArcKayles, hp]
  | some G =>
    simp only [decideArcKayles, hp, Option.some.injEq]
    constructor
    · intro h
      exact ⟨G, rfl, (winEval_correct G.graph Finset.univ G.vertices (by simp)).mp h⟩
    · rintro ⟨_, rfl, h⟩
      exact (winEval_correct G.graph Finset.univ G.vertices (by simp)).mpr h

end Lax689614Proofs
