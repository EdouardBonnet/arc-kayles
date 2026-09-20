import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

/-!
---
title: Arc Kayles
type: definition
---
A position consists of a finite set of surviving vertices of a simple graph.
A move removes the two endpoints of a surviving edge. Under normal play,
the player with no legal move loses. A position is winning for the player
to move if some legal move leaves a position losing for the opponent.
Isolated vertices may be retained: they permit no moves.
-/

namespace Lax689614.ArcKayles

variable {V : Type} [DecidableEq V]

/-- The position after playing an edge with endpoints `u` and `v`. -/
def remove (S : Finset V) (u v : V) : Finset V := (S.erase u).erase v

/-- Legal moves, represented by ordered pairs of endpoints. -/
noncomputable def moves (G : SimpleGraph V) (S : Finset V) : Finset (V × V) := by
  classical
  exact (S ×ˢ S).filter fun e => G.Adj e.1 e.2

/-- Winning for the next player, by backward induction on surviving vertices. -/
def Winning (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ e : {e // e ∈ moves G S}, ¬ Winning G (remove S e.val.1 e.val.2)
termination_by S.card
decreasing_by
  have h := e.property
  simp only [moves, Finset.mem_filter, Finset.mem_product] at h
  exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem h.1.1)

end Lax689614.ArcKayles
