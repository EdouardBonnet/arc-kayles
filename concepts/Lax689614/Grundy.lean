import Lax689614.ArcKayles
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat

/-!
---
title: Sprague–Grundy values
type: definition
---
The minimum excluded value of a finite set of natural numbers is the least
natural number outside the set. The Sprague–Grundy value of a position is
the minimum excluded value of the values reachable in one move.
In particular, a terminal position has value zero.
-/

namespace Lax689614.Grundy

open ArcKayles

noncomputable def mex (S : Finset ℕ) : ℕ := sInf {n : ℕ | n ∉ S}

noncomputable def value {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  mex ((moves G S).attach.image fun e => value G (remove S e.val.1 e.val.2))
termination_by S.card
decreasing_by
  have h := e.property
  simp only [moves, Finset.mem_filter, Finset.mem_product] at h
  exact lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem h.1.1)

end Lax689614.Grundy
