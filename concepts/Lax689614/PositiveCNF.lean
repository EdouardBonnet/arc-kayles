import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
---
title: The positive CNF game
type: definition
---
A positive CNF formula is a list of clauses, each a set of variables.
True and False alternately choose an unassigned variable, assigning it
their own truth value. True starts and wins exactly when each clause
contains a variable assigned true. Empty clauses and unused variables are
allowed. At an intermediate position, `U` is the set of unassigned
variables and `T` the set already assigned true.
-/

namespace Lax689614.PositiveCNF

structure Formula where
  nvars : ℕ
  clauses : List (Finset (Fin nvars))

def Satisfied (φ : Formula) (T : Finset (Fin φ.nvars)) : Prop :=
  ∀ C ∈ φ.clauses, ∃ x ∈ C, x ∈ T

/-- Whether True can force satisfaction from the specified position and turn. -/
def TrueWins (φ : Formula) (U T : Finset (Fin φ.nvars)) (trueTurn : Bool) : Prop :=
  if U = ∅ then Satisfied φ T
  else if trueTurn then
    ∃ x : U, TrueWins φ (U.erase x.val) (insert x.val T) false
  else
    ∀ x : U, TrueWins φ (U.erase x.val) T true
termination_by U.card
decreasing_by all_goals exact Finset.card_erase_lt_of_mem x.property

def FirstWins (φ : Formula) : Prop := TrueWins φ Finset.univ ∅ true

end Lax689614.PositiveCNF
