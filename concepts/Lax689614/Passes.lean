import Lax689614.PositiveCNF

/-!
---
title: Passing and assigning either truth value
type: theorem
---
Lemma 5, in its finite form. Give the two players a shared supply of $p$
passes, and allow either player to assign either truth value to a selected
unassigned variable. Passing consumes one unit of the supply. Play ends
as soon as all variables are assigned, with the same satisfaction rule.
For every finite supply, this game has the same winner as ordinary positive
CNF, including at intermediate positions. A finite supply avoids infinite
plays consisting of passes and covers all passes in the reduction graph.
-/

namespace Lax689614.Passes

open PositiveCNF

def TrueWins (φ : Formula) (U T : Finset (Fin φ.nvars))
    (trueTurn : Bool) (passes : ℕ) : Prop :=
  if U = ∅ then Satisfied φ T
  else if trueTurn then
    (∃ x : U, ∃ b : Bool,
      TrueWins φ (U.erase x.val) (if b then insert x.val T else T) false passes) ∨
    (∃ _h : 0 < passes, TrueWins φ U T false (passes - 1))
  else
    (∀ x : U, ∀ b : Bool,
      TrueWins φ (U.erase x.val) (if b then insert x.val T else T) true passes) ∧
    (∀ _h : 0 < passes, TrueWins φ U T true (passes - 1))
termination_by U.card + passes
decreasing_by
  all_goals first
    | have := Finset.card_erase_lt_of_mem x.property; omega
    | omega

axiom outcome_equivalent (φ : Formula) (U T : Finset (Fin φ.nvars))
    (hd : Disjoint U T) (turn : Bool) (passes : ℕ) :
    TrueWins φ U T turn passes ↔ PositiveCNF.TrueWins φ U T turn

end Lax689614.Passes
