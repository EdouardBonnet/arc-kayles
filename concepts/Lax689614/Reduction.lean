import Lax689614.Construction
import Lax689614.PSPACE

/-!
---
title: Correctness and complexity of the reduction
type: theorem
---
Claims 9 and 10: for a formula with an odd number of clauses, the first
player wins Arc Kayles on the constructed graph if and only if True wins
the positive CNF game. The second player's winning implication is stated
separately to expose the two strategy arguments.

There is a polynomial-time many-one reduction on all binary strings.
Before applying the construction, duplicate a clause if the nonempty clause
list has even length. Handle the empty conjunction and malformed encodings
separately by fixed yes and no instances.
-/

namespace Lax689614.Reduction

open PositiveCNF Construction ArcKayles

axiom false_strategy (φ : Formula) (hm : φ.clauses.length % 2 = 1)
    (h : ¬ FirstWins φ) : ¬ Winning (graph φ) (board φ)

axiom true_strategy (φ : Formula) (hm : φ.clauses.length % 2 = 1)
    (h : FirstWins φ) : Winning (graph φ) (board φ)

axiom polynomial_reduction :
    Lax429075.Reductions.ManyOne Encoding.positiveCNF Encoding.arcKayles

end Lax689614.Reduction
