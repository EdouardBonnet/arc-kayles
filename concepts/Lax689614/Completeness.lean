import Lax689614.Reduction
import Lax689614.PositiveCNFHardness

/-!
---
title: Arc Kayles is PSPACE-complete
type: theorem
---
Theorem 1. Determining the winner of Arc Kayles on a finite simple
undirected graph is PSPACE-complete under polynomial-time many-one
reductions. Membership follows by depth-first evaluation of the game tree:
at most $n/2$ moves are played and each position uses $O(n^2)$ bits.
Hardness follows from the positive CNF game and the reduction graph.
-/

namespace Lax689614.Completeness

axiom membership : Encoding.arcKayles ∈ Lax434930.PolynomialSpace.PSPACE

axiom pspace_complete : PSPACE.Complete Encoding.arcKayles

end Lax689614.Completeness
