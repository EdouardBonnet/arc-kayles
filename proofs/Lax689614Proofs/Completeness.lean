import Lax689614Proofs.PositiveCNFHardness
import Lax689614Proofs.ReductionTime
import Lax689614Proofs.Membership

namespace Lax689614Proofs

/--
---
conclusion: Lax689614.Completeness.pspace_complete
---
The compiled depth-first evaluator gives PSPACE membership. Compose
positive-CNF PSPACE-hardness with the checked polynomial-time graph
reduction to obtain PSPACE-hardness of Arc Kayles.
-/
theorem arcKayles_pspace_complete : Lax689614.PSPACE.Complete Lax689614.Encoding.arcKayles :=
  pspace_complete_of_reduction Lax689614.PositiveCNFHardness.hard
    Lax689614.Reduction.polynomial_reduction Lax689614.Completeness.membership

end Lax689614Proofs
