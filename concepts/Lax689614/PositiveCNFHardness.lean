import Lax689614.Encoding
import Lax689614.PSPACE

/-!
---
title: PSPACE-hardness of the positive CNF game
type: theorem
---
Schaefer's theorem: determining whether True wins the positive CNF game
is PSPACE-hard under polynomial-time many-one reductions.

# References
Thomas J. Schaefer, *On the complexity of some two-person
perfect-information games*, JCSS 16(2), 185–225 (1978).
-/

namespace Lax689614.PositiveCNFHardness

axiom hard : PSPACE.Hard Encoding.positiveCNF

end Lax689614.PositiveCNFHardness
