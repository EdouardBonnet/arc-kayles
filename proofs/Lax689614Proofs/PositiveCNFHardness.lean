import Lax689614Proofs.SpaceReductionCode
import Lax689614Proofs.ReductionComposition
import Lax689614.PositiveCNFHardness

namespace Lax689614Proofs

open Lax434930.PolynomialTime Lax434930.PolynomialSpace Lax429075.Reductions

theorem signedCNF_hard : Lax689614.PSPACE.Hard Byskov.signedLanguage := by
  intro A hA
  obtain ⟨p, M, _hd, hdec, hspace⟩ := hA
  refine ⟨fun w => (CircuitStreaming.sourceCode M p).eval (fun _ => w),
    MachineCode.code_polynomial_time (CircuitStreaming.sourceCode M p), ?_⟩
  intro w
  exact (hdec w).2.symm.trans (CircuitStreaming.sourceCode_correct M p w (hspace w)).symm

/--
---
conclusion: Lax689614.PositiveCNFHardness.hard
---
Compile polynomial-space machine reachability into a quantified circuit,
then use the verified Cook–Levin gate clauses and quantifier normalization.
The checked Byskov game gadgets transfer the resulting alternating-CNF
game to positive CNF. Both word transformations have compiled polynomial-
time Turing-machine witnesses; their composition uses the archived
polynomial-time composition proof.
-/
theorem positiveCNF_hard : Lax689614.PSPACE.Hard Lax689614.Encoding.positiveCNF :=
  pspace_hard_of_reduction signedCNF_hard Byskov.signedReduction_polynomial

end Lax689614Proofs
