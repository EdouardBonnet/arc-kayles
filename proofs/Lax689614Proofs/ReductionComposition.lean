import Lax434930Proofs.PolynomialComposition
import Lax689614.PSPACE

namespace Lax689614Proofs

open Lax434930.PolynomialTime Lax434930.PolynomialSpace Lax429075.Reductions

theorem manyOne_trans {A B C : Language} (hab : ManyOne A B) (hbc : ManyOne B C) :
    ManyOne A C := by
  obtain ⟨f, ⟨hf⟩, hfc⟩ := hab
  obtain ⟨g, ⟨hg⟩, hgc⟩ := hbc
  refine ⟨g ∘ f, Lax434930Proofs.PolynomialComposition.comp hf hg, ?_⟩
  intro w
  exact (hfc w).trans (hgc (f w))

theorem pspace_hard_of_reduction {A B : Language} (hA : Lax689614.PSPACE.Hard A)
    (hAB : ManyOne A B) : Lax689614.PSPACE.Hard B := by
  intro C hC
  exact manyOne_trans (hA C hC) hAB

theorem pspace_complete_of_reduction {A B : Language} (hA : Lax689614.PSPACE.Hard A)
    (hAB : ManyOne A B) (hB : B ∈ PSPACE) : Lax689614.PSPACE.Complete B :=
  ⟨hB, pspace_hard_of_reduction hA hAB⟩

end Lax689614Proofs
