import Lax434930.PolynomialSpace
import Lax429075.Reductions

/-!
---
title: PSPACE-completeness
type: definition
---
A binary language is PSPACE-hard if every language decidable in polynomial
space has a polynomial-time many-one reduction to it. It is PSPACE-complete
if it is also decidable in polynomial space. Polynomial space and reductions
are those of the classical complexity and Cook–Levin submissions.
-/

namespace Lax689614.PSPACE

open Lax434930.PolynomialTime Lax434930.PolynomialSpace Lax429075.Reductions

def Hard (B : Language) : Prop := ∀ A : Language, A ∈ PSPACE → ManyOne A B

def Complete (B : Language) : Prop := B ∈ PSPACE ∧ Hard B

end Lax689614.PSPACE
