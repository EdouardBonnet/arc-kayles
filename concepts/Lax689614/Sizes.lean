import Lax689614.Construction

/-!
---
title: Sizes of encodings and the reduction graph
type: theorem
---
The graph encoding has $n^2+n+1$ bits. The formula encoding has
$mn+n+m+2$ bits, where $n$ and $m$ are its variable and clause counts.
The reduction graph has exactly $13n+4m+18$ vertices.
These bounds account explicitly for the unary size prefixes and incidence
matrices; they are separate from the running-time proof of the reduction.
-/

namespace Lax689614.Sizes

axiom graph_length (G : Encoding.Graph) :
    (Encoding.graphWord G).length = G.vertices ^ 2 + G.vertices + 1

axiom formula_length (φ : PositiveCNF.Formula) :
    (Encoding.formulaWord φ).length =
      φ.clauses.length * φ.nvars + φ.nvars + φ.clauses.length + 2

axiom construction_size (φ : PositiveCNF.Formula) :
    Construction.size φ = 13 * φ.nvars + 4 * φ.clauses.length + 18

end Lax689614.Sizes
