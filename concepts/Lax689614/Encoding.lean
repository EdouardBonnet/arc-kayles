import Lax689614.ArcKayles
import Lax689614.PositiveCNF
import Lax434930.PolynomialTime

/-!
---
title: Binary encodings of graphs and positive CNF formulas
type: definition
---
A graph on $n$ labeled vertices is encoded by $1^n0$ followed by its
$n\times n$ adjacency matrix in row order. A formula on $n$ variables
with $m$ clauses is encoded by $1^n0\,1^m0$ followed by the $m\times n$
clause-variable incidence matrix in row order. These encodings retain
isolated vertices, unused variables, empty clauses, and repeated clauses.
Malformed strings are excluded from the associated languages.
-/

namespace Lax689614.Encoding

open Lax434930.PolynomialTime

structure Graph where
  vertices : ℕ
  graph : SimpleGraph (Fin vertices)

noncomputable def graphWord (G : Graph) : Word := by
  classical
  exact List.replicate G.vertices true ++ [false] ++
    (List.finRange G.vertices).flatMap fun u =>
      (List.finRange G.vertices).map fun v => decide (G.graph.Adj u v)

def formulaWord (φ : PositiveCNF.Formula) : Word :=
  List.replicate φ.nvars true ++ [false] ++
    List.replicate φ.clauses.length true ++ [false] ++
    φ.clauses.flatMap fun C =>
      (List.finRange φ.nvars).map fun x => decide (x ∈ C)

def arcKayles : Language :=
  {w | ∃ G : Graph, graphWord G = w ∧ ArcKayles.Winning G.graph Finset.univ}

def positiveCNF : Language :=
  {w | ∃ φ : PositiveCNF.Formula, formulaWord φ = w ∧ PositiveCNF.FirstWins φ}

end Lax689614.Encoding
