import Lax689614.Sizes
import Mathlib.Tactic

namespace Lax689614Proofs

open Lax689614

/--
---
conclusion: Lax689614.Sizes.graph_length
---
-/
theorem graph_length (G : Encoding.Graph) :
    (Encoding.graphWord G).length = G.vertices ^ 2 + G.vertices + 1 := by
  classical
  simp [Encoding.graphWord, List.length_flatMap, pow_two]
  omega

/--
---
conclusion: Lax689614.Sizes.formula_length
---
-/
theorem formula_length (φ : PositiveCNF.Formula) :
    (Encoding.formulaWord φ).length =
      φ.clauses.length * φ.nvars + φ.nvars + φ.clauses.length + 2 := by
  simp [Encoding.formulaWord, List.length_flatMap]
  omega

/--
---
conclusion: Lax689614.Sizes.construction_size
---
-/
theorem construction_size (φ : PositiveCNF.Formula) :
    Construction.size φ = 13 * φ.nvars + 4 * φ.clauses.length + 18 := by
  simp only [Construction.size, Construction.K, Construction.R]
  omega

end Lax689614Proofs
