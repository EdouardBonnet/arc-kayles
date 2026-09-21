import Lax689614Proofs.EdgeCode
import Lax689614Proofs.Sizes

namespace Lax689614Proofs.MachineCode

open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930.PolynomialTime
open Lax689614

def sizeNumber {I : Type} (n m : Number I) : Number I :=
  (((Number.constant 13).mul n).add ((Number.constant 4).mul m)).add (.constant 18)

def adjTest {I : Type} (n m : Number I) (bits : I) (u w : Number I) : Test I :=
  (Test.eq u w).not.and ((edgeTest n m bits u w).or (edgeTest n m bits w u))

def rawAdj (n m : ℕ) (bits : Word) (u w : ℕ) : Prop :=
  u ≠ w ∧ (rawEdge n m bits u w ∨ rawEdge n m bits w u)

theorem adjTest_value {I : Type} (n m : Number I) (bits : I) (u w : Number I) (a : I → Word) :
    (adjTest n m bits u w).value a = true ↔ rawAdj (n.value a) (m.value a) (a bits) (u.value a) (w.value a) := by
  simp only [adjTest, Test.and, Bool.and_eq_true, Test.not, Bool.not_eq_true',
    Test.eq_value, decide_eq_false_iff_not, Test.or, Bool.or_eq_true, edgeTest_value, rawAdj]

theorem adjTest_decide {I : Type} (n m : Number I) (bits : I) (u w : Number I) (a : I → Word) :
    (adjTest n m bits u w).value a =
      @decide (rawAdj (n.value a) (m.value a) (a bits) (u.value a) (w.value a)) (Classical.propDecidable _) := by
  classical
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact adjTest_value n m bits u w a

def graphCode {I : Type} (n m : Number I) (bits : I) : Code I :=
  .append (sizeNumber n m).code (.append (.literal [false])
    (Code.loop (sizeNumber n m) (Code.loop ((sizeNumber n m).rename some)
      (adjTest (n.rename (some ∘ some)) (m.rename (some ∘ some)) (some (some bits))
        (.length (some none)) (.length none)).code)))

noncomputable def rawGraphWord (n m : ℕ) (bits : Word) : Word := by
  classical
  let N := 13 * n + 4 * m + 18
  exact List.replicate N true ++ [false] ++
    (List.range N).flatMap fun u => (List.range N).map fun w => decide (rawAdj n m bits u w)

theorem graphCode_eval {I : Type} (n m : Number I) (bits : I) (a : I → Word) :
    (graphCode n m bits).eval a = rawGraphWord (n.value a) (m.value a) (a bits) := by
  classical
  change (sizeNumber n m).code.eval a ++ ([false] ++
    (Code.loop (sizeNumber n m) (Code.loop ((sizeNumber n m).rename some)
      (adjTest (n.rename (some ∘ some)) (m.rename (some ∘ some)) (some (some bits))
        (.length (some none)) (.length none)).code)).eval a) = _
  rw [Number.correct]
  simp only [Code.eval_loop, Test.correct,
    adjTest_decide, sizeNumber, Number.add, Number.mul, Number.constant,
    Number.rename, Number.length, extend, Option.elim_none, Option.elim_some,
    List.length_replicate, Function.comp_def, rawGraphWord, List.flatMap_map,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [← List.map_eq_flatMap, List.append_assoc]

theorem map_finRange_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp

theorem rawGraphWord_correct (φ : PositiveCNF.Formula) :
    rawGraphWord φ.nvars φ.clauses.length (φ.clauses.flatMap clauseBits) =
      Encoding.graphWord (Construction.labeledGraph φ) := by
  classical
  have hAdj (u w : Fin (Construction.size φ)) :
      (Construction.labeledGraph φ).graph.Adj u w ↔
        rawAdj φ.nvars φ.clauses.length (φ.clauses.flatMap clauseBits) u.val w.val := by
    simp only [Construction.labeledGraph, SimpleGraph.fromRel_adj, rawAdj,
      rawEdge_construction, Fin.val_inj]
    exact and_congr_left (fun _ => not_congr Fin.val_injective.eq_iff.symm)
  simp only [rawGraphWord, Encoding.graphWord, Construction.labeledGraph]
  rw [← construction_size φ]
  rw [← map_finRange_val (Construction.size φ)]
  simp only [List.flatMap_map, List.map_map, Function.comp_def]
  congr 2
  congr 1
  funext u
  congr 1
  funext w
  exact congrArg (fun p : Prop => decide p) (propext (hAdj u w).symm)

end Lax689614Proofs.MachineCode
