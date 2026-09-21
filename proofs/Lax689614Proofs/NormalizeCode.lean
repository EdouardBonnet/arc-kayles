import Lax689614Proofs.GraphCode

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.MachineCode

open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930.PolynomialTime Lax689614 PositiveCNF

def takeCode {I : Type} (n : Number I) (bits : I) : Code I :=
  Code.loop n (Test.input (some bits) (.length none)).code

theorem takeCode_eval {I : Type} (n : Number I) (bits : I) (a : I → Word) :
    (takeCode n bits).eval a = (List.range (n.value a)).map fun i => ((a bits)[i]?).getD false := by
  simp only [takeCode, Code.eval_loop, Test.correct, Test.input, Number.length,
    extend, Option.elim_none, Option.elim_some, List.length_replicate, ← List.map_eq_flatMap]
  simp [Code.eval, extend, List.head?_drop, ← List.map_eq_flatMap]

theorem take_as_range (w : Word) (n : ℕ) (hn : n ≤ w.length) :
    (List.range n).map (fun i => (w[i]?).getD false) = w.take n := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    cases w with
    | nil => simp at hn
    | cons b w =>
      have hn' : n ≤ w.length := by simpa using hn
      simpa [List.range_succ_eq_map, List.map_map, Function.comp_def] using congrArg (List.cons b) (ih w hn')

def oddTest {I : Type} (m : Number I) : Test I := Test.eq (m.mod (.constant 2)) (.constant 1)
def oddNumber {I : Type} (m : Number I) : Number I :=
  Number.choose (oddTest m) m (m.add (.constant 1))

def normalizeBitsCode {I : Type} (n m : Number I) (bits : I) : Code I :=
  Code.when (oddTest m) (.source bits) (.append (.source bits) (takeCode n bits))

def normalizedGraphCode {I : Type} (n m : Number I) (bits : I) : Code I :=
  .bind (normalizeBitsCode n m bits) (graphCode (n.rename some) ((oddNumber m).rename some) none)

theorem oddTest_value {I : Type} (m : Number I) (a : I → Word) :
    (oddTest m).value a = decide (m.value a % 2 = 1) := by
  simp [oddTest, Test.eq_value, Number.mod, Number.constant]

theorem normalizedGraphCode_correct {I : Type} (n m : Number I) (bits : I) (a : I → Word)
    (φ : Formula) (hn : n.value a = φ.nvars) (hm : m.value a = φ.clauses.length)
    (hbits : a bits = φ.clauses.flatMap clauseBits) (hc : φ.clauses ≠ []) :
    (normalizedGraphCode n m bits).eval a = Encoding.graphWord (Construction.labeledGraph (oddify φ)) := by
  have hpos : 0 < φ.clauses.length := List.length_pos_iff.mpr hc
  have htake : (takeCode n bits).eval a = (φ.clauses.take 1).flatMap clauseBits := by
    rw [takeCode_eval, hn, hbits, take_as_range]
    · exact clausesBits_take_first φ.clauses
    · rw [clausesBits_length]; nlinarith
  have hm' : (oddNumber m).value a = (oddify φ).clauses.length := by
    simp only [oddNumber, Number.choose, oddTest_value, hm, Number.add, Number.constant, oddify,
      decide_eq_true_eq]
    split_ifs
    · rfl
    · simp only [List.length_append, List.length_take]; omega
  have hbits' : (normalizeBitsCode n m bits).eval a = (oddify φ).clauses.flatMap clauseBits := by
    simp only [normalizeBitsCode, Code.eval_when, oddTest_value, hm, oddify, decide_eq_true_eq]
    split_ifs
    · exact hbits
    · change a bits ++ (takeCode n bits).eval a = _
      rw [hbits, htake, List.flatMap_append]
  change (graphCode (n.rename some) ((oddNumber m).rename some) none).eval
    (extend a ((normalizeBitsCode n m bits).eval a)) = _
  rw [graphCode_eval]
  change rawGraphWord (n.value a) ((oddNumber m).value a) ((normalizeBitsCode n m bits).eval a) = _
  rw [hn, hm', hbits']
  exact rawGraphWord_correct (oddify φ)

end Lax689614Proofs.MachineCode
