import Lax689614Proofs.ReachabilityBounds
import Lax689614Proofs.ByskovEncoding

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax429075Proofs.CircuitBuilder Lax429075Proofs.Streaming
open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs ConfigurationWords
open Lax429075

def fragmentCode {I : Type} (e : Expression I) (start : Number I) : Code I :=
  .append (Code.segment [[(e.outputAt start, .constant true)]])
    (.append (e.run start) (.literal [false]))

theorem fragmentCode_eval {I : Type} (e : Expression I) (start : Number I) (a : I → Word) :
    (fragmentCode e start).eval a =
      Lax429075.Encoding.encodeCNF (Quantified.fragmentCNF (start.value a) (e.value a)) := by
  rw [fragmentCode, Code.eval, Code.eval_segment, Code.eval, Expression.eval_run]
  simp only [Code.eval, List.map_cons, List.map_nil, LiteralCode.value,
    Expression.outputAt_value, Test.constant]
  rw [← Lax429075Proofs.CNFOutput.segment_encode]
  simp only [Quantified.fragmentCNF, Lax429075Proofs.CNFOutput.segment, List.flatMap_append,
    List.flatMap_assoc, gatesWord, List.append_assoc]
  rfl

def roundFlags (n : ℕ) : Word := List.replicate n false ++ true :: List.replicate (2 * n) false

theorem roundPrefix_expand (n : ℕ) :
    Quantified.Prefix.expand (Quantified.NumericReach.roundPrefix n) = roundFlags n := by
  change List.replicate n false ++ (List.replicate 1 true ++
    (List.replicate n false ++ (List.replicate n false ++ []))) =
    List.replicate n false ++ true :: List.replicate (2 * n) false
  rw [two_mul, List.replicate_add]
  simp

theorem reachPrefix_expand (n d : ℕ) :
    Quantified.Prefix.expand (Quantified.NumericReach.reachPrefix n d) =
      (List.range d).flatMap (fun _ => roundFlags n) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [Quantified.NumericReach.reachPrefix]
    simp only [Quantified.Prefix.expand, List.flatMap_append]
    rw [← Quantified.Prefix.expand, roundPrefix_expand, ← Quantified.Prefix.expand, ih]
    simp [List.range_succ_eq_map, List.flatMap_map]

def falseCode {I : Type} (n : Number I) : Code I := Code.loop n (.literal [false])

theorem falseCode_eval {I : Type} (n : Number I) (a : I → Word) :
    (falseCode n).eval a = List.replicate (n.value a) false := by
  simp only [falseCode, Code.eval_loop, Code.eval]
  induction n.value a with
  | zero => rfl
  | succ j ih => simp [List.range_succ, ih, List.replicate_succ']

def flagsCode {I : Type} (n gates : Number I) : Code I :=
  .append (Code.loop n (.append (falseCode (n.rename some))
    (.append (.literal [true]) (falseCode ((Number.constant 2).mul (n.rename some)))))) (falseCode gates)

theorem flagsCode_eval {I : Type} (n gates : Number I) (a : I → Word) :
    (flagsCode n gates).eval a = Quantified.Prefix.expand
      (Quantified.NumericReach.reachPrefix (n.value a) (n.value a) ++ [(false, gates.value a)]) := by
  simp only [flagsCode, Code.eval, Code.eval_loop, falseCode_eval, Number.rename,
    Number.mul, Number.constant, extend_some, Quantified.Prefix.expand, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [← Quantified.Prefix.expand, reachPrefix_expand]
  rfl

def quantifierNumber {I : Type} (n : Number I) : Number I := n.mul (widthNumber n)

noncomputable def machineClauses (M : Machine) {I : Type} (input table : I)
    (count k : Number I) (a : I → Word) : CNF.Formula :=
  Quantified.fragmentCNF ((quantifierNumber (bitNumber M count)).value a)
    ((machineMatrix M input table count k).value a)

noncomputable def machinePrefix (M : Machine) {I : Type} (input table : I)
    (count k : Number I) (a : I → Word) : Quantified.Prefix :=
  Quantified.NumericReach.reachPrefix ((bitNumber M count).value a) ((bitNumber M count).value a) ++
    [(false, ((machineMatrix M input table count k).cost).value a)]

theorem machineClauses_bounded (M : Machine) {I : Type} (input table : I)
    (count k : Number I) (a : I → Word) (hk : k.value a + 2 ≤ count.value a) :
    Quantified.CNFBounded (Quantified.Prefix.expand (machinePrefix M input table count k a)).length
      (machineClauses M input table count k a) := by
  have hb := machineMatrix_bounded M input table count k a hk
  rw [Quantified.NumericReach.reachPrefix_count] at hb
  have h := Quantified.fragmentCNF_bounded _ _ hb
  have hp : (Quantified.Prefix.expand (machinePrefix M input table count k a)).length =
      (quantifierNumber (bitNumber M count)).value a +
        (compile ((quantifierNumber (bitNumber M count)).value a)
          ((machineMatrix M input table count k).value a)).gates.length := by
    simp only [machinePrefix, Quantified.Prefix.expand, List.flatMap_append,
    List.length_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_replicate,
    Expression.cost_correct, compile_length]
    change (Quantified.NumericReach.reachPrefix _ _).count + _ = _
    rw [Quantified.NumericReach.reachPrefix_count]
    rfl
  rw [hp]
  simpa only [machineClauses,
    compile_length, quantifierNumber, Number.mul, widthNumber, Number.add, Number.constant,
    Quantified.NumericReach.width] using h

theorem machineCNF_truth (M : Machine) {I : Type} (input table : I)
    (count k : Number I) (a : I → Word) (s : ℕ)
    (hc : count.value a = k.value a + s + 2)
    (ht : a table = digitTable ((a input).length + 2) (k.value a))
    (hk : (a input).length + 1 < 2 ^ k.value a) (hs : M.UsesSpace (a input) s) :
    (machinePrefix M input table count k a).Holds (machineClauses M input table count k a) 0
      (fun _ => false) ↔ M.Accepts (a input) := by
  have hb := machineMatrix_bounded M input table count k a (by omega)
  have h := Quantified.Prefix.compile_matrix
    (Quantified.NumericReach.reachPrefix ((bitNumber M count).value a) ((bitNumber M count).value a))
    0 (fun _ => false) ((machineMatrix M input table count k).value a) (by simpa using hb)
  simp only [Nat.zero_add, Quantified.NumericReach.reachPrefix_count, compile_length] at h
  simpa only [machinePrefix, machineClauses, Expression.cost_correct, quantifierNumber,
    widthNumber, Number.mul, Number.add, Number.constant, Quantified.NumericReach.width] using
    h.trans (machineMatrix_truth M input table count k a _ s hc ht hk hs)

end Lax689614Proofs.CircuitStreaming
