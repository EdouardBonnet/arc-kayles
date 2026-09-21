import Lax689614Proofs.ReachabilityCircuit
import Lax689614Proofs.SpaceToQuantified

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax429075Proofs.CircuitBuilder Lax429075Proofs.Streaming
open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax434930Proofs.SavitchProofs ConfigurationWords
open Lax434930Proofs.SavitchDefinitions.Reachability
open Quantified (Vector vectorNumber)

def lastNumber {I : Type} (n depth : Number I) (side : Bool) : Number I :=
  if side then rightNumber n ((depth.sub (.constant 1)).mul (widthNumber n))
  else leftNumber n ((depth.sub (.constant 1)).mul (widthNumber n))

theorem endpoint_last {I : Type} (n depth : Number I) (side : Bool)
    (a : I → Word) (hd : 0 < depth.value a) :
    Quantified.NumericReach.endpoint (n.value a) (depth.value a) side =
      Quantified.NumericReach.readVector (n.value a) ((lastNumber n depth side).value a) := by
  obtain ⟨j, hj⟩ : ∃ j, depth.value a = j + 1 := ⟨depth.value a - 1, by omega⟩
  cases side <;> simp [hj, Quantified.NumericReach.endpoint, lastNumber,
    leftNumber, rightNumber, widthNumber, Number.add, Number.mul, Number.sub, Number.constant,
    Quantified.NumericReach.leftBase, Quantified.NumericReach.rightBase, Quantified.NumericReach.width]

theorem decode_read (M : Machine) (n base : ℕ) (ρ : ℕ → Bool) :
    EncodedGraph.decode M n (vectorNumber (Quantified.NumericReach.readVector n base ρ)) =
      FiniteCoding.decodeWord (Payload M) (slice ρ base n) := by
  unfold EncodedGraph.decode vectorNumber
  rw [show BinaryCounter.word n (BinaryCounter.value
      (Quantified.vectorWord (Quantified.NumericReach.readVector n base ρ))) =
      Quantified.vectorWord (Quantified.NumericReach.readVector n base ρ) from
    by simpa only [Quantified.vectorWord_length] using
      BinaryCounter.word_of_value (Quantified.vectorWord (Quantified.NumericReach.readVector n base ρ))]
  exact congrArg (FiniteCoding.decodeWord (Payload M)) (vectorWord_slice ρ base n)

def bitNumber (M : Machine) {I : Type} (count : Number I) : Number I :=
  (Number.constant (FiniteCoding.width (Payload M))).mul count

noncomputable def machineMatrix (M : Machine) {I : Type} (input table : I)
    (count k : Number I) : Expression I :=
  let n := bitNumber M count
  matrixExpression n n (transitionExpression M input table count k
    (lastNumber n n false) (lastNumber n n true))

theorem machineMatrix_eval (M : Machine) {I : Type} (input table : I)
    (count k : Number I) (a : I → Word) (ρ : ℕ → Bool)
    (hc : 0 < count.value a)
    (ht : a table = digitTable ((a input).length + 2) (k.value a)) :
    ((machineMatrix M input table count k).value a).eval ρ = true ↔
      Quantified.NumericReach.matrixCondition ((bitNumber M count).value a)
        ((bitNumber M count).value a)
        (fun x y => Quantified.ConfigurationGraph.graph M (a input) (k.value a) (count.value a)
          (vectorNumber x) (vectorNumber y) = true) ρ := by
  apply matrixExpression_eval
  have hn : 0 < (bitNumber M count).value a :=
    Nat.mul_pos (FiniteCoding.width_pos (Payload M)) hc
  simp only [endpoint_last (bitNumber M count) (bitNumber M count) false a hn,
    endpoint_last (bitNumber M count) (bitNumber M count) true a hn]
  simp only [bitNumber, Number.mul, Number.constant]
  rw [Quantified.ConfigurationGraph.edge_iff, decode_read, decode_read]
  exact transitionExpression_correct M input table count k _ _ a ρ ht

theorem machineMatrix_truth (M : Machine) {I : Type} (input table : I)
    (count k : Number I) (a : I → Word) (ρ : ℕ → Bool) (s : ℕ)
    (hc : count.value a = k.value a + s + 2)
    (ht : a table = digitTable ((a input).length + 2) (k.value a))
    (hk : (a input).length + 1 < 2 ^ k.value a) (hs : M.UsesSpace (a input) s) :
    Quantified.Prefix.Truth (fun b => ((machineMatrix M input table count k).value a).eval b = true)
      (Quantified.NumericReach.reachPrefix ((bitNumber M count).value a) ((bitNumber M count).value a))
      0 ρ ↔ M.Accepts (a input) := by
  rw [Quantified.Prefix.truth_congr _ _ _
    (fun b => machineMatrix_eval M input table count k a b (by omega) ht)]
  rw [Quantified.NumericReach.truth_matrixCondition]
  simp only [bitNumber, Number.mul, Number.constant]
  let E := fun x y => Quantified.ConfigurationGraph.graph M (a input) (k.value a) (count.value a) x y = true
  have he := Quantified.within_equiv (Quantified.vectorEquiv _)
    (fun x y => E (vectorNumber x) (vectorNumber y)) E (fun _ _ => Iff.rfl)
    (2 ^ (FiniteCoding.width (Payload M) * count.value a)) (fun _ => false) (fun _ => true)
  apply he.trans
  change Within E _ (vectorNumber (fun _ => false)) (vectorNumber (fun _ => true)) ↔ _
  rw [Quantified.vectorNumber_zero, Quantified.vectorNumber_one, ← recursive_reachability]
  change search (Quantified.ConfigurationGraph.graph M (a input) (k.value a) (count.value a))
    (FiniteCoding.width (Payload M) * count.value a) (EncodedGraph.first _) (EncodedGraph.last _) = true ↔ _
  have result := Quantified.ConfigurationGraph.search_correct M (a input) (k.value a) s hk hs
  dsimp only at result
  rw [← hc] at result
  exact result

end Lax689614Proofs.CircuitStreaming
