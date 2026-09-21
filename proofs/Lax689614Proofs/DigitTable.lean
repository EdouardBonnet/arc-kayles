import Lax689614Proofs.StreamingBridge
import Lax689614Proofs.MatrixBits
import Lax689614Proofs.GraphCode
import Lax434930Proofs.SavitchProofs.BinaryWords

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax434930.PolynomialTime
open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930Proofs.SavitchProofs

theorem binaryWord_get (width value : ℕ) (j : Fin width) :
    (BinaryCounter.word width value)[j.val]'(by simp) = decide (value / 2 ^ j.val % 2 = 1) := by
  induction width generalizing value with
  | zero => exact Fin.elim0 j
  | succ width ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [BinaryCounter.word]
    · simp only [BinaryCounter.word, Fin.val_succ, List.getElem_cons_succ, ih,
        Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]

def digitRow (width value : ℕ) : Finset (Fin width) :=
  Finset.univ.filter (fun j => value / 2 ^ j.val % 2 = 1)

theorem binaryWord_clauseBits (width value : ℕ) : BinaryCounter.word width value = clauseBits (digitRow width value) := by
  apply List.ext_getElem
  · simp [clauseBits]
  · intro j hj hk
    have hjw : j < width := by simpa using hj
    rw [binaryWord_get width value ⟨j, hjw⟩]
    simp [clauseBits, digitRow]

def digitRowCode {I : Type} (width value : Number I) : Code I :=
  Code.loop width (Test.eq
    ((value.rename some).digit (.constant 2) (.length none)) (.constant 1)).code

theorem digitRowCode_eval {I : Type} (width value : Number I) (a : I → Word) :
    (digitRowCode width value).eval a = BinaryCounter.word (width.value a) (value.value a) := by
  rw [binaryWord_clauseBits]
  simp only [digitRowCode, Code.eval_loop, Test.correct, Test.eq_value, Number.digit_value,
    Number.rename, Number.length, Number.constant, extend_some, extend, Option.elim_none,
    List.length_replicate, List.flatMap_map, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, ← List.map_eq_flatMap]
  rw [← MachineCode.map_finRange_val (width.value a), List.map_map]
  simp [clauseBits, digitRow]

def digitTableCode {I : Type} (bound width : Number I) : Code I :=
  Code.loop bound (digitRowCode (width.rename some) (.length none))

def digitTable (bound width : ℕ) : Word :=
  (List.range bound).flatMap (BinaryCounter.word width)

theorem digitTableCode_eval {I : Type} (bound width : Number I) (a : I → Word) :
    (digitTableCode bound width).eval a = digitTable (bound.value a) (width.value a) := by
  simp only [digitTableCode, Code.eval_loop, digitRowCode_eval, Number.rename,
    Number.length, extend_some, extend, Option.elim_none, List.length_replicate, digitTable]

theorem digitTable_matrix (bound width : ℕ) :
    digitTable bound width = ((List.finRange bound).map (fun i => digitRow width i.val)).flatMap clauseBits := by
  rw [digitTable, ← MachineCode.map_finRange_val bound]
  simp only [List.flatMap_map, Function.comp_def, binaryWord_clauseBits]

theorem digitTable_get (bound width : ℕ) (i : Fin bound) (j : Fin width) :
    (digitTable bound width)[i.val * width + j.val]? = some (decide (i.val / 2 ^ j.val % 2 = 1)) := by
  rw [digitTable_matrix]
  have h := clausesBits_get ((List.finRange bound).map (fun i => digitRow width i.val))
    ⟨i.val, by simpa using i.isLt⟩ j
  simpa [digitRow] using h

end Lax689614Proofs.CircuitStreaming
