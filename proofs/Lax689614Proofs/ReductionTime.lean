import Lax689614Proofs.HeaderCode
import Lax689614Proofs.WordReduction

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.MachineCode

open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930.PolynomialTime Lax689614

noncomputable def reductionBody : Code HeaderContext :=
  Code.when (validTest (.length nIndex) (.length mIndex) wordIndex tailIndex none)
    (Code.when (Test.eq (.length mIndex) (.constant 0))
      (.literal (Encoding.graphWord yesGraph))
      (normalizedGraphCode (.length nIndex) (.length mIndex) none))
    (.literal (Encoding.graphWord noGraph))

noncomputable def reductionCode : Code Unit := withHeader reductionBody

theorem reductionCode_correct (w : Word) :
    reductionCode.eval (fun _ => w) = reduceWord w := by
  rw [reductionCode, withHeader_eval]
  unfold reductionBody
  rw [Code.eval_when]
  by_cases hv : ValidHeader w
  · rw [(validTest_header w).mpr hv]
    simp only [↓reduceIte]
    rw [Code.eval_when]
    obtain ⟨φ, hp⟩ := parse_of_header w hv
    obtain ⟨hn, hm, hbits, _⟩ := header_of_parse hp
    have hnv : (Number.length nIndex).value (headerEnv w) = φ.nvars := by
      simpa [Number.length, headerEnv, nIndex, extend] using hn
    have hmv : (Number.length mIndex).value (headerEnv w) = φ.clauses.length := by
      simpa [Number.length, headerEnv, mIndex, extend] using hm
    have hbitv : headerEnv w none = φ.clauses.flatMap clauseBits := hbits
    have hzero : (Test.eq (.length mIndex) (.constant 0)).value (headerEnv w) =
        decide (φ.clauses = []) := by
      rw [Test.eq_value, hmv]
      simp [Number.constant]
    rw [hzero]
    by_cases hc : φ.clauses = []
    · simp [hc, Code.eval, reduceWord, hp]
    · simp only [hc, decide_false, ↓reduceIte, reduceWord, hp]
      exact normalizedGraphCode_correct _ _ _ _ φ hnv hmv hbitv hc
  · have htest : (validTest (.length nIndex) (.length mIndex) wordIndex tailIndex none).value
        (headerEnv w) = false := by
      cases ht : (validTest (.length nIndex) (.length mIndex) wordIndex tailIndex none).value (headerEnv w)
      · rfl
      · exact False.elim (hv ((validTest_header w).mp ht))
    have hp : parseFormula w = none := by
      cases hp : parseFormula w with
      | none => rfl
      | some φ => exact False.elim (hv (header_of_parse hp).2.2.2)
    simp [htest, Code.eval, reduceWord, hp]

theorem reduceWord_polytime : Nonempty (Turing.TM2ComputableInPolyTime id id reduceWord) := by
  have he : (fun w => reductionCode.eval (fun _ => w)) = reduceWord := funext reductionCode_correct
  rw [← he]
  exact code_polynomial_time reductionCode

end Lax689614Proofs.MachineCode

namespace Lax689614Proofs

/--
---
conclusion: Lax689614.Reduction.polynomial_reduction
---
Compile unary header checks, clause normalization, and adjacency-matrix
generation into a finite stack program with a polynomial step bound.
The archived compiler supplies the Turing-machine witness. The separately
proved word-level correctness theorem handles every binary input.
-/
theorem polynomial_reduction :
    Lax429075.Reductions.ManyOne Lax689614.Encoding.positiveCNF Lax689614.Encoding.arcKayles :=
  ⟨reduceWord, MachineCode.reduceWord_polytime, reduceWord_correct⟩

end Lax689614Proofs
