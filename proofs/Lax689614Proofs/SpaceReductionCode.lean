import Lax689614Proofs.MachineCNF
import Lax689614Proofs.CNFMatrixCode
import Lax689614Proofs.ByskovPolynomial
import Lax429075Proofs.OutputPolynomials

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax429075Proofs.Streaming

noncomputable def machineSignedCode (M : Machine) {I : Type} (input table : I)
    (count k : Number I) : CS.Code I :=
  let e := machineMatrix M input table count k
  let n := bitNumber M count
  .bind (liftCode (flagsCode n e.cost))
    (.bind ((liftCode (fragmentCode e (quantifierNumber n))).rename some)
      (CNFTraversal.signedMatrixCode (some none) none))

theorem machineSignedCode_eval (M : Machine) {I : Type} (input table : I)
    (count k : Number I) (a : I → Word) :
    (machineSignedCode M input table count k).eval a =
      Byskov.signedWord (Quantified.signedFormula
        (Quantified.Prefix.expand (machinePrefix M input table count k a)).length
        (fun i => (Quantified.Prefix.expand (machinePrefix M input table count k a))[i.val])
        (machineClauses M input table count k a)) := by
  simp only [machineSignedCode, CS.Code.eval, liftCode_eval, flagsCode_eval,
    Lax434930Proofs.InclusionAux.TimeHelpers.Streaming.Code.eval_rename,
    Lax434930Proofs.InclusionAux.TimeHelpers.Streaming.extend_some, fragmentCode_eval]
  exact CNFTraversal.signedMatrixCode_eval (some none) none _ _ rfl

def inputWidth {I : Type} (input : I) : Number I := (Number.length input).add (.constant 2)

noncomputable def configurationCount {I : Type} (p : Polynomial ℕ) (input : I) : Number I :=
  ((inputWidth input).add (Number.polynomial p (.length input))).add (.constant 2)

def sourceEnvironment (w : Word) : Option Unit → Word :=
  extend (fun _ => w) (digitTable (w.length + 2) (w.length + 2))

noncomputable def sourceCode (M : Machine) (p : Polynomial ℕ) : CS.Code Unit :=
  .bind (digitTableCode (liftNumber (inputWidth ())) (liftNumber (inputWidth ())))
    (machineSignedCode M (some ()) none (configurationCount p (some ())) (inputWidth (some ())))

noncomputable def sourceSignedFormula (M : Machine) (p : Polynomial ℕ) (w : Word) :
    Byskov.SignedCNF (Quantified.Prefix.expand (machinePrefix M (some ()) none
      (configurationCount p (some ())) (inputWidth (some ())) (sourceEnvironment w))).length :=
  let qs := Quantified.Prefix.expand (machinePrefix M (some ()) none
    (configurationCount p (some ())) (inputWidth (some ())) (sourceEnvironment w))
  Quantified.signedFormula qs.length (fun i => qs[i.val])
    (machineClauses M (some ()) none (configurationCount p (some ()))
      (inputWidth (some ())) (sourceEnvironment w))

theorem sourceCode_eval (M : Machine) (p : Polynomial ℕ) (w : Word) :
    (sourceCode M p).eval (fun _ => w) = Byskov.signedWord (sourceSignedFormula M p w) := by
  rw [sourceCode, CS.Code.eval, digitTableCode_eval, machineSignedCode_eval]
  rfl

theorem sourceSignedFormula_correct (M : Machine) (p : Polynomial ℕ) (w : Word)
    (hs : M.UsesSpace w (p.eval w.length)) :
    (sourceSignedFormula M p w).True ↔ M.Accepts w := by
  have hc : (configurationCount p (some ())).value (sourceEnvironment w) =
      (inputWidth (some ())).value (sourceEnvironment w) + p.eval w.length + 2 := by
    simp [configurationCount, Number.add, Number.constant, Number.polynomial_value,
      Number.length, sourceEnvironment, extend]
  have hb := machineClauses_bounded M (some ()) none (configurationCount p (some ()))
    (inputWidth (some ())) (sourceEnvironment w) (by omega)
  rw [sourceSignedFormula, Quantified.signedFormula_correct _ _ hb, Quantified.Prefix.expand_correct]
  apply machineCNF_truth M (some ()) none _ _ (sourceEnvironment w) (p.eval w.length) hc
  · rfl
  · change w.length + 1 < 2 ^ (w.length + 2)
    have h : w.length + 2 < 2 ^ (w.length + 2) := Nat.lt_two_pow_self
    omega
  · exact hs

theorem sourceCode_correct (M : Machine) (p : Polynomial ℕ) (w : Word)
    (hs : M.UsesSpace w (p.eval w.length)) :
    (sourceCode M p).eval (fun _ => w) ∈ Byskov.signedLanguage ↔ M.Accepts w := by
  rw [sourceCode_eval, Byskov.signedWord_mem, sourceSignedFormula_correct M p w hs]

end Lax689614Proofs.CircuitStreaming
