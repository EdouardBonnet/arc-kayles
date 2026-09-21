import Lax689614Proofs.UniformPatterns
import Lax689614Proofs.CodeComputer

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CircuitStreaming

open Lax434930.PolynomialTime

namespace CS
export Lax434930Proofs.InclusionAux.TimeHelpers.Streaming (Code Number Test extend)
namespace Code
export Lax434930Proofs.InclusionAux.TimeHelpers.Streaming.Code (eval)
end Code
end CS

namespace CL
export Lax429075Proofs.Streaming (Code Number Test extend Expression)
namespace Code
export Lax429075Proofs.Streaming.Code (eval)
end Code
end CL

/-- Embed the Cook–Levin output language in the extended archive language.
    The latter additionally supports bounded state iteration. -/
def liftCode : {I : Type} → CL.Code I → CS.Code I
  | _, .literal w => .literal w
  | _, .source i => .source i
  | _, .length i => .length i
  | _, .drop s i => .drop s i
  | _, .inspect i f => .inspect i f
  | _, .append p q => .append (liftCode p) (liftCode q)
  | _, .bind p q => .bind (liftCode p) (liftCode q)
  | _, .branch i p q => .branch i (liftCode p) (liftCode q)
  | _, .forRange n p => .forRange n (liftCode p)

theorem liftCode_eval {I : Type} (c : CL.Code I) (a : I → Word) : (liftCode c).eval a = c.eval a := by
  induction c with
  | literal w | source i | length i | drop s i | inspect i f => rfl
  | append p q ihp ihq => simp only [liftCode, CS.Code.eval, CL.Code.eval, ihp, ihq]
  | bind p q ihp ihq =>
    simp only [liftCode, CS.Code.eval, CL.Code.eval, ihp, ihq]
    rfl
  | branch i p q ihp ihq => simp only [liftCode, CS.Code.eval, CL.Code.eval, ihp, ihq]
  | forRange n p ih =>
    simp only [liftCode, CS.Code.eval, CL.Code.eval, ih]
    rfl

def liftNumber {I : Type} (n : CL.Number I) : CS.Number I :=
  ⟨n.value, liftCode n.code, fun a => (liftCode_eval n.code a).trans (n.correct a)⟩

def liftTest {I : Type} (t : CL.Test I) : CS.Test I :=
  ⟨t.value, liftCode t.code, fun a => (liftCode_eval t.code a).trans (t.correct a)⟩

theorem cookCode_polynomial (c : CL.Code Unit) :
    Nonempty (Turing.TM2ComputableInPolyTime id id (fun w => c.eval (fun _ => w))) := by
  have h := MachineCode.code_polynomial_time (liftCode c)
  simpa only [liftCode_eval] using h

end Lax689614Proofs.CircuitStreaming
