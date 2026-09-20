import Lax434930Proofs.InclusionAux.TimeHelpers.BoundedCode
import Lax434930Proofs.InclusionAux.TimeCompiler.StackClear

/-!
The output-buffer conversion below adapts the Apache-2.0 proof in
`Lax429075Proofs.OutputMachine` (Cook–Levin, commit
905f2da2698d5b38002676f74632aa716e731389) to the classical-complexity
package's extended `Code`, which also has space-capped iteration.
-/

namespace Lax689614Proofs.MachineCode

open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram
open Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
open Lax434930Proofs.InclusionAux.TimeCompiler.StackRename
open Lax434930Proofs.InclusionAux.TimeCompiler.StackClear (clear clear_store)
open Lax434930.PolynomialTime Polynomial Turing
open Lax434930Proofs.InclusionAux.TimeHelpers.CNFOutput

theorem code_polynomial_time (c : Code Unit) :
    Nonempty (TM2ComputableInPolyTime id id (fun x => c.eval (fun _ => x))) := by
  classical
  let p := c.emitter
  let K := Key Unit (Option p.Workspace)
  let input : K := .input ()
  let output : K := .work none
  let program : BitProgram K Unit := .seq (rename (workMap some) p.program)
    (.seq (clear input) (transfer .output output))
  apply program_polytime program input output ((), none) id id
    (fun x => c.eval (fun _ => x)) (C 4 * p.bound + C 2 * X + C 4)
  intro x
  let a : Unit → Word := fun _ => x
  let s : BitStore K Unit := ioStore input ((), none) x
  obtain ⟨t, ht, he⟩ := p.run_in (workMap some) (workMap_injective _ (Option.some_injective _))
    s a x.length (by intro i; cases i; simp [s, input, workMap, ioStore, a])
    (by intro w; simp [s, input, workMap, ioStore]) (by intro i; rfl)
  simp only [workMap] at he
  let mid := emitted Key.output (c.eval a) s
  have hclear := clear_store input mid
  let cleaned : BitStore K Unit := ⟨((), none), Function.update mid.stk input []⟩
  change Executes (clear input) mid cleaned (2 * (mid.stk input).length + 2) at hclear
  have htransfer := transfer_store (Key.output : K) output (by simp [output]) cleaned
  have hinput : mid.stk input = x := by simp [mid, emitted, s, ioStore, input]
  have hbuffer : cleaned.stk Key.output = (c.eval a).reverse := by
    simp [cleaned, mid, emitted, s, ioStore, input]
  rw [hinput] at hclear
  rw [hbuffer, List.length_reverse] at htransfer
  have hend : (⟨(cleaned.state.1, none),
      Function.update (Function.update cleaned.stk Key.output []) output
        (((c.eval a).reverse).reverse ++ cleaned.stk output)⟩ : BitStore K Unit) =
      ioStore output ((), none) (c.eval a) := by
    apply Store.ext <;> try rfl
    funext k
    rcases k with u | _ | w
    · cases u; simp [cleaned, mid, emitted, s, ioStore, input, output]
    · simp [cleaned, mid, emitted, s, ioStore, input, output]
    · cases w <;> simp [cleaned, mid, emitted, s, ioStore, input, output, Function.update_apply]
  rw [hend] at htransfer
  have hlen := p.length_bound a x.length (by intro i; rfl)
  refine ⟨t + ((2 * x.length + 2) + (3 * (c.eval a).length + 2)), ?_,
    .seq he (.seq hclear htransfer)⟩
  simp only [eval_add, eval_mul, eval_C, eval_X, id_eq]
  change (c.eval a).length ≤ p.bound.eval x.length at hlen
  omega

end Lax689614Proofs.MachineCode
