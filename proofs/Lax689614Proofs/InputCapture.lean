import Lax689614Proofs.CodeStepper

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CodeStepper

open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram
open Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
open Lax434930Proofs.SavitchProofs
open StackLanguage
open Lax434930.PolynomialTime Lax434930.SpaceMachines
open scoped Classical

noncomputable section

theorem capture_data_ext {K Γ σ : Type} {d e : Data K Γ σ}
    (hs : d.state = e.state) (hi : d.inputHead = e.inputHead) (hk : d.store = e.store) : d = e := by
  cases d; cases e; cases hs; cases hi; cases hk; rfl

def inputBit : InputSymbol → Option Bool
  | .bit b => some b
  | _ => none

def sample (c : Code Bool) : Command (Keys c) Bool Register :=
  .input (fun q sym => (q.1, inputBit sym))

def captureBody (c : Code Bool) : Command (Keys c) Bool Register :=
  .seq (.push (fun _ => .output) (fun q => q.2.getD false))
    (.seq (.move (fun _ => .right)) (sample c))

def captureLoop (c : Code Bool) : Command (Keys c) Bool Register :=
  .loop (fun q => q.2.isSome) (captureBody c)

def captureConfig (c : Code Bool) (pre rest : Word) : Data (Keys c) Bool Register :=
  ⟨(((), none), rest.head?), pre.length + 1, fun k => if k = .output then pre.reverse else []⟩

theorem inputBit_append (pre rest : Word) :
    inputBit (readInput (pre ++ rest) (pre.length + 1)) = rest.head? := by
  simp only [readInput, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  cases rest <;> rfl

theorem capture_good (c : Code Bool) (w pre rest : Word) (bound : ℕ)
    (hw : w = pre ++ rest) (hb : w.length < bound) : Good w bound (captureConfig c pre rest) := by
  refine ⟨?_, ?_⟩
  · simp [captureConfig, hw]
  · intro k
    change (if k = Key.output then pre.reverse else []).length < bound
    split_ifs <;> simp only [List.length_reverse, List.length_nil]
    · have hh : pre.length ≤ w.length := by simp [hw]
      omega
    · omega

theorem capture_loop (c : Code Bool) (w pre rest : Word) (bound : ℕ)
    (hw : w = pre ++ rest) (hb : w.length < bound) :
    Exec w bound (captureLoop c) (captureConfig c pre rest) (captureConfig c w []) := by
  induction rest generalizing pre with
  | nil =>
    have he : w = pre := by simpa using hw
    subst pre
    exact .loop_false _ _ _ (capture_good c w w [] bound (by simp) hb) rfl
  | cons b rest ih =>
    let d := captureConfig c pre (b :: rest)
    let e := pushed d .output b
    have hd := capture_good c w pre (b :: rest) bound hw hb
    have he : Good w bound e := by
      refine ⟨hd.1, ?_⟩
      intro k
      by_cases hk : k = Key.output
      · subst k
        have hl : pre.length + 1 ≤ w.length := by simp [hw]
        have hlt : pre.length + 1 < bound := by omega
        simpa [e, pushed, d, captureConfig] using hlt
      · simpa [e, pushed, hk] using hd.2 k
    have hp : Exec w bound (.push (fun _ => Key.output) (fun q : Register => q.2.getD false)) d e :=
      .push _ _ _ hd he
    let m := moved w e .right
    have hm : Exec w bound (.move (fun _ : Register => .right)) e m := .move _ _ he
    have hh : m.inputHead = (pre ++ [b]).length + 1 := by
      have hi : pre.length + 1 + 1 ≤ w.length + 1 := by simp [hw] <;> omega
      simp [m, moved, e, pushed, d, captureConfig, Move.apply, Nat.min_eq_left hi]
    have hs : Exec w bound (sample c) m (assigned m (m.state.1, inputBit (readInput w m.inputHead))) :=
      .input _ _ hm.good.2
    have hw' : w = (pre ++ [b]) ++ rest := by simpa [List.append_assoc] using hw
    have hout : assigned m (m.state.1, inputBit (readInput w m.inputHead)) =
        captureConfig c (pre ++ [b]) rest := by
      apply capture_data_ext
      · simp only [assigned, hh, hw', inputBit_append]
        rfl
      · exact hh
      · funext k
        by_cases hk : k = Key.output <;>
          simp [assigned, m, moved, e, pushed, d, captureConfig, hk]
    rw [hout] at hs
    exact .loop_true rfl (.seq hp (.seq hm hs)) (ih (pre ++ [b]) hw')

def capture (c : Code Bool) : Command (Keys c) Bool Register :=
  .seq (.move (fun _ => .right)) (.seq (sample c)
    (.seq (captureLoop c) (ProgramSpace.compile (transfer .output (.input false)))))

theorem capture_input (c : Code Bool) (w : Word) (bound : ℕ) (hb : 4 * w.length + 2 < bound) :
    Exec w bound (capture c) ⟨(((), none), none), 0, fun _ => []⟩
      (ProgramSpace.encode (configuration c w [] none) (w.length + 1)) := by
  let d : Data (Keys c) Bool Register := ⟨(((), none), none), 0, fun _ => []⟩
  have hd : Good w bound d := ⟨by simp [d], by intro k; change 0 < bound; omega⟩
  have hm := Exec.move d (fun _ : Register => Move.right) hd
  let e := moved w d .right
  have he : e.inputHead = 1 := by simp [e, moved, Move.apply, d]
  have hs := Exec.input e (fun q : Register => fun sym => (q.1, inputBit sym)) hm.good.2
  have hout : assigned e (e.state.1, inputBit (readInput w e.inputHead)) = captureConfig c [] w := by
    apply capture_data_ext
    · rw [he]
      simpa [assigned, e, moved, d, captureConfig] using inputBit_append [] w
    · exact he
    · funext k; simp [assigned, e, moved, d, captureConfig]
  rw [hout] at hs
  have hl := capture_loop c w [] w bound (by simp) (by omega)
  let s : BitStore (Keys c) Unit := ⟨((), none), fun k => if k = .output then w.reverse else []⟩
  have htr := transfer_store (Key.output : Keys c) (.input false) (by simp) s
  have hstart : ProgramSpace.encode s (w.length + 1) = captureConfig c w [] := rfl
  have hfinal : (⟨(s.state.1, none), Function.update (Function.update s.stk .output []) (.input false)
      ((s.stk .output).reverse ++ s.stk (.input false))⟩ : BitStore (Keys c) Unit) =
      configuration c w [] none := by
    apply Store.ext
    · rfl
    · funext k; cases k with
      | input i => cases i <;> simp [s, configuration, store, args]
      | output => simp [s, configuration, store]
      | work k => simp [s, configuration, store]
  rw [hfinal] at htr
  have hspace := ProgramSpace.executes_space w bound (w.length + 1) (Nat.le_refl _) htr
    (by
      intro k
      have hk : (s.stk k).length ≤ w.length := by
        simp only [s]; split_ifs <;> simp
      have ho : (s.stk .output).length = w.length := by simp [s]
      rw [ho]; omega)
  rw [hstart] at hspace
  exact .seq hm (.seq hs (.seq hl hspace))

end

end Lax689614Proofs.CodeStepper
