import Lax689614Proofs.TransitionCode
import Lax689614Proofs.ProgramSpace

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CodeStepper

noncomputable section

open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram
open Lax434930Proofs.InclusionAux.TimeCompiler.StackTransfer
open Lax434930Proofs.InclusionAux.TimeCompiler.StackClear
open Lax434930Proofs.SavitchProofs
open Lax434930.PolynomialTime Polynomial
open MachineCode

def running (s : Word) : Bool := decide (s.length ≠ 2)

def flagCode (c : Code Bool) : Code Bool :=
  .bind c (.append (Test.eq (.length none) (.constant 2)).not.code (.source none))

theorem flagCode_eval (c : Code Bool) (a : Bool → Word) :
    (flagCode c).eval a = running (c.eval a) :: c.eval a := by
  rw [flagCode, eval_bind, eval_append, Test.correct]
  simp [Test.not, Test.eq_value, Number.length, Number.constant, extend, Code.eval, running]

abbrev Keys (c : Code Bool) := Key Bool (flagCode c).emitter.Workspace
abbrev Register := (Unit × Option Bool) × Option Bool

def args (w s : Word) : Bool → Word := fun b => if b then s else w

def configuration (c : Code Bool) (w s : Word) (scratch : Option Bool) : BitStore (Keys c) Unit :=
  store (args w s) [] scratch

def body (c : Code Bool) : BitProgram (Keys c) Unit :=
  .seq (flagCode c).emitter.program
    (.seq (clear (.input true))
      (.seq (transfer .output (.input true)) (read (.input true))))

theorem body_executes (c : Code Bool) (w s : Word) (scratch : Option Bool) (b : ℕ)
    (hw : w.length ≤ b) (hs : s.length ≤ b) :
    ∃ t, t ≤ 4 * (flagCode c).emitter.bound.eval b + 2 * b + 5 ∧
      Executes (body c) (configuration c w s scratch)
        (configuration c w (c.eval (args w s)) (some (running (c.eval (args w s))))) t := by
  let p := (flagCode c).emitter
  let a := args w s
  let out := (flagCode c).eval a
  have ha : ∀ i, (a i).length ≤ b := by intro i; cases i <;> assumption
  obtain ⟨t, ht, hp⟩ := p.executes a [] scratch b ha
  simp only [List.append_nil] at hp
  let mid : BitStore (Keys c) Unit := store a out.reverse none
  change Executes p.program (configuration c w s scratch) mid t at hp
  let cleaned : BitStore (Keys c) Unit :=
    ⟨((), none), Function.update mid.stk (.input true) []⟩
  have hc := clear_store (Key.input true : Keys c) mid
  change Executes (clear (.input true)) mid cleaned (2 * s.length + 2) at hc
  have htr := transfer_store (Key.output : Keys c) (.input true) (by simp) cleaned
  have hout : cleaned.stk .output = out.reverse := by simp [cleaned, mid, store]
  have hempty : cleaned.stk (.input true) = [] := by simp [cleaned]
  rw [hout, hempty, List.reverse_reverse, List.append_nil, List.length_reverse] at htr
  let transferred : BitStore (Keys c) Unit :=
    ⟨((), none), Function.update (Function.update cleaned.stk .output []) (.input true) out⟩
  change Executes (transfer .output (.input true)) cleaned transferred (3 * out.length + 2) at htr
  have hr := Executes.atom (Op.pop (.input true) (fun q : Unit × Option Bool => fun v => (q.1, v))) transferred
  have hend : (Op.pop (.input true) (fun q : Unit × Option Bool => fun v => (q.1, v))).apply transferred =
      configuration c w (c.eval a) (some (running (c.eval a))) := by
    apply Store.ext
    · simp [Op.apply, transferred, out, flagCode_eval, configuration, store]
    · funext k
      cases k with
      | input i => cases i <;>
          simp [Op.apply, transferred, cleaned, mid, store, configuration, args, a, out, flagCode_eval]
      | output => simp [Op.apply, transferred, cleaned, mid, store, configuration]
      | work k => simp [Op.apply, transferred, cleaned, mid, store, configuration]
  rw [hend] at hr
  have hl := p.length_bound a b ha
  refine ⟨t + ((2 * s.length + 2) + ((3 * out.length + 2) + 1)), ?_,
    .seq hp (.seq hc (.seq htr hr))⟩
  change out.length ≤ p.bound.eval b at hl
  dsimp only [p] at ht hl
  omega

def spaceBound (c : Code Bool) (b : ℕ) : ℕ :=
  4 * (flagCode c).emitter.bound.eval b + 3 * b + 6

theorem body_space (c : Code Bool) (w s : Word) (scratch : Option Bool) (b i : ℕ)
    (hw : w.length ≤ b) (hs : s.length ≤ b) (hi : i ≤ w.length + 1) :
    StackLanguage.Exec w (spaceBound c b) (ProgramSpace.compile (body c))
      (ProgramSpace.encode (configuration c w s scratch) i)
      (ProgramSpace.encode (configuration c w (c.eval (args w s))
        (some (running (c.eval (args w s))))) i) := by
  obtain ⟨t, ht, he⟩ := body_executes c w s scratch b hw hs
  apply ProgramSpace.executes_space w (spaceBound c b) i hi he
  intro k
  have hk : ((configuration c w s scratch).stk k).length ≤ b := by
    cases k with
    | input j => cases j <;> assumption
    | output => simp [configuration, store]
    | work k => simp [configuration, store]
  unfold spaceBound
  omega

def machineLoop (c : Code Bool) : StackLanguage.Command (Keys c) Bool Register :=
  .loop (fun q => q.1.2.getD false) (ProgramSpace.compile (body c))

def Transition (c : Code Bool) (w : Word) (b : ℕ) (s t : Word) : Prop :=
  running s = true ∧ c.eval (args w s) = t ∧ s.length ≤ b ∧ t.length ≤ b

theorem loop_space (c : Code Bool) (w : Word) (b i : ℕ)
    (hw : w.length ≤ b) (hi : i ≤ w.length + 1) {s t : Word}
    (h : Relation.ReflTransGen (Transition c w b) s t) (ht : running t = false)
    (hlen : t.length ≤ b) :
    StackLanguage.Exec w (spaceBound c b) (machineLoop c)
      (ProgramSpace.encode (configuration c w s (some (running s))) i)
      (ProgramSpace.encode (configuration c w t (some false)) i) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    rw [ht]
    apply StackLanguage.Exec.loop_false
    · refine ⟨hi, ?_⟩
      intro k
      have hk : ((configuration c w t (some false)).stk k).length ≤ b := by
        cases k with
        | input j => cases j <;> assumption
        | output => simp [configuration, store]
        | work k => simp [configuration, store]
      change ((configuration c w t (some false)).stk k).length < spaceBound c b
      unfold spaceBound
      omega
    · rfl
  | @head s u hsu hut ih =>
    have he := body_space c w s (some (running s)) b i hw hsu.2.2.1 hi
    rw [hsu.2.1] at he
    exact StackLanguage.Exec.loop_true hsu.1 he ih

end

end Lax689614Proofs.CodeStepper
