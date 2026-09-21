import Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram
import Lax434930Proofs.SavitchProofs.StackLanguage

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.ProgramSpace

open Lax434930.PolynomialTime
open Lax434930Proofs.InclusionAux.TimeCompiler.StackProgram
open Lax434930Proofs.SavitchProofs

variable {K σ : Type} [DecidableEq K]

abbrev StoreB (K σ : Type) := Store (fun _ : K => Bool) σ
abbrev ProgramB (K σ : Type) := Program (fun _ : K => Bool) σ

def encode (s : StoreB K σ) (i : ℕ) : StackLanguage.Data K Bool (σ × Option Bool) :=
  ⟨(s.state, none), i, s.stk⟩

def opCode : Op (fun _ : K => Bool) σ → StackLanguage.Command K Bool (σ × Option Bool)
  | .push k f => .push (fun _ => k) (fun s => f s.1)
  | .pop k f => .pop (fun _ => k) (fun s v => (f s.1 v, none))
  | .load f => .assign (fun s => (f s.1, none))
  | .peek k f => .seq (.pop (fun _ => k) (fun s v => (s.1, v)))
      (.seq (.branch (fun s => s.2.isSome)
        (.push (fun _ => k) (fun s => s.2.getD false)) .skip)
        (.assign (fun s => (f s.1 s.2, none))))

def compile : ProgramB K σ → StackLanguage.Command K Bool (σ × Option Bool)
  | .atom o => opCode o
  | .seq p q => .seq (compile p) (compile q)
  | .branch test p q => .branch (fun s => test s.1) (compile p) (compile q)
  | .loop test p => .loop (fun s => test s.1) (compile p)

theorem executes_length {p : ProgramB K σ} {s t : StoreB K σ} {steps : ℕ}
    (h : Executes p s t steps) (k : K) : (t.stk k).length ≤ (s.stk k).length + steps := by
  induction h with
  | atom o s =>
    cases o with
    | push j f => by_cases hk : k = j <;> simp [Op.apply, hk]
    | pop j f => by_cases hk : k = j <;> simp [Op.apply, hk]; omega
    | peek j f => simp [Op.apply]
    | load f => simp [Op.apply]
  | seq hp hq ihp ihq => omega
  | branch_true ht hp ih => omega
  | branch_false ht hp ih => omega
  | loop_false ht => omega
  | loop_true ht hp hq ihp ihq => omega

theorem peek_exec (w : Word) (bound : ℕ) (s : StoreB K σ) (i : ℕ)
    (k : K) (f : σ → Option Bool → σ) (hi : i ≤ w.length + 1)
    (hs : ∀ k, (s.stk k).length < bound) :
    StackLanguage.Exec w bound (opCode (.peek k f)) (encode s i) (encode ((Op.peek k f).apply s) i) := by
  open StackLanguage in
  have hd : Good w bound (encode s i) := ⟨hi, hs⟩
  let d := StackLanguage.popped (encode s i) k (fun q v => (q.1, v))
  have hpop : StackLanguage.Exec w bound
      (.pop (fun _ => k) (fun q v => (q.1, v))) (encode s i) d := .pop _ _ _ hd
  cases hx : s.stk k with
  | nil =>
    have he : d = encode s i := by
      simp only [d, StackLanguage.popped, encode, hx, List.head?_nil, List.tail_nil]
      congr 1
      funext j
      by_cases hj : j = k <;> simp [Function.update_apply, hj, hx]
    have hb : (d.state.2).isSome = false := by simp [he, encode]
    have hskip : StackLanguage.Exec w bound
        (.branch (fun q => q.2.isSome) (.push (fun _ => k) (fun q => q.2.getD false)) .skip) d d :=
      .branch_false hb (.skip d hpop.good.2)
    have hload := StackLanguage.Exec.assign d (fun q => (f q.1 q.2, none)) hpop.good.2
    have hout : StackLanguage.assigned d (f d.state.1 d.state.2, none) =
        encode ((Op.peek k f).apply s) i := by simp [he, StackLanguage.assigned, encode, Op.apply, hx]
    exact hout ▸ StackLanguage.Exec.seq hpop (StackLanguage.Exec.seq hskip hload)
  | cons b xs =>
    let e := StackLanguage.pushed d k (d.state.2.getD false)
    have he : e = ⟨(s.state, some b), i, s.stk⟩ := by
      simp only [e, d, StackLanguage.pushed, StackLanguage.popped, encode, hx,
        List.head?_cons, List.tail_cons, Option.getD_some]
      congr 1
      funext j
      by_cases hj : j = k <;> simp [Function.update_apply, hj, hx]
    have hegood : StackLanguage.Good w bound e := by rw [he]; exact ⟨hi, hs⟩
    have hpush : StackLanguage.Exec w bound
        (.push (fun _ => k) (fun q => q.2.getD false)) d e := .push _ _ _ hpop.good.2 hegood
    have hb : d.state.2.isSome = true := by simp [d, StackLanguage.popped, encode, hx]
    have hbranch : StackLanguage.Exec w bound
        (.branch (fun q => q.2.isSome) (.push (fun _ => k) (fun q => q.2.getD false)) .skip) d e :=
      .branch_true hb hpush
    have hload := StackLanguage.Exec.assign e (fun q => (f q.1 q.2, none)) hegood
    have hout : StackLanguage.assigned e (f e.state.1 e.state.2, none) =
        encode ((Op.peek k f).apply s) i := by simp [he, StackLanguage.assigned, encode, Op.apply, hx]
    exact hout ▸ StackLanguage.Exec.seq hpop (StackLanguage.Exec.seq hbranch hload)

theorem op_exec (w : Word) (bound : ℕ) (s : StoreB K σ) (i : ℕ)
    (o : Op (fun _ : K => Bool) σ) (hi : i ≤ w.length + 1)
    (hs : ∀ k, (s.stk k).length + 1 < bound) :
    StackLanguage.Exec w bound (opCode o) (encode s i) (encode (o.apply s) i) := by
  have hd : StackLanguage.Good w bound (encode s i) :=
    ⟨hi, fun k => by change (s.stk k).length < bound; have := hs k; omega⟩
  cases o with
  | push k f =>
    have he : StackLanguage.pushed (encode s i) k (f s.state) = encode ((Op.push k f).apply s) i := by
      simp only [StackLanguage.pushed, encode, Op.apply]
      congr 1
      funext j; by_cases hj : j = k <;> simp [Function.update_apply, hj]
    rw [← he]
    apply StackLanguage.Exec.push (encode s i) (fun _ => k) (fun q => f q.1) hd
    refine ⟨hi, ?_⟩
    intro j
    by_cases hj : j = k
    · subst j; simpa [StackLanguage.pushed, encode] using hs k
    · simpa [StackLanguage.pushed, encode, hj] using hd.2 j
  | pop k f =>
    have he : StackLanguage.popped (encode s i) k (fun q v => (f q.1 v, none)) =
        encode ((Op.pop k f).apply s) i := by
      simp only [StackLanguage.popped, encode, Op.apply]
      congr 1
      funext j; by_cases hj : j = k <;> simp [Function.update_apply, hj]
    rw [← he]
    exact StackLanguage.Exec.pop (encode s i) (fun _ => k) (fun q v => (f q.1 v, none)) hd
  | load f => exact StackLanguage.Exec.assign _ _ hd
  | peek k f => exact peek_exec w bound s i k f hi hd.2

theorem executes_space (w : Word) (bound i : ℕ) (hi : i ≤ w.length + 1)
    {p : ProgramB K σ} {s t : StoreB K σ} {steps : ℕ} (h : Executes p s t steps)
    (hs : ∀ k, (s.stk k).length + steps < bound) :
    StackLanguage.Exec w bound (compile p) (encode s i) (encode t i) := by
  induction h with
  | atom o s => exact op_exec w bound s i o hi hs
  | @seq p q s u t a b hp hq ihp ihq =>
    apply StackLanguage.Exec.seq (ihp (fun k => by have := hs k; omega))
    apply ihq
    intro k
    have hl := executes_length hp k
    have hh := hs k
    omega
  | branch_true ht hp ih =>
    exact .branch_true ht (ih (fun k => by have := hs k; omega))
  | branch_false ht hp ih =>
    exact .branch_false ht (ih (fun k => by have := hs k; omega))
  | loop_false ht =>
    exact .loop_false _ _ _ ⟨hi, fun k => by change (_ : List Bool).length < bound; dsimp only [encode]; have := hs k; omega⟩ ht
  | @loop_true p s u t a c test ht hp hq ihp ihq =>
    apply StackLanguage.Exec.loop_true ht (ihp (fun k => by have := hs k; omega))
    apply ihq
    intro k
    have hl := executes_length hp k
    have hh := hs k
    omega

end Lax689614Proofs.ProgramSpace
