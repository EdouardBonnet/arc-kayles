import Lax689614Proofs.GraphValidationCode
import Lax689614Proofs.CodeStepper

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.DepthFirst

open Lax689614 Encoding MachineCode CodeStepper Polynomial
open Lax434930.PolynomialTime
open scoped Classical

noncomputable def stateBound : Polynomial ℕ := (X + C 2) ^ 3 + C 2 * X + C 2

theorem stateBound_eval (n : ℕ) : stateBound.eval n = (n + 2) ^ 3 + 2 * n + 2 := by
  simp [stateBound]

theorem stateBound_input (n : ℕ) : 2 * n + 2 ≤ stateBound.eval n := by
  rw [stateBound_eval]; omega

theorem stateBound_stack (n l : ℕ) (hn : n ≤ l) :
    (n + 1) * (n * n + 2 * n + 2) + 2 ≤ stateBound.eval l := by
  have hm := Nat.pow_le_pow_left hn 3
  have hm2 := Nat.pow_le_pow_left hn 2
  rw [stateBound_eval]
  nlinarith

theorem stateWord_ne_nil {n : ℕ} (s : State n) : stateWord s ≠ [] := by
  cases s <;> simp [stateWord]

theorem step_running {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {s t : State n} (h : Step G s t) : running (stateWord s) = true := by
  cases h <;> simp only [running, stateWord, List.length_append, List.length_cons,
    List.length_nil, decide_eq_true_eq, List.flatMap_cons, List.length_append, frameWord_length] <;> omega

theorem driver_trace (G : Graph) {s t : State G.vertices}
    (h : Trace G.graph (G.vertices + 1) s t) (hs : s.Good) :
    Relation.ReflTransGen (Transition driverCode (graphWord G) (stateBound.eval (graphWord G).length))
      (stateWord s) (stateWord t) := by
  have hn : G.vertices ≤ (graphWord G).length := by
    have hp := (graphWord_header G).2.2.1
    rw [(graphWord_header G).1] at hp
    omega
  have hb := stateBound_stack G.vertices (graphWord G).length hn
  induction h with
  | refl => exact .refl
  | @tail t u ht htu ih =>
    have hgood := trace_good ht hs
    apply ih.tail
    refine ⟨step_running htu.1, ?_, ?_, ?_⟩
    · rw [show args (graphWord G) (stateWord t) = (fun b => if b then stateWord t else graphWord G) from rfl,
        driverCode_next _ _ (stateWord_ne_nil t)]
      exact nextWord_step G htu.1 hgood
    · exact (stateWord_length_bound t hgood htu.2.1).trans hb
    · exact (stateWord_length_bound u (step_good htu.1 hgood) htu.2.2).trans hb

theorem driver_decides (w : Word) : ∃ b : Bool,
    Relation.ReflTransGen (Transition driverCode w (stateBound.eval w.length)) [] [true, b] ∧
    (b = true ↔ w ∈ arcKayles) := by
  have hbound := stateBound_input w.length
  cases hp : parseGraph w with
  | none =>
    refine ⟨false, Relation.ReflTransGen.single ?_, ?_⟩
    · refine ⟨by decide, ?_, by simp, by simp; omega⟩
      change driverCode.eval (fun b => if b then [] else w) = _
      rw [driverCode_initial, initialWord_invalid hp]
    · have hc := decideArcKayles_correct w
      simpa [decideArcKayles, hp] using hc
  | some G =>
    have he := parseGraph_sound hp
    subst w
    let start : State G.vertices := .search [⟨Finset.univ, edgeList G.vertices, G.vertices⟩]
    have hlen : (stateWord start).length ≤ stateBound.eval (graphWord G).length := by
      have hn : G.vertices ≤ (graphWord G).length := by
        have hh := (graphWord_header G).2.2.1
        rw [(graphWord_header G).1] at hh
        omega
      exact (stateWord_length_bound start (initial_good G.vertices)
        (by simp [start, State.depth, State.frames])).trans (stateBound_stack _ _ hn)
    have hinit : Transition driverCode (graphWord G) (stateBound.eval (graphWord G).length) [] (stateWord start) := by
      refine ⟨by decide, ?_, by simp, hlen⟩
      change driverCode.eval (fun b => if b then [] else graphWord G) = _
      rw [driverCode_initial, initialWord_graph]
    have hdfs := driver_trace G (evaluate_initial G.graph) (initial_good G.vertices)
    refine ⟨winEval G.graph Finset.univ G.vertices, (Relation.ReflTransGen.single hinit).trans hdfs, ?_⟩
    rw [winEval_correct _ _ _ (by simp), graphWord_mem]

end Lax689614Proofs.DepthFirst
