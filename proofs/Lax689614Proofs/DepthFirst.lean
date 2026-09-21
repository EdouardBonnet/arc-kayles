import Lax689614Proofs.GameEvaluation

namespace Lax689614Proofs.DepthFirst

open Lax689614 ArcKayles

structure Frame (n : ℕ) where
  board : Finset (Fin n)
  todo : List (Fin n × Fin n)
  fuel : ℕ

inductive State (n : ℕ)
  | search (frames : List (Frame n))
  | returning (result : Bool) (frames : List (Frame n))

def State.frames {n : ℕ} : State n → List (Frame n)
  | .search fs => fs
  | .returning _ fs => fs

def State.depth {n : ℕ} (s : State n) : ℕ := s.frames.length

def frameValue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (f : Frame n) : Bool :=
  match f.fuel with
  | 0 => false
  | fuel + 1 => f.todo.any fun e => legalEdge G f.board e && !winEval G (remove f.board e.1 e.2) fuel

inductive Step {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : State n → State n → Prop
  | zero (S es rest) : Step G (.search (⟨S, es, 0⟩ :: rest)) (.returning false rest)
  | exhausted (S fuel rest) : Step G (.search (⟨S, [], fuel + 1⟩ :: rest)) (.returning false rest)
  | skip (S e es fuel rest) (he : legalEdge G S e = false) :
      Step G (.search (⟨S, e :: es, fuel + 1⟩ :: rest)) (.search (⟨S, es, fuel + 1⟩ :: rest))
  | descend (S e es fuel rest) (he : legalEdge G S e = true) :
      Step G (.search (⟨S, e :: es, fuel + 1⟩ :: rest))
        (.search (⟨remove S e.1 e.2, edgeList n, fuel⟩ :: ⟨S, es, fuel + 1⟩ :: rest))
  | childWins (parent rest) : Step G (.returning true (parent :: rest)) (.search (parent :: rest))
  | childLoses (parent rest) : Step G (.returning false (parent :: rest)) (.returning true rest)

def BoundedStep {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (bound : ℕ)
    (s t : State n) : Prop := Step G s t ∧ s.depth ≤ bound ∧ t.depth ≤ bound

abbrev Trace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (bound : ℕ) :=
  Relation.ReflTransGen (BoundedStep G bound)

theorem one_step {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {b : ℕ} {s t : State n} (h : Step G s t) (hs : s.depth ≤ b) (ht : t.depth ≤ b) : Trace G b s t :=
  Relation.ReflTransGen.single ⟨h, hs, ht⟩

theorem evaluate_frame {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (fuel : ℕ) (S : Finset (Fin n)) (es : List (Fin n × Fin n)) (rest : List (Frame n)) :
    Trace G (rest.length + fuel + 1) (.search (⟨S, es, fuel⟩ :: rest))
      (.returning (frameValue G ⟨S, es, fuel⟩) rest) := by
  induction fuel generalizing S es rest with
  | zero =>
    exact one_step (Step.zero S es rest) (by simp [State.depth, State.frames])
      (by simp [State.depth, State.frames])
  | succ fuel ih =>
    induction es with
    | nil =>
      exact one_step (Step.exhausted S fuel rest)
        (by simp [State.depth, State.frames]<;> omega) (by simp [State.depth, State.frames]<;> omega)
    | cons e es ihes =>
      cases he : legalEdge G S e with
      | false =>
        have hfirst : Trace G (rest.length + (fuel + 1) + 1)
            (.search (⟨S, e :: es, fuel + 1⟩ :: rest)) (.search (⟨S, es, fuel + 1⟩ :: rest)) :=
          one_step (Step.skip S e es fuel rest he)
            (by simp [State.depth, State.frames]<;> omega) (by simp [State.depth, State.frames]<;> omega)
        simpa [frameValue, he] using hfirst.trans ihes
      | true =>
        have hfirst : Trace G (rest.length + (fuel + 1) + 1)
            (.search (⟨S, e :: es, fuel + 1⟩ :: rest))
            (.search (⟨remove S e.1 e.2, edgeList n, fuel⟩ :: ⟨S, es, fuel + 1⟩ :: rest)) :=
          one_step (Step.descend S e es fuel rest he)
            (by simp [State.depth, State.frames]<;> omega) (by simp [State.depth, State.frames]<;> omega)
        have hchild := ih (remove S e.1 e.2) (edgeList n) (⟨S, es, fuel + 1⟩ :: rest)
        have hval : frameValue G ⟨remove S e.1 e.2, edgeList n, fuel⟩ =
            winEval G (remove S e.1 e.2) fuel := by cases fuel <;> rfl
        rw [hval] at hchild
        have hbound : (⟨S, es, fuel + 1⟩ :: rest).length + fuel + 1 = rest.length + (fuel + 1) + 1 := by simp<;> omega
        rw [hbound] at hchild
        cases hc : winEval G (remove S e.1 e.2) fuel with
        | false =>
          rw [hc] at hchild
          have hlast : Trace G (rest.length + (fuel + 1) + 1)
              (.returning false (⟨S, es, fuel + 1⟩ :: rest)) (.returning true rest) :=
            one_step (Step.childLoses _ _)
              (by simp [State.depth, State.frames]<;> omega) (by simp [State.depth, State.frames]<;> omega)
          simpa [frameValue, he, hc] using (hfirst.trans hchild).trans hlast
        | true =>
          rw [hc] at hchild
          have hresume : Trace G (rest.length + (fuel + 1) + 1)
              (.returning true (⟨S, es, fuel + 1⟩ :: rest)) (.search (⟨S, es, fuel + 1⟩ :: rest)) :=
            one_step (Step.childWins _ _)
              (by simp [State.depth, State.frames]<;> omega) (by simp [State.depth, State.frames]<;> omega)
          simpa [frameValue, he, hc] using ((hfirst.trans hchild).trans hresume).trans ihes

theorem evaluate_initial {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Trace G (n + 1) (.search [⟨Finset.univ, edgeList n, n⟩])
      (.returning (winEval G Finset.univ n) []) := by
  have h := evaluate_frame G n Finset.univ (edgeList n) []
  have hv : frameValue G ⟨Finset.univ, edgeList n, n⟩ = winEval G Finset.univ n := by cases n <;> rfl
  simpa only [List.length_nil, Nat.zero_add, hv] using h

end Lax689614Proofs.DepthFirst
