import Lax689614.Construction
import Lax689614.Grundy

/-!
---
title: Assignment moves, pass moves, and deviations
type: theorem
---
An assignment move is $v_it_i$ or $v_if_i$ with $i<n$. A pass move is
$v_it_i$ with $n\leq i<R$, or $y_iz_i$. A regular position is reachable
from the initial graph by such moves. Write $r$ and $k$ for the numbers
of surviving $v_i$ and $y_i$, respectively.

Claim 7: when $m$ is odd, $r\geq m$, and $k\geq1$, any other move
loses unless it is $sa_j$ and all literal vertices of clause $j$ are gone.
Claim 8: at a regular position with $r\geq m$, such an exceptional move
wins exactly when $r+k$ is even.
-/

namespace Lax689614.RegularPlay

open PositiveCNF Construction ArcKayles

def SameEdge (u w x z : ℕ) : Prop := (u = x ∧ w = z) ∨ (u = z ∧ w = x)

def RegularMove (φ : Formula) (u w : ℕ) : Prop :=
  (∃ i < R φ, SameEdge u w (v φ i) (vt φ i)) ∨
  (∃ i < φ.nvars, SameEdge u w (v φ i) (f φ i)) ∨
  (∃ i < K φ, SameEdge u w (y φ i) (z φ i))

inductive Reachable (φ : Formula) : Finset ℕ → Prop
  | initial : Reachable φ (board φ)
  | step {S : Finset ℕ} {u w : ℕ} : Reachable φ S →
      u ∈ S → w ∈ S → (graph φ).Adj u w → RegularMove φ u w →
      Reachable φ (remove S u w)

def remainingV (φ : Formula) (S : Finset ℕ) : ℕ :=
  ((Finset.range (R φ)).filter fun i => v φ i ∈ S).card

def remainingY (φ : Formula) (S : Finset ℕ) : ℕ :=
  ((Finset.range (K φ)).filter fun i => y φ i ∈ S).card

def Exhausted (φ : Formula) (S : Finset ℕ) (j : Fin φ.clauses.length) : Prop :=
  ∀ i ∈ φ.clauses[j], f φ i ∉ S

def Exceptional (φ : Formula) (S : Finset ℕ) (u w : ℕ) : Prop :=
  ∃ j : Fin φ.clauses.length, SameEdge u w s (a φ j) ∧ Exhausted φ S j

axiom deviation_loses (φ : Formula) (hm : φ.clauses.length % 2 = 1)
    (S : Finset ℕ) (hS : Reachable φ S)
    (hr : φ.clauses.length ≤ remainingV φ S) (hk : 1 ≤ remainingY φ S)
    (u w : ℕ) (hu : u ∈ S) (hw : w ∈ S) (he : (graph φ).Adj u w)
    (hn : ¬ RegularMove φ u w) (hx : ¬ Exceptional φ S u w) :
    Winning (graph φ) (remove S u w)

axiom exceptional_parity (φ : Formula) (hm : φ.clauses.length % 2 = 1)
    (S : Finset ℕ) (hS : Reachable φ S)
    (hr : φ.clauses.length ≤ remainingV φ S)
    (j : Fin φ.clauses.length) (hj : Exhausted φ S j) :
    ¬ Winning (graph φ) (remove S s (a φ j)) ↔
      (remainingV φ S + remainingY φ S) % 2 = 0

end Lax689614.RegularPlay
