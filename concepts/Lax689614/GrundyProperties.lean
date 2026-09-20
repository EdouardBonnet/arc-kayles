import Lax689614.Grundy
import Mathlib.Data.Nat.Bitwise

/-!
---
title: Basic properties of Sprague–Grundy values
type: theorem
---
Observation 2 and Lemma 3: every smaller value is reachable, the current
value is not reachable, and a position is losing exactly when its value is
zero. Lemma 4: on a disjoint union, the value is the bitwise exclusive-or
of the component values. The binary formula gives the finite-family formula
by iteration.
-/

namespace Lax689614.GrundyProperties

open ArcKayles Grundy

axiom smaller_reachable {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (i : ℕ) (h : i < value G S) :
    ∃ u ∈ S, ∃ v ∈ S, G.Adj u v ∧ value G (remove S u v) = i

axiom value_not_reachable {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (u v : V) (hu : u ∈ S) (hv : v ∈ S) (he : G.Adj u v) :
    value G (remove S u v) ≠ value G S

axiom losing_iff_zero {V : Type} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    ¬ Winning G S ↔ value G S = 0

axiom disjoint_union {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S T : Finset V) (hd : Disjoint S T)
    (hn : ∀ u ∈ S, ∀ v ∈ T, ¬ G.Adj u v) :
    value G (S ∪ T) = Nat.xor (value G S) (value G T)

end Lax689614.GrundyProperties
