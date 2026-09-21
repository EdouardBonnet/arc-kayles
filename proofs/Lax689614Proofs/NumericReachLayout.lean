import Lax689614Proofs.NumericReachability

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified.NumericReach

open Lax429075
open Lax434930Proofs.SavitchDefinitions.Reachability

def endpoint (n : ℕ) : ℕ → Bool → VectorFunction n
  | 0, side => fun _ _ => side
  | j + 1, false => readVector n (leftBase n (j * width n))
  | j + 1, true => readVector n (rightBase n (j * width n))

theorem endpoint_before (n j : ℕ) (side : Bool) : ReadsBefore (j * width n) (endpoint n j side) := by
  cases j with
  | zero => intro a b h; rfl
  | succ j =>
    cases side <;> apply readVector_before <;> simp only [leftBase, rightBase, width] <;> nlinarith

theorem forall_lt_succ_front (P : ℕ → Prop) (n : ℕ) :
    (∀ j < n + 1, P j) ↔ P 0 ∧ ∀ j < n, P (j + 1) := by
  constructor
  · intro h; exact ⟨h 0 (by omega), fun j hj => h (j + 1) (by omega)⟩
  · rintro ⟨h0, hs⟩ j hj
    cases j with
    | zero => exact h0
    | succ j => exact hs j (by omega)

theorem condition_unroll (n d j : ℕ) (E : Vector n → Vector n → Prop) (a : CNF.Assignment) :
    condition n E d (j * width n) (endpoint n j false) (endpoint n j true) a ↔
      (∀ i < d, aligned n ((j + i) * width n) (endpoint n (j + i) false) (endpoint n (j + i) true) a) ∧
        (endpoint n (j + d) false a = endpoint n (j + d) true a ∨
          E (endpoint n (j + d) false a) (endpoint n (j + d) true a)) := by
  induction d generalizing j with
  | zero => simp [condition]
  | succ d ih =>
    rw [condition]
    have he : j * width n + width n = (j + 1) * width n := by ring
    rw [he]
    change (aligned n (j * width n) (endpoint n j false) (endpoint n j true) a ∧
      condition n E d ((j + 1) * width n) (endpoint n (j + 1) false) (endpoint n (j + 1) true) a) ↔ _
    rw [ih, forall_lt_succ_front]
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, and_assoc]

def matrixCondition (n d : ℕ) (E : Vector n → Vector n → Prop) (a : CNF.Assignment) : Prop :=
  (∀ i < d, aligned n (i * width n) (endpoint n i false) (endpoint n i true) a) ∧
    (endpoint n d false a = endpoint n d true a ∨ E (endpoint n d false a) (endpoint n d true a))

theorem truth_matrixCondition (n d : ℕ) (E : Vector n → Vector n → Prop) (a : CNF.Assignment) :
    Prefix.Truth (matrixCondition n d E) (reachPrefix n d) 0 a ↔
      Within E (2 ^ d) (fun _ => false) (fun _ => true) := by
  have he (b : CNF.Assignment) : condition n E d 0 (endpoint n 0 false) (endpoint n 0 true) b ↔
      matrixCondition n d E b := by simpa [matrixCondition] using condition_unroll n d 0 E b
  rw [← Prefix.truth_congr _ _ _ he]
  exact truth_condition n d 0 E _ _ (by intro a b h; rfl) (by intro a b h; rfl) a

theorem reachPrefix_count (n d : ℕ) : (reachPrefix n d).count = d * width n := by
  induction d with
  | zero => simp [reachPrefix, Prefix.count_nil]
  | succ d ih =>
    simp only [reachPrefix, roundPrefix, List.cons_append, List.nil_append, Prefix.count_cons, ih]
    unfold width
    ring

end Lax689614Proofs.Quantified.NumericReach
