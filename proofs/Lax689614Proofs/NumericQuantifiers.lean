import Lax689614Proofs.QuantifiedPositiveCNF

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified

open Lax429075

def Prefix.count (qs : Prefix) : ℕ := (Prefix.expand qs).length

theorem Prefix.count_nil : Prefix.count [] = 0 := rfl

theorem Prefix.count_cons (q : Bool) (k : ℕ) (qs : Prefix) :
    Prefix.count ((q, k) :: qs) = k + Prefix.count qs := Prefix.expand_cons q k qs

def Prefix.Truth (P : CNF.Assignment → Prop) : Prefix → ℕ → CNF.Assignment → Prop
  | [], _, a => P a
  | (q, k) :: qs, start, a =>
      quantify q (fun v : Vector k => Prefix.Truth P qs (start + k) (assignBlock start k v a))

theorem Prefix.truth_congr (qs : Prefix) (start : ℕ) (a : CNF.Assignment)
    {P Q : CNF.Assignment → Prop} (h : ∀ b, P b ↔ Q b) :
    Prefix.Truth P qs start a ↔ Prefix.Truth Q qs start a := by
  induction qs generalizing start a with
  | nil => exact h a
  | cons q qs ih => exact quantify_congr q.1 (fun _ => ih _ _)

theorem Prefix.truth_append (P : CNF.Assignment → Prop) (qs rs : Prefix) (start : ℕ) (a : CNF.Assignment) :
    Prefix.Truth P (qs ++ rs) start a ↔
      Prefix.Truth (fun b => Prefix.Truth P rs (start + qs.count) b) qs start a := by
  induction qs generalizing start a with
  | nil => simp [Prefix.Truth, Prefix.count_nil]
  | cons q qs ih =>
    rcases q with ⟨q, k⟩
    simp only [List.cons_append, Prefix.Truth, Prefix.count_cons]
    apply quantify_congr; intro v
    simpa only [Nat.add_assoc] using ih (start + k) (assignBlock start k v a)

def AgreesBefore (n : ℕ) (a b : CNF.Assignment) : Prop := ∀ i < n, a i = b i

def DependsBefore (n : ℕ) (P : CNF.Assignment → Prop) : Prop :=
  ∀ a b, AgreesBefore n a b → (P a ↔ P b)

theorem DependsBefore.mono {n m : ℕ} {P : CNF.Assignment → Prop}
    (h : DependsBefore n P) (hnm : n ≤ m) : DependsBefore m P := by
  intro a b hab
  exact h a b (fun i hi => hab i (hi.trans_le hnm))

theorem assignBlock_agrees (start k : ℕ) (v : Vector k) (a : CNF.Assignment) :
    AgreesBefore start (assignBlock start k v a) a := assignBlock_before start k v a

theorem Prefix.truth_guard (qs : Prefix) (start : ℕ) (a : CNF.Assignment)
    (G P : CNF.Assignment → Prop) (hG : DependsBefore start G) :
    Prefix.Truth (fun b => G b ∧ P b) qs start a ↔ G a ∧ Prefix.Truth P qs start a := by
  induction qs generalizing start a with
  | nil => rfl
  | cons q qs ih =>
    rcases q with ⟨q, k⟩
    simp only [Prefix.Truth]
    have hstep (v : Vector k) :
        Prefix.Truth (fun b => G b ∧ P b) qs (start + k) (assignBlock start k v a) ↔
          G a ∧ Prefix.Truth P qs (start + k) (assignBlock start k v a) := by
      rw [ih _ _ (hG.mono (Nat.le_add_right _ _)),
        hG _ _ (assignBlock_agrees start k v a)]
    rw [quantify_congr q hstep]
    cases q <;> simp only [quantify, Bool.false_eq_true, Bool.true_eq, ↓reduceIte]
    · exact exists_and_left
    · constructor
      · intro h; exact ⟨(h (fun _ => false)).1, fun v => (h v).2⟩
      · rintro ⟨hg, hp⟩ v; exact ⟨hg, hp v⟩

theorem Prefix.holds_eq_truth (cs : CNF.Formula) (qs : Prefix) (start : ℕ) (a : CNF.Assignment) :
    qs.Holds cs start a ↔ Prefix.Truth (fun b => CNF.eval cs b = true) qs start a := by
  induction qs generalizing start a with
  | nil => rfl
  | cons q qs ih =>
    rcases q with ⟨q, k⟩
    change quantify q _ ↔ quantify q _
    exact quantify_congr q (fun _ => ih _ _)

theorem Prefix.compile_matrix (qs : Prefix) (start : ℕ) (a : CNF.Assignment)
    (e : Lax429075Proofs.CircuitBuilder.Expr) (he : e.Bounded (start + qs.count)) :
    Prefix.Holds (fragmentCNF (start + qs.count) e)
      (qs ++ [(false, (Lax429075Proofs.CircuitBuilder.compile (start + qs.count) e).gates.length)]) start a ↔
      Prefix.Truth (fun b => e.eval b = true) qs start a := by
  rw [Prefix.holds_eq_truth, Prefix.truth_append]
  apply Prefix.truth_congr
  intro b
  change (∃ v, CNF.eval (fragmentCNF (start + qs.count) e)
    (assignBlock (start + qs.count) _ v b) = true) ↔ _
  exact fragmentCNF_exists (start + qs.count) e he b

end Lax689614Proofs.Quantified
