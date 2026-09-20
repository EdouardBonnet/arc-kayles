import Lax689614Proofs.FormulaParser

namespace Lax689614Proofs

open Lax689614 PositiveCNF

theorem clauseBits_length {n : ℕ} (C : Finset (Fin n)) : (clauseBits C).length = n := by
  simp [clauseBits]

theorem clausesBits_length {n : ℕ} (cs : List (Finset (Fin n))) :
    (cs.flatMap clauseBits).length = cs.length * n := by
  induction cs with
  | nil => simp
  | cons C cs ih => simp [ih, clauseBits_length, Nat.add_mul, Nat.add_comm]

theorem readClause_total (n : ℕ) (w : List Bool) (hlen : n ≤ w.length) :
    ∃ C v, readClause n w = some (C, v) := by
  induction n generalizing w with
  | zero => exact ⟨∅, w, rfl⟩
  | succ n ih =>
    cases w with
    | nil => simp at hlen
    | cons b w =>
      obtain ⟨C, v, hCv⟩ := ih w (by simpa using hlen)
      exact ⟨pushBit b C, v, by simp [readClause, hCv]⟩

theorem readClause_length {n : ℕ} {w v : List Bool} {C : Finset (Fin n)}
    (h : readClause n w = some (C, v)) : w.length = n + v.length := by
  rw [readClause_sound h, List.length_append, clauseBits_length]

theorem readClauses_total (n m : ℕ) (w : List Bool) (hlen : m * n ≤ w.length) :
    ∃ cs v, readClauses n m w = some (cs, v) := by
  induction m generalizing w with
  | zero => exact ⟨[], w, rfl⟩
  | succ m ih =>
    obtain ⟨C, v, hCv⟩ := readClause_total n w (by nlinarith)
    have hlenv := readClause_length hCv
    obtain ⟨cs, u, hcs⟩ := ih v (by nlinarith)
    exact ⟨C :: cs, u, by simp [readClauses, hCv, hcs]⟩

theorem readClauses_length {n m : ℕ} {w v : List Bool} {cs : List (Finset (Fin n))}
    (h : readClauses n m w = some (cs, v)) : w.length = m * n + v.length := by
  obtain ⟨hlen, heq⟩ := readClauses_sound h
  rw [heq, List.length_append, clausesBits_length, hlen]

theorem takeWhile_unary_prefix (n : ℕ) (w : List Bool) :
    (List.replicate n true ++ false :: w).takeWhile id = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem readUnary_leading {w : List Bool} {n : ℕ} {v : List Bool}
    (h : readUnary w = some (n, v)) :
    (w.takeWhile id).length = n ∧ w.drop (n + 1) = v ∧ n < w.length := by
  rw [readUnary_sound h, takeWhile_unary_prefix]
  simp [List.drop_append]

theorem readUnary_total (w : List Bool) (h : (w.takeWhile id).length < w.length) :
    ∃ n v, readUnary w = some (n, v) := by
  induction w with
  | nil => simp at h
  | cons b w ih =>
    cases b
    · exact ⟨0, w, rfl⟩
    · have ht : (w.takeWhile id).length < w.length := by simpa using h
      obtain ⟨n, v, hnv⟩ := ih ht
      exact ⟨n + 1, v, by simp [readUnary, hnv]⟩

theorem parseFormula_matrix (n m : ℕ) (bits : List Bool) (hlen : bits.length = m * n) :
    ∃ cs : List (Finset (Fin n)), cs.length = m ∧
      parseFormula (List.replicate n true ++ false ::
        (List.replicate m true ++ false :: bits)) = some ⟨n, cs⟩ := by
  obtain ⟨cs, rest, hcs⟩ := readClauses_total n m bits (by omega)
  have hr := readClauses_length hcs
  have hrest : rest = [] := List.length_eq_zero_iff.mp (by omega)
  subst rest
  refine ⟨cs, (readClauses_sound hcs).1, ?_⟩
  simp [parseFormula, readUnary_prefix, hcs]

end Lax689614Proofs
