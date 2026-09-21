import Lax689614Proofs.ParserLengths

namespace Lax689614Proofs

theorem clauseBits_get {n : ℕ} (C : Finset (Fin n)) (i : Fin n) :
    (clauseBits C)[i.val]? = some (decide (i ∈ C)) := by
  simp [clauseBits, List.getElem?_eq_getElem, i.isLt]

theorem clausesBits_get {n : ℕ} (cs : List (Finset (Fin n)))
    (j : Fin cs.length) (i : Fin n) :
    (cs.flatMap clauseBits)[j.val * n + i.val]? = some (decide (i ∈ cs[j])) := by
  induction cs with
  | nil => exact Fin.elim0 j
  | cons C cs ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add, List.flatMap_cons,
        List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [clauseBits_length]; exact i.isLt)]
      exact clauseBits_get C i
    · simp only [Fin.val_succ, List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [clauseBits_length]; nlinarith)]
      rw [clauseBits_length]
      have he : (k.val + 1) * n + i.val - n = k.val * n + i.val := by
        simp only [Nat.add_mul, Nat.one_mul]; omega
      rw [he]
      exact ih k

theorem clausesBits_take_first {n : ℕ} (cs : List (Finset (Fin n))) :
    (cs.flatMap clauseBits).take n = (cs.take 1).flatMap clauseBits := by
  cases cs with
  | nil => simp
  | cons C cs =>
    simp only [List.flatMap_cons, List.take_succ_cons, List.take_zero, List.flatMap_nil,
      List.append_nil]
    simpa only [clauseBits_length] using
      (List.take_left (l₁ := clauseBits C) (l₂ := cs.flatMap clauseBits))

end Lax689614Proofs
