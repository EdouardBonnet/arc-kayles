import Lax689614Proofs.Normalization

namespace Lax689614Proofs

open Lax689614 PositiveCNF

def readUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: w => some (0, w)
  | true :: w => (readUnary w).map fun p => (p.1 + 1, p.2)

theorem readUnary_prefix (n : ℕ) (w : List Bool) :
    readUnary (List.replicate n true ++ false :: w) = some (n, w) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, readUnary] using congrArg (Option.map (fun p : ℕ × List Bool => (p.1 + 1, p.2))) ih

theorem readUnary_sound {w : List Bool} {n : ℕ} {v : List Bool}
    (h : readUnary w = some (n, v)) : w = List.replicate n true ++ false :: v := by
  induction w generalizing n v with
  | nil => simp [readUnary] at h
  | cons b w ih =>
    cases b
    · simp only [readUnary, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; rfl
    · simp only [readUnary, Option.map_eq_some_iff] at h
      obtain ⟨⟨k, u⟩, hk, hku⟩ := h
      cases hku
      rw [ih hk]
      simp [List.replicate_succ]

def pushBit {n : ℕ} (b : Bool) (C : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  if b then insert 0 (C.image Fin.succ) else C.image Fin.succ

def tailClause {n : ℕ} (C : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.succ ∈ C

def clauseBits {n : ℕ} (C : Finset (Fin n)) : List Bool :=
  (List.finRange n).map fun i => decide (i ∈ C)

theorem pushBit_reconstruct {n : ℕ} (C : Finset (Fin (n + 1))) :
    pushBit (decide (0 ∈ C)) (tailClause C) = C := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · by_cases h0 : 0 ∈ C <;> simp [pushBit, tailClause, h0]
  · by_cases h0 : 0 ∈ C <;> simp [pushBit, tailClause, h0]

theorem clauseBits_push {n : ℕ} (b : Bool) (C : Finset (Fin n)) :
    clauseBits (pushBit b C) = b :: clauseBits C := by
  cases b <;> simp [clauseBits, List.finRange_succ, pushBit,
    Fin.succ_ne_zero, List.map_map, Function.comp_def]

def readClause : (n : ℕ) → List Bool → Option (Finset (Fin n) × List Bool)
  | 0, w => some (∅, w)
  | _ + 1, [] => none
  | n + 1, b :: w => (readClause n w).map fun p => (pushBit b p.1, p.2)

theorem readClause_prefix {n : ℕ} (C : Finset (Fin n)) (w : List Bool) :
    readClause n (clauseBits C ++ w) = some (C, w) := by
  induction n with
  | zero => have hC : C = ∅ := Subsingleton.elim _ _; subst C; rfl
  | succ n ih =>
    rw [← pushBit_reconstruct C, clauseBits_push, List.cons_append, readClause]
    rw [ih]
    rfl

theorem readClause_sound {n : ℕ} {w v : List Bool} {C : Finset (Fin n)}
    (h : readClause n w = some (C, v)) : w = clauseBits C ++ v := by
  induction n generalizing w v with
  | zero =>
    simp only [readClause, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | succ n ih =>
    cases w with
    | nil => simp [readClause] at h
    | cons b w =>
      simp only [readClause, Option.map_eq_some_iff] at h
      obtain ⟨⟨D, u⟩, hD, hDu⟩ := h
      cases hDu
      rw [ih hD, clauseBits_push, List.cons_append]

def readClauses (n : ℕ) : ℕ → List Bool → Option (List (Finset (Fin n)) × List Bool)
  | 0, w => some ([], w)
  | m + 1, w => do
      let (C, v) ← readClause n w
      let (cs, u) ← readClauses n m v
      pure (C :: cs, u)

theorem readClauses_prefix {n : ℕ} (cs : List (Finset (Fin n))) (w : List Bool) :
    readClauses n cs.length (cs.flatMap clauseBits ++ w) = some (cs, w) := by
  induction cs with
  | nil => rfl
  | cons C cs ih =>
    simp [List.length_cons, List.flatMap_cons, List.append_assoc, readClauses,
      readClause_prefix, ih]

theorem readClauses_sound {n m : ℕ} {w v : List Bool} {cs : List (Finset (Fin n))}
    (h : readClauses n m w = some (cs, v)) :
    cs.length = m ∧ w = cs.flatMap clauseBits ++ v := by
  induction m generalizing w v cs with
  | zero =>
    simp only [readClauses, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | succ m ih =>
    simp only [readClauses, bind, Option.bind_eq_some_iff, pure] at h
    obtain ⟨⟨C, u⟩, hC, ⟨⟨ds, t⟩, hds, hout⟩⟩ := h
    cases hout
    obtain ⟨hlen, heq⟩ := ih hds
    dsimp only at heq ⊢
    exact ⟨by simp [hlen], by rw [readClause_sound hC, heq]; simp [List.append_assoc]⟩

def parseFormula (w : List Bool) : Option Formula := do
  let (n, v) ← readUnary w
  let (m, u) ← readUnary v
  let (cs, rest) ← readClauses n m u
  if rest = [] then some ⟨n, cs⟩ else none

theorem parseFormula_word (φ : Formula) : parseFormula (Encoding.formulaWord φ) = some φ := by
  cases φ with
  | mk n cs =>
    have hcs : readClauses n cs.length (cs.flatMap clauseBits) = some (cs, []) := by
      simpa using readClauses_prefix cs []
    simp [parseFormula, Encoding.formulaWord, List.append_assoc, readUnary_prefix]
    change ((readClauses n cs.length (cs.flatMap clauseBits)).bind
      (fun p => if p.2 = [] then some (Formula.mk n p.1) else none)) = some (Formula.mk n cs)
    rw [hcs]; rfl

theorem parseFormula_sound {w : List Bool} {φ : Formula} (h : parseFormula w = some φ) :
    Encoding.formulaWord φ = w := by
  simp only [parseFormula, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨n, v⟩, hn, ⟨⟨m, u⟩, hm, ⟨⟨cs, rest⟩, hcs, hout⟩⟩⟩ := h
  dsimp only at hm hcs hout
  split_ifs at hout with hr
  · subst rest
    cases hout
    obtain ⟨hlen, heq⟩ := readClauses_sound hcs
    rw [readUnary_sound hn, readUnary_sound hm, heq]
    simp [Encoding.formulaWord, ← hlen, clauseBits, List.append_assoc]
    rfl

theorem formulaWord_injective : Function.Injective Encoding.formulaWord := by
  intro φ ψ he
  have h := congrArg parseFormula he
  simpa only [parseFormula_word, Option.some.injEq] using h

end Lax689614Proofs
