import Lax689614Proofs.ParserLengths
import Lax689614Proofs.UnaryCode

namespace Lax689614Proofs

open Lax689614 PositiveCNF

def inputVars (w : List Bool) : ℕ := (w.takeWhile id).length
def afterVars (w : List Bool) : List Bool := w.drop (inputVars w + 1)
def inputClauses (w : List Bool) : ℕ := ((afterVars w).takeWhile id).length
def inputMatrix (w : List Bool) : List Bool := (afterVars w).drop (inputClauses w + 1)

def ValidHeader (w : List Bool) : Prop := inputVars w < w.length ∧
  inputClauses w < (afterVars w).length ∧ (inputMatrix w).length = inputClauses w * inputVars w

theorem header_of_parse {w : List Bool} {φ : Formula} (hp : parseFormula w = some φ) :
    inputVars w = φ.nvars ∧ inputClauses w = φ.clauses.length ∧
    inputMatrix w = φ.clauses.flatMap clauseBits ∧ ValidHeader w := by
  have hw := parseFormula_sound hp
  have hword : w = List.replicate φ.nvars true ++ false ::
      (List.replicate φ.clauses.length true ++ false :: φ.clauses.flatMap clauseBits) := by
    rw [← hw]; simp [Encoding.formulaWord, List.append_assoc]; rfl
  have hn := readUnary_leading (readUnary_prefix φ.nvars
    (List.replicate φ.clauses.length true ++ false :: φ.clauses.flatMap clauseBits))
  have hm := readUnary_leading (readUnary_prefix φ.clauses.length (φ.clauses.flatMap clauseBits))
  have hv : inputVars w = φ.nvars := by rw [hword]; exact hn.1
  have hav : afterVars w = List.replicate φ.clauses.length true ++ false :: φ.clauses.flatMap clauseBits := by
    unfold afterVars; rw [hv, hword]; exact hn.2.1
  have hc : inputClauses w = φ.clauses.length := by unfold inputClauses; rw [hav]; exact hm.1
  have hmat : inputMatrix w = φ.clauses.flatMap clauseBits := by
    unfold inputMatrix; rw [hc, hav]; exact hm.2.1
  refine ⟨hv, hc, hmat, ?_⟩
  unfold ValidHeader
  rw [hv, hc, hmat, clausesBits_length]
  exact ⟨by rw [hword]; exact hn.2.2, by rw [hav]; exact hm.2.2, rfl⟩

theorem parse_of_header (w : List Bool) (h : ValidHeader w) : ∃ φ, parseFormula w = some φ := by
  obtain ⟨n, v, hn⟩ := readUnary_total w h.1
  have hnl := readUnary_leading hn
  have hv : afterVars w = v := by unfold afterVars; rw [show inputVars w = n from hnl.1]; exact hnl.2.1
  have hvm : (v.takeWhile id).length < v.length := by simpa only [inputClauses, hv] using h.2.1
  obtain ⟨m, bits, hm⟩ := readUnary_total v hvm
  have hml := readUnary_leading hm
  have hc : inputClauses w = m := by unfold inputClauses; rw [hv]; exact hml.1
  have hbits : inputMatrix w = bits := by unfold inputMatrix; rw [hc, hv]; exact hml.2.1
  have hlen : bits.length = m * n := by
    have he := h.2.2
    rwa [hbits, hc, show inputVars w = n from hnl.1] at he
  obtain ⟨cs, _, hp⟩ := parseFormula_matrix n m bits hlen
  refine ⟨⟨n, cs⟩, ?_⟩
  rwa [← readUnary_sound hm, ← readUnary_sound hn] at hp

theorem validHeader_iff (w : List Bool) : ValidHeader w ↔ ∃ φ, parseFormula w = some φ :=
  ⟨parse_of_header w, fun ⟨φ, hp⟩ => (header_of_parse hp).2.2.2⟩

end Lax689614Proofs
