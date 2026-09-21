import Lax689614Proofs.TransitionWords

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs

open Lax689614 Encoding DepthFirst
open scoped Classical

def MatrixValid (n : ℕ) (bits : List Bool) : Prop :=
  bits.length = n * n ∧ (∀ u : Fin n, bit bits (u.val * n + u.val) = false) ∧
    ∀ u v : Fin n, bit bits (u.val * n + v.val) = bit bits (v.val * n + u.val)

def ValidGraphHeader (w : List Bool) : Prop :=
  inputVars w < w.length ∧ MatrixValid (inputVars w) (afterVars w)

theorem matrix_bit {n : ℕ} (cs : List (Finset (Fin n))) (hlen : cs.length = n)
    (u v : Fin n) : bit (cs.flatMap clauseBits) (u.val * n + v.val) =
      decide (v ∈ matrixRow cs u) := by
  have hu : u.val < cs.length := by simpa [hlen] using u.isLt
  unfold bit
  rw [clausesBits_get cs ⟨u.val, hu⟩ v]
  simp [matrixRow, List.getElem?_eq_getElem, hu]

theorem matrix_valid_iff {n : ℕ} (cs : List (Finset (Fin n))) (hlen : cs.length = n) :
    MatrixValid n (cs.flatMap clauseBits) ↔ GraphRowsValid cs := by
  simp only [MatrixValid, clausesBits_length, hlen, true_and, matrix_bit cs hlen,
    decide_eq_false_iff_not, decide_eq_decide, GraphRowsValid]

theorem graphWord_header (G : Graph) : inputVars (graphWord G) = G.vertices ∧
    afterVars (graphWord G) = (graphRows G).flatMap clauseBits ∧ ValidGraphHeader (graphWord G) := by
  have hn : inputVars (graphWord G) = G.vertices := graphWord_leading G
  have hb : afterVars (graphWord G) = (graphRows G).flatMap clauseBits := by
    unfold afterVars
    rw [hn, graphWord_rows]
    exact drop_unary _ _
  refine ⟨hn, hb, ?_⟩
  unfold ValidGraphHeader
  rw [hn, hb]
  constructor
  · rw [graphWord_rows]; simp
  · exact (matrix_valid_iff _ (graphRows_length G)).mpr (graphRows_valid G)

theorem parseGraph_of_header (w : List Bool) (h : ValidGraphHeader w) :
    ∃ G, parseGraph w = some G := by
  obtain ⟨n, bits, hn⟩ := readUnary_total w h.1
  have hlead := readUnary_leading hn
  have he : inputVars w = n := hlead.1
  have hb : afterVars w = bits := by unfold afterVars; rw [he]; exact hlead.2.1
  have hv : MatrixValid n bits := by simpa only [he, hb] using h.2
  obtain ⟨cs, rest, hc⟩ := readClauses_total n n bits (by have := hv.1; omega)
  have hlen := readClauses_length hc
  have hr : rest = [] := List.length_eq_zero_iff.mp (by have := hv.1; omega)
  subst rest
  have hcs := readClauses_sound hc
  simp only [List.append_nil] at hcs
  have hvalid : GraphRowsValid cs :=
    (matrix_valid_iff cs hcs.1).mp (hcs.2 ▸ hv)
  exact ⟨matrixGraph n cs, by simp [parseGraph, hn, hc, hvalid]⟩

theorem validGraphHeader_iff (w : List Bool) :
    ValidGraphHeader w ↔ ∃ G, parseGraph w = some G := by
  refine ⟨parseGraph_of_header w, ?_⟩
  rintro ⟨G, hG⟩
  rw [← parseGraph_sound hG]
  exact (graphWord_header G).2.2

end Lax689614Proofs
