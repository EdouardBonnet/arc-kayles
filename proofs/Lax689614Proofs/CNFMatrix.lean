import Lax689614Proofs.CNFLiteralCode
import Lax689614Proofs.GraphCode

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.CNFTraversal

open Lax429075 CNF Encoding
open Lax434930.PolynomialTime
open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming

def matrixClause (flags : Word) (C : Clause) : Finset (Fin (4 * flags.length)) :=
  ((C.filterMap (Quantified.signedLiteral flags.length (fun i => flags[i.val]))).toFinset).image
    Byskov.SignedLiteral.index

theorem signedLiteral_address (flags : Word) (l : Literal) (h : l.index < flags.length) :
    (Byskov.SignedLiteral.index ⟨⟨l.index, h⟩, !(flags[l.index]), l.positive⟩).val =
      literalAddress flags l := by
  simp only [Byskov.SignedLiteral.index, literalAddress, List.getElem?_eq_getElem h,
    Option.getD_some]
  cases flags[l.index] <;> rfl

theorem matrixClause_mem (flags : Word) (C : Clause) (i : Fin (4 * flags.length)) :
    i ∈ matrixClause flags C ↔
      ∃ l ∈ C, l.index < flags.length ∧ literalAddress flags l = i.val := by
  constructor
  · intro hi
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hi
    obtain ⟨l, hl, heq⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hs)
    unfold Quantified.signedLiteral at heq
    split_ifs at heq with hb
    · simp only [Option.some.injEq] at heq
      subst s
      exact ⟨l, hl, hb, (signedLiteral_address flags l hb).symm.trans (congrArg Fin.val he)⟩
  · rintro ⟨l, hl, hb, he⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨⟨l.index, hb⟩, !(flags[l.index]), l.positive⟩, ?_, ?_⟩
    · apply List.mem_toFinset.mpr
      exact List.mem_filterMap.mpr ⟨l, hl, by simp [Quantified.signedLiteral, hb]⟩
    · apply Fin.ext
      exact (signedLiteral_address flags l hb).trans he

def clauseRowCode {I : Type} (flags word : I) : Code I :=
  Code.loop ((Number.constant 4).mul (.length flags))
    (clauseMatches (some flags) (some word) (.length none)).code

theorem clauseRowCode_eval {I : Type} (flags word : I) (a : I → Word)
    (C : Clause) (tail : Word) (hw : a word = encodeClause C ++ tail) :
    (clauseRowCode flags word).eval a = clauseBits (matrixClause (a flags) C) := by
  rw [clauseRowCode, Code.eval_loop]
  simp only [Test.correct]
  change (List.range (4 * (a flags).length)).flatMap (fun j =>
    [(clauseMatches (some flags) (some word) (.length none)).value
      (extend a (List.replicate j true))]) = _
  have he (i : Fin (4 * (a flags).length)) :
      (clauseMatches (some flags) (some word) (.length none)).value
        (extend a (List.replicate i.val true)) = decide (i ∈ matrixClause (a flags) C) := by
    apply Bool.eq_iff_iff.mpr
    rw [clauseMatches_correct _ _ _ _ C tail (by exact hw), decide_eq_true_eq, matrixClause_mem]
    simp [Number.length, extend]
  rw [← MachineCode.map_finRange_val]
  simp only [List.flatMap_map]
  simp_rw [he]
  exact List.map_eq_flatMap.symm

end Lax689614Proofs.CNFTraversal
