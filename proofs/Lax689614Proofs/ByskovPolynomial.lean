import Lax689614Proofs.ByskovWord
import Lax689614Proofs.WordReduction

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Byskov

open Lax689614 PositiveCNF
open Lax434930.PolynomialTime
open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open MachineCode

def signedLanguage : Language :=
  {w | ∃ r, ∃ F : SignedCNF r, signedWord F = w ∧ F.True}

theorem matrixFormula_injective (r : ℕ) : Function.Injective (@matrixFormula r) := by
  intro F G he
  have hc : (matrixFormula F).clauses = (matrixFormula G).clauses := by
    simpa only [matrixFormula, Formula.mk.injEq, heq_eq_eq, true_and] using he
  have hd := congrArg (decodeMatrix r) hc
  simpa only [decodeMatrix_matrix] using hd

theorem signedWord_mem {r : ℕ} (F : SignedCNF r) : signedWord F ∈ signedLanguage ↔ F.True := by
  constructor
  · rintro ⟨s, G, he, hG⟩
    have hm : matrixFormula G = matrixFormula F := formulaWord_injective he
    have hn := congrArg Formula.nvars hm
    have hsr : s = r := by change 4 * s = 4 * r at hn; omega
    subst s
    have hGF := matrixFormula_injective r hm
    subst G
    exact hG
  · intro hF; exact ⟨r, F, rfl, hF⟩

theorem matrixFormula_surjective (φ : Formula) (hn : φ.nvars % 4 = 0) :
    ∃ r, ∃ F : SignedCNF r, matrixFormula F = φ := by
  rcases φ with ⟨n, cs⟩
  obtain ⟨r, hr⟩ := Nat.dvd_of_mod_eq_zero hn
  dsimp only at hr
  subst n
  exact ⟨r, decodeMatrix r cs, matrix_decodeMatrix r cs⟩

def losingFormula : Formula := ⟨0, [∅]⟩

theorem losingFormula_loses : ¬ FirstWins losingFormula := by
  simp only [FirstWins, losingFormula, Finset.univ_eq_empty]
  rw [cnf_empty]
  simp [Satisfied]

def signedHeader (w : Word) : Prop := ValidHeader w ∧ inputVars w % 4 = 0

def signedHeaderTest : Test HeaderContext :=
  (validTest (.length nIndex) (.length mIndex) wordIndex tailIndex none).and
    (Test.eq ((Number.length nIndex).mod (.constant 4)) (.constant 0))

theorem signedHeaderTest_value (w : Word) :
    signedHeaderTest.value (headerEnv w) = true ↔ signedHeader w := by
  simp only [signedHeaderTest, Test.and, Bool.and_eq_true]
  rw [validTest_header]
  simp only [Test.eq_value, decide_eq_true_eq, Number.mod, Number.constant, Number.length,
    headerEnv, nIndex, extend, Option.elim_some, Option.elim_none, List.length_replicate,
    signedHeader]

noncomputable def signedReductionBody : Code HeaderContext :=
  Code.when signedHeaderTest
    (positiveCode ((Number.length nIndex).div (.constant 4)) (.length mIndex) none)
    (.literal (Encoding.formulaWord losingFormula))

noncomputable def signedReductionCode : Code Unit := withHeader signedReductionBody

noncomputable def signedReduction (w : Word) : Word := signedReductionCode.eval (fun _ => w)

theorem signedReduction_word {r : ℕ} (F : SignedCNF r) :
    signedReduction (signedWord F) = Encoding.formulaWord (positiveFormula F) := by
  have hp := parseFormula_word (matrixFormula F)
  obtain ⟨hn, hm, hb, hv⟩ := header_of_parse hp
  change inputVars (signedWord F) = 4 * r at hn
  change inputClauses (signedWord F) = (matrixFormula F).clauses.length at hm
  have hs : signedHeader (signedWord F) := ⟨hv, by rw [hn]; omega⟩
  rw [signedReduction, signedReductionCode, withHeader_eval, signedReductionBody,
    Code.eval_when, (signedHeaderTest_value _).mpr hs]
  simp only [↓reduceIte, positiveCode_eval]
  have hnr : ((Number.length nIndex).div (.constant 4)).value (headerEnv (signedWord F)) = r := by
    simp only [Number.div, Number.length, Number.constant, headerEnv, nIndex, extend,
      Option.elim_some, Option.elim_none, List.length_replicate]
    rw [hn]; omega
  have hmr : (Number.length mIndex).value (headerEnv (signedWord F)) = F.length := by
    simpa only [Number.length, headerEnv, mIndex, extend, Option.elim_some, Option.elim_none,
      List.length_replicate, matrixFormula, List.length_map] using hm
  have hbr : headerEnv (signedWord F) none = (matrixFormula F).clauses.flatMap clauseBits := hb
  rw [hnr, hmr, hbr, positiveWord_correct]

theorem signedHeader_iff (w : Word) : signedHeader w ↔ ∃ r, ∃ F : SignedCNF r, signedWord F = w := by
  constructor
  · rintro ⟨hv, hn⟩
    obtain ⟨φ, hp⟩ := parse_of_header w hv
    have hv := (header_of_parse hp).1
    rw [hv] at hn
    obtain ⟨r, F, rfl⟩ := matrixFormula_surjective φ hn
    exact ⟨r, F, parseFormula_sound hp⟩
  · rintro ⟨r, F, rfl⟩
    obtain ⟨hn, _, _, hv⟩ := header_of_parse (parseFormula_word (matrixFormula F))
    refine ⟨hv, ?_⟩
    change inputVars (Encoding.formulaWord (matrixFormula F)) % 4 = 0
    rw [hn]
    change (4 * r) % 4 = 0
    omega

theorem signedReduction_correct (w : Word) :
    w ∈ signedLanguage ↔ signedReduction w ∈ Encoding.positiveCNF := by
  by_cases hv : signedHeader w
  · obtain ⟨r, F, rfl⟩ := (signedHeader_iff w).mp hv
    rw [signedReduction_word, formulaWord_mem, positiveFormula_correct, signedWord_mem]
  · have hs : signedHeaderTest.value (headerEnv w) = false := by
      apply Bool.eq_false_iff.mpr
      intro ht; exact hv ((signedHeaderTest_value w).mp ht)
    have hn : w ∉ signedLanguage := by
      rintro ⟨r, F, he, _⟩
      exact hv ((signedHeader_iff w).mpr ⟨r, F, he⟩)
    rw [signedReduction, signedReductionCode, withHeader_eval, signedReductionBody,
      Code.eval_when, hs]
    simp only [Bool.false_eq_true, ↓reduceIte, Code.eval]
    simp [hn, formulaWord_mem, losingFormula_loses]

theorem signedReduction_polynomial :
    Lax429075.Reductions.ManyOne signedLanguage Encoding.positiveCNF :=
  ⟨signedReduction, code_polynomial_time signedReductionCode, signedReduction_correct⟩

end Lax689614Proofs.Byskov
