import Lax689614Proofs.QuantifierNormalization
import Lax689614Proofs.ByskovReduction

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified

open Lax429075 Byskov

def selected {r : ℕ} (flags : Fin r → Bool) (a : Byskov.Assignment r) : CNF.Assignment :=
  fun j => if h : j < r then if flags ⟨j, h⟩ then (a ⟨j, h⟩).1 else (a ⟨j, h⟩).2 else false

theorem selected_update {r : ℕ} (flags : Fin r → Bool) (a : Byskov.Assignment r)
    (i : Fin r) (b c : Bool) :
    selected flags (Function.update a i (b, c)) =
      Function.update (selected flags a) i.val (if flags i then b else c) := by
  funext j
  by_cases hj : j = i.val
  · subst j; simp [selected, i.isLt]
  · by_cases hr : j < r
    · have hji : (⟨j, hr⟩ : Fin r) ≠ i := by intro h; exact hj (congrArg Fin.val h)
      simp [selected, hr, Function.update_of_ne hj, Function.update_of_ne hji]
    · simp [selected, hr, Function.update_of_ne hj]

def indexedHolds (cs : CNF.Formula) : List (ℕ × Bool) → CNF.Assignment → Prop
  | [], a => CNF.eval cs a = true
  | (i, q) :: qs, a => quantify q (fun b => indexedHolds cs qs (Function.update a i b))

theorem indexedHolds_zipIdx (cs : CNF.Formula) (qs : List Bool) (start : ℕ) (a : CNF.Assignment) :
    indexedHolds cs ((qs.zipIdx start).map Prod.swap) a ↔ singleHolds cs qs start a := by
  induction qs generalizing start a with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.zipIdx_cons, List.map_cons, Prod.swap, indexedHolds, singleHolds]
    exact quantify_congr q (fun b => ih _ _)

def signedLiteral (r : ℕ) (flags : Fin r → Bool) (l : CNF.Literal) : Option (SignedLiteral r) :=
  if h : l.index < r then some ⟨⟨l.index, h⟩, !(flags ⟨l.index, h⟩), l.positive⟩ else none

def signedFormula (r : ℕ) (flags : Fin r → Bool) (cs : CNF.Formula) : SignedCNF r :=
  cs.map fun C => (C.filterMap (signedLiteral r flags)).toFinset

def CNFBounded (r : ℕ) (cs : CNF.Formula) : Prop :=
  ∀ C ∈ cs, ∀ l ∈ C, l.index < r

theorem signedLiteral_eval {r : ℕ} (flags : Fin r → Bool) (l : CNF.Literal)
    (hl : l.index < r) (a : Byskov.Assignment r) :
    (SignedLiteral.mk ⟨l.index, hl⟩ (!(flags ⟨l.index, hl⟩)) l.positive).value a = true ↔
      l.eval (selected flags a) = true := by
  cases hq : flags ⟨l.index, hl⟩ <;> cases hp : l.positive <;>
    simp [SignedLiteral.value, CNF.Literal.eval, selected, hl, hq, hp]

theorem signedFormula_satisfied {r : ℕ} (flags : Fin r → Bool) (cs : CNF.Formula)
    (hcs : CNFBounded r cs) (a : Byskov.Assignment r) :
    (signedFormula r flags cs).Satisfied a ↔ CNF.eval cs (selected flags a) = true := by
  simp only [SignedCNF.Satisfied, signedFormula, List.forall_mem_map, CNF.eval, List.all_eq_true]
  apply forall_congr'; intro C
  apply forall_congr'; intro hC
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨l, hl, hv⟩
    obtain ⟨k, hk, he⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp hl)
    have hb := hcs C hC k hk
    simp only [signedLiteral, dif_pos hb, Option.some.injEq] at he
    subst l
    exact ⟨k, hk, (signedLiteral_eval flags k hb a).mp hv⟩
  · rintro ⟨l, hl, hv⟩
    have hb := hcs C hC l hl
    refine ⟨⟨⟨l.index, hb⟩, !(flags ⟨l.index, hb⟩), l.positive⟩, ?_,
      (signedLiteral_eval flags l hb a).mpr hv⟩
    apply List.mem_toFinset.mpr
    exact List.mem_filterMap.mpr ⟨l, hl, by simp [signedLiteral, hb]⟩

theorem signedFormula_truthFrom {r : ℕ} (flags : Fin r → Bool) (cs : CNF.Formula)
    (hcs : CNFBounded r cs) (js : List (Fin r)) (a : Byskov.Assignment r) :
    (signedFormula r flags cs).TruthFrom js a ↔
      indexedHolds cs (js.map fun i => (i.val, flags i)) (selected flags a) := by
  induction js generalizing a with
  | nil => exact signedFormula_satisfied flags cs hcs a
  | cons i js ih =>
    simp only [SignedCNF.TruthFrom, List.map_cons, indexedHolds]
    simp_rw [ih, selected_update]
    cases hq : flags i <;> simp [quantify, hq]

theorem finRange_zipIdx (qs : List Bool) :
    (List.finRange qs.length).map (fun i => (i.val, qs[i.val])) =
      (qs.zipIdx 0).map Prod.swap := by
  apply List.ext_getElem
  · simp
  · intro j hj hk
    simp at hj
    simp [List.getElem_finRange, List.getElem_zipIdx, hj]

/-- One universal/existential pair per original variable suffices. The unused
    member of each pair is a dummy and does not occur in the translated matrix. -/
theorem signedFormula_correct (qs : List Bool) (cs : CNF.Formula)
    (hcs : CNFBounded qs.length cs) :
    (signedFormula qs.length (fun i => qs[i.val]) cs).True ↔
      singleHolds cs qs 0 (fun _ => false) := by
  rw [SignedCNF.True, signedFormula_truthFrom _ _ hcs, finRange_zipIdx,
    indexedHolds_zipIdx]
  have he : selected (fun i : Fin qs.length => qs[i.val]) (fun _ => (false, false)) =
      (fun _ => false) := by
    funext j; simp [selected]
  rw [he]

theorem blockCNF_positive_correct (qs : Prefix) (cs : CNF.Formula)
    (hcs : CNFBounded (Prefix.expand qs).length cs) :
    Lax689614.PositiveCNF.FirstWins (positiveFormula
      (signedFormula (Prefix.expand qs).length (fun i => (Prefix.expand qs)[i.val]) cs)) ↔
      qs.Holds cs 0 (fun _ => false) := by
  rw [positiveFormula_correct, signedFormula_correct _ _ hcs, Prefix.expand_correct]

end Lax689614Proofs.Quantified
