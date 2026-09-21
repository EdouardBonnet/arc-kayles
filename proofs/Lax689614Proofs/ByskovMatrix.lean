import Lax689614Proofs.ByskovEncoding
import Lax689614Proofs.MatrixBits

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Byskov

theorem mem_take_finRange {r : ℕ} (i : Fin r) (k : ℕ) :
    i ∈ (List.finRange r).take k ↔ i.val < k := by
  constructor
  · intro hi
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hi
    have hh : j < min k r := by simpa using hj
    have hjr : j < r := (lt_min_iff.mp hh).2
    have heq : j = i.val := by
      have := congrArg Fin.val he
      simpa [List.getElem_take, List.getElem_finRange] using this
    have hk : j < k := (lt_min_iff.mp hh).1
    omega
  · intro hi
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val, by simp [hi, i.isLt], ?_⟩
    simp

theorem node_div {r : ℕ} (i : Fin r) (v : Vertex) : (node i v).val / 9 = i.val := by
  have := v.index_lt
  change (9 * i.val + v.index) / 9 = i.val
  omega

theorem node_mod {r : ℕ} (i : Fin r) (v : Vertex) : (node i v).val % 9 = v.index := by
  have := v.index_lt
  change (9 * i.val + v.index) % 9 = v.index
  omega

theorem node_lt {r : ℕ} (i : Fin r) (v : Vertex) : (node i v).val < 9 * r := by
  have := v.index_lt
  have := i.isLt
  change 9 * i.val + v.index < 9 * r
  omega

def priorControl (r k u : ℕ) : Prop :=
  u < 9 * r ∧ u / 9 < k ∧ (u % 9 = 2 ∨ u % 9 = 4)

theorem controls_nat {r : ℕ} (k : ℕ) (u : Fin (9 * r + 1)) :
    u ∈ controls ((List.finRange r).take k) ↔ priorControl r k u.val := by
  by_cases hu : u = dummy r
  · subst u
    have hn : dummy r ∉ controls ((List.finRange r).take k) := by
      intro h
      obtain ⟨i, hi, h⟩ := Finset.mem_biUnion.mp h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact node_ne_dummy i .u h.symm
      · exact node_ne_dummy i .e h.symm
    rw [show priorControl r k (dummy r).val ↔ False by simp [priorControl, dummy]]
    exact iff_false_intro hn
  · obtain ⟨i, v, rfl⟩ := node_of_ne_dummy u hu
    rw [mem_controls, mem_take_finRange]
    simp only [priorControl, node_lt, true_and, node_div, node_mod]
    cases v with
    | x b | y b | yp b => cases b <;> simp [Vertex.index]
    | u | up | e => simp [Vertex.index]

def localIndices (j : ℕ) : Finset ℕ :=
  ((localClauses[j]?).getD ∅).image Vertex.index

theorem localIndices_get (j : Fin 9) (v : Vertex) :
    v.index ∈ localIndices j.val ↔ v ∈ localClauses[j.val]'(by simp [localClauses]) := by
  simp [localIndices, List.getElem?_eq_getElem, show j.val < localClauses.length by
    simpa [localClauses] using j.isLt, Vertex.index_injective.eq_iff]

def localCell (r i j u : ℕ) : Prop :=
  u < 9 * r ∧ u / 9 = i ∧ u % 9 ∈ localIndices j

theorem localCell_correct {r : ℕ} (i : Fin r) (j : Fin 9) (u : Fin (9 * r + 1)) :
    u ∈ (localClauses[j.val]'(by simp [localClauses])).image (node i) ↔
      localCell r i.val j.val u.val := by
  by_cases hu : u = dummy r
  · subst u
    have hn : dummy r ∉ (localClauses[j.val]'(by simp [localClauses])).image (node i) := by
      rintro h
      obtain ⟨v, hv, he⟩ := Finset.mem_image.mp h
      exact node_ne_dummy i v he
    rw [show localCell r i.val j.val (dummy r).val ↔ False by simp [localCell, dummy]]
    exact iff_false_intro hn
  · obtain ⟨k, v, rfl⟩ := node_of_ne_dummy u hu
    simp only [Finset.mem_image, node_eq, localCell, node_lt, true_and, node_div, node_mod,
      localIndices_get]
    constructor
    · rintro ⟨w, hw, hik, hwv⟩
      subst k; subst w
      exact ⟨rfl, hw⟩
    · rintro ⟨hki, hv⟩
      have hki' : k = i := Fin.ext hki
      subst k
      exact ⟨v, hv, rfl, rfl⟩

def literalCell (r : ℕ) (bits : List Bool) (j u : ℕ) : Prop :=
  u < 9 * r ∧ ∃ l : SignedLiteral r, l.node.val = u ∧
    bits[j * (4 * r) + l.index.val]? = some true

theorem literalCell_correct {r : ℕ} (F : SignedCNF r) (j : Fin F.length)
    (u : Fin (9 * r + 1)) :
    u ∈ (F[j]).image SignedLiteral.node ↔
      literalCell r ((matrixFormula F).clauses.flatMap clauseBits) j.val u.val := by
  have hbit (l : SignedLiteral r) :
      ((matrixFormula F).clauses.flatMap clauseBits)[j.val * (4 * r) + l.index.val]? =
        some (decide (l ∈ F[j])) := by
    have h := clausesBits_get (matrixFormula F).clauses
      ⟨j.val, by simpa [matrixFormula] using j.isLt⟩ l.index
    have hinj : Function.Injective (@SignedLiteral.index r) := (literalEquiv r).injective
    simpa [matrixFormula, hinj.eq_iff] using h
  simp only [literalCell, hbit, Option.some.injEq, decide_eq_true_eq, Finset.mem_image]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨node_lt l.round l.vertex, l, rfl, hl⟩
  · rintro ⟨_, l, he, hl⟩
    exact ⟨l, hl, Fin.ext he⟩

end Lax689614Proofs.Byskov
