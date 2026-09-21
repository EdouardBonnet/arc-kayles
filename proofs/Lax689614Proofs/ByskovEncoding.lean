import Lax689614Proofs.ByskovReduction
import Lax689614Proofs.FormulaHeader
import Lax689614Proofs.Sizes

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Byskov

open Lax689614 PositiveCNF

def SignedLiteral.index {r : ℕ} (l : SignedLiteral r) : Fin (4 * r) :=
  ⟨4 * l.round.val + (if l.existential then 2 else 0) + (if l.positive then 1 else 0), by
    have := l.round.isLt
    split <;> split <;> omega⟩

def indexLiteral (r : ℕ) (i : Fin (4 * r)) : SignedLiteral r :=
  ⟨⟨i.val / 4, by have := i.isLt; omega⟩, decide (2 ≤ i.val % 4), decide (i.val % 2 = 1)⟩

theorem indexLiteral_index {r : ℕ} (l : SignedLiteral r) : indexLiteral r l.index = l := by
  rcases l with ⟨i, k, b⟩
  cases k <;> cases b <;> simp [indexLiteral, SignedLiteral.index, Nat.add_mod, Nat.mul_mod]
  all_goals apply Fin.ext; simp; omega

theorem index_indexLiteral (r : ℕ) (i : Fin (4 * r)) : (indexLiteral r i).index = i := by
  apply Fin.ext
  simp only [SignedLiteral.index, indexLiteral, decide_eq_true_eq]
  have hm := Nat.mod_lt i.val (by omega : 0 < 4)
  have hdiv := Nat.mod_add_div i.val 4
  split <;> split <;> omega

def literalEquiv (r : ℕ) : SignedLiteral r ≃ Fin (4 * r) where
  toFun := SignedLiteral.index
  invFun := indexLiteral r
  left_inv := indexLiteral_index
  right_inv := index_indexLiteral r

def matrixFormula {r : ℕ} (F : SignedCNF r) : Formula :=
  ⟨4 * r, F.map (Finset.image SignedLiteral.index)⟩

def decodeMatrix (r : ℕ) (cs : List (Finset (Fin (4 * r)))) : SignedCNF r :=
  cs.map (Finset.image (indexLiteral r))

theorem decodeMatrix_matrix {r : ℕ} (F : SignedCNF r) :
    decodeMatrix r (matrixFormula F).clauses = F := by
  simp [decodeMatrix, matrixFormula, List.map_map, Function.comp_def, Finset.image_image,
    indexLiteral_index]

theorem matrix_decodeMatrix (r : ℕ) (cs : List (Finset (Fin (4 * r)))) :
    matrixFormula (decodeMatrix r cs) = Formula.mk (4 * r) cs := by
  simp [decodeMatrix, matrixFormula, List.map_map, Function.comp_def, Finset.image_image,
    index_indexLiteral]

def signedWord {r : ℕ} (F : SignedCNF r) : List Bool := Encoding.formulaWord (matrixFormula F)

theorem signedWord_length {r : ℕ} (F : SignedCNF r) :
    (signedWord F).length = 4 * r + F.length + 2 + F.length * (4 * r) := by
  rw [signedWord, formula_length]
  simp only [matrixFormula, List.length_map]
  omega

def controls {r : ℕ} (js : List (Fin r)) : Finset (Fin (9 * r + 1)) :=
  js.toFinset.biUnion fun i => {node i .u, node i .e}

theorem controls_nil {r : ℕ} : controls ([] : List (Fin r)) = ∅ := by simp [controls]

theorem controls_cons {r : ℕ} (i : Fin r) (js : List (Fin r)) :
    controls (i :: js) = {node i .u, node i .e} ∪ controls js := by simp [controls]

theorem controls_append {r : ℕ} (js ks : List (Fin r)) :
    controls (js ++ ks) = controls js ∪ controls ks := by
  ext j
  simp [controls, Finset.mem_biUnion, or_and_right, exists_or]

theorem mem_controls {r : ℕ} (i : Fin r) (v : Vertex) (js : List (Fin r)) :
    node i v ∈ controls js ↔ i ∈ js ∧ (v = .u ∨ v = .e) := by
  simp [controls, Finset.mem_biUnion, node_eq, and_or_left, exists_or, eq_comm]

def flatLayers {r : ℕ} (base : List (Finset (Fin (9 * r + 1))))
    (js : List (Fin r)) (P : Finset (Fin (9 * r + 1))) : List (Finset (Fin (9 * r + 1))) :=
  (js.zipIdx).flatMap (fun ik => localClauses.map
    (fun C => C.image (node ik.1) ∪ (controls (js.take ik.2) ∪ P))) ++
    base.map (fun C => C ∪ (controls js ∪ P))

theorem layers_flat {r : ℕ} (base : List (Finset (Fin (9 * r + 1))))
    (js : List (Fin r)) (P : Finset (Fin (9 * r + 1))) :
    (layers base js).map (fun C => C ∪ P) = flatLayers base js P := by
  induction js generalizing P with
  | nil => simp [layers, flatLayers, controls_nil]
  | cons i js ih =>
    simp only [layers, List.map_append, List.map_map, Function.comp_def]
    have he : (fun C : Finset (Fin (9 * r + 1)) => insert (node i .u) (insert (node i .e) C) ∪ P) =
        (fun C => C ∪ ({node i .u, node i .e} ∪ P)) := by
      funext C; ext j; simp [or_assoc, or_left_comm, or_comm]
    rw [he, ih]
    simp only [flatLayers, List.zipIdx_cons, List.flatMap_cons, List.take_zero,
      controls_nil, Finset.empty_union, List.take_succ_cons, controls_cons]
    rw [List.zipIdx_eq_map_add (i := 1)]
    simp only [List.flatMap_map]
    simp [Nat.add_comm, List.append_assoc, controls_cons, Finset.union_assoc, Finset.union_left_comm]

end Lax689614Proofs.Byskov
