import Lax689614Proofs.ByskovCode

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Byskov

open Lax689614 PositiveCNF
open MachineCode (map_finRange_val)

theorem rawLocalRow_correct {r : ℕ} (i : Fin r) (j : Fin 9) :
    rawLocalRow r i.val j.val = clauseBits
      ((localClauses[j.val]'(by simp [localClauses])).image (node i) ∪
        controls ((List.finRange r).take i.val)) := by
  classical
  rw [rawLocalRow, ← map_finRange_val (9 * r + 1), List.map_map]
  apply List.map_congr_left
  intro u hu
  simp only [Function.comp_apply, clauseBits, Finset.mem_union]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, controls_nat, localCell_correct, or_comm]

theorem rawBaseRow_correct {r : ℕ} (F : SignedCNF r) (j : Fin F.length) :
    rawBaseRow r ((matrixFormula F).clauses.flatMap clauseBits) j.val =
      clauseBits ((F[j]).image SignedLiteral.node ∪ controls (List.finRange r)) := by
  classical
  rw [rawBaseRow, ← map_finRange_val (9 * r + 1), List.map_map]
  change (List.finRange (9 * r + 1)).map _ = (List.finRange (9 * r + 1)).map _
  apply List.map_congr_left
  intro u hu
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq, Finset.mem_union, literalCell_correct]
  have hc := controls_nat r u
  have hc' : u ∈ controls (List.finRange r) ↔ priorControl r r u.val := by
    simpa only [show (List.finRange r).take r = List.finRange r by simp] using hc
  exact or_comm.trans (or_congr Iff.rfl hc'.symm)

theorem dummyRow_correct (r : ℕ) :
    (List.range (9 * r + 1)).map (fun u => decide (u = 9 * r)) = clauseBits {dummy r} := by
  rw [← map_finRange_val (9 * r + 1), List.map_map]
  simp [clauseBits, dummy, Fin.ext_iff]

theorem map_finRange_get {α : Type} (xs : List α) :
    (List.finRange xs.length).map (fun i => xs[i.val]) = xs := by
  apply List.ext_getElem <;> simp

theorem zipIdx_finRange (r : ℕ) :
    (List.finRange r).zipIdx = (List.finRange r).map (fun i => (i, i.val)) := by
  apply List.ext_getElem <;> simp

theorem localRows_correct {r : ℕ} (i : Fin r) :
    (List.range 9).flatMap (rawLocalRow r i.val) =
      localClauses.flatMap (fun C => clauseBits (C.image (node i) ∪
        controls ((List.finRange r).take i.val))) := by
  rw [← map_finRange_val 9, List.flatMap_map]
  have he := map_finRange_get localClauses
  have hlen : localClauses.length = 9 := by simp [localClauses]
  have he' : (List.finRange 9).map
      (fun j => localClauses[j.val]'(by omega)) = localClauses := by
    exact he
  conv_rhs => rw [← he', List.flatMap_map]
  apply congrArg (List.flatMap · (List.finRange 9))
  funext j
  exact rawLocalRow_correct i j

theorem positiveRows_correct {r : ℕ} (F : SignedCNF r) :
    (positiveFormula F).clauses.flatMap clauseBits =
      (List.range (9 * r + 1)).map (fun u => decide (u = 9 * r)) ++
        (List.range r).flatMap (fun i => (List.range 9).flatMap (rawLocalRow r i)) ++
          (List.range F.length).flatMap (rawBaseRow r ((matrixFormula F).clauses.flatMap clauseBits)) := by
  rw [dummyRow_correct]
  have hf := layers_flat (literalClauses F) (List.finRange r) ∅
  simp only [Finset.union_empty, List.map_id'] at hf
  simp only [positiveFormula, List.flatMap_cons]
  rw [hf, flatLayers, List.flatMap_append, List.flatMap_assoc, List.flatMap_map,
    zipIdx_finRange, List.flatMap_map]
  simp only [Finset.union_empty]
  rw [← map_finRange_val r, ← map_finRange_val F.length]
  simp only [List.flatMap_map, Function.comp_def, List.append_assoc]
  congr 1
  apply congrArg₂ List.append
  · apply congrArg (List.flatMap · (List.finRange r))
    funext i
    simpa only [List.flatMap_map] using (localRows_correct i).symm
  · rw [literalClauses, List.flatMap_map]
    conv_lhs => rw [← map_finRange_get F, List.flatMap_map]
    apply congrArg (List.flatMap · (List.finRange F.length))
    funext j
    exact (rawBaseRow_correct F j).symm

theorem positiveWord_correct {r : ℕ} (F : SignedCNF r) :
    positiveWord r F.length ((matrixFormula F).clauses.flatMap clauseBits) =
      Encoding.formulaWord (positiveFormula F) := by
  have he : Encoding.formulaWord (positiveFormula F) =
      List.replicate (positiveFormula F).nvars true ++ [false] ++
        List.replicate (positiveFormula F).clauses.length true ++ [false] ++
          (positiveFormula F).clauses.flatMap clauseBits := by
    simp only [Encoding.formulaWord, List.append_assoc]
    rfl
  rw [he, positiveRows_correct, positiveFormula_clause_count]
  simp only [positiveWord, positiveFormula, List.append_assoc]

end Lax689614Proofs.Byskov
