import Lax689614Proofs.Deviations
import Lax689614Proofs.PositiveCNF

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles

@[simp] theorem varIndex_inj {φ : Formula} (i j : Fin φ.nvars) :
    varIndex i = varIndex j ↔ i = j := by simp [varIndex, Fin.ext_iff]

def pending {φ : Formula} (S : Finset (Vertex φ)) : Finset (Fin φ.nvars) :=
  Finset.univ.filter fun i => Vertex.v (varIndex i) ∈ S

def trueVars {φ : Formula} (S : Finset (Vertex φ)) : Finset (Fin φ.nvars) :=
  Finset.univ.filter fun i => Vertex.v (varIndex i) ∉ S ∧ Vertex.f i ∈ S

theorem pending_true_disjoint {φ : Formula} (S : Finset (Vertex φ)) :
    Disjoint (pending S) (trueVars S) := by
  apply Finset.disjoint_left.mpr
  intro i hi ht
  exact (Finset.mem_filter.mp ht).2.1 (Finset.mem_filter.mp hi).2

theorem regular_vf {φ : Formula} (S : Finset (Vertex φ)) (h : VertexReachable φ S) :
    ∀ i, Vertex.v (varIndex i) ∈ S → Vertex.f i ∈ S := by
  induction h with
  | initial => simp
  | @step S u w h hu hw he hr ih =>
    rcases hr with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩ <;>
      rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals
      intro i hi
      have hiS := remove_subset S _ _ hi
      have hf := ih i hiS
      simp_all [remove, varIndex, Fin.ext_iff]

theorem pending_true_move {φ : Formula} (S : Finset (Vertex φ)) (i : Fin φ.nvars) :
    pending (remove S (.v (varIndex i)) (.vt (varIndex i))) = (pending S).erase i := by
  ext j
  simp [pending, remove]

theorem trueVars_true_move {φ : Formula} (S : Finset (Vertex φ)) (i : Fin φ.nvars)
    (hf : Vertex.f i ∈ S) :
    trueVars (remove S (.v (varIndex i)) (.vt (varIndex i))) = insert i (trueVars S) := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [trueVars, remove, hf]
  · simp [trueVars, remove, hj]

theorem pending_false_move {φ : Formula} (S : Finset (Vertex φ)) (i : Fin φ.nvars) :
    pending (remove S (.v (varIndex i)) (.f i)) = (pending S).erase i := by
  ext j
  simp [pending, remove]

theorem trueVars_false_move {φ : Formula} (S : Finset (Vertex φ)) (i : Fin φ.nvars)
    (hv : Vertex.v (varIndex i) ∈ S) :
    trueVars (remove S (.v (varIndex i)) (.f i)) = trueVars S := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [trueVars, remove, hv]
  · simp [trueVars, remove, hj]

theorem pending_reserve_move {φ : Formula} (S : Finset (Vertex φ))
    (i : Fin (Construction.R φ)) (hi : φ.nvars ≤ i.val) :
    pending (remove S (.v i) (.vt i)) = pending S := by
  ext j
  have hji : varIndex j ≠ i := by
    intro hh
    have he := congrArg Fin.val hh
    have := j.isLt
    simp only [varIndex] at he
    omega
  simp [pending, remove, hji]

theorem trueVars_reserve_move {φ : Formula} (S : Finset (Vertex φ))
    (i : Fin (Construction.R φ)) (hi : φ.nvars ≤ i.val) :
    trueVars (remove S (.v i) (.vt i)) = trueVars S := by
  ext j
  have hji : varIndex j ≠ i := by
    intro hh
    have he := congrArg Fin.val hh
    have := j.isLt
    simp only [varIndex] at he
    omega
  simp [trueVars, remove, hji]

theorem pending_pass_move {φ : Formula} (S : Finset (Vertex φ))
    (i : Fin (Construction.K φ)) :
    pending (remove S (.y i) (.z i)) = pending S := by ext j; simp [pending, remove]

theorem trueVars_pass_move {φ : Formula} (S : Finset (Vertex φ))
    (i : Fin (Construction.K φ)) :
    trueVars (remove S (.y i) (.z i)) = trueVars S := by ext j; simp [trueVars, remove]

theorem cnf_possible (φ : Formula) (U T : Finset (Fin φ.nvars)) (turn : Bool)
    (hw : PositiveCNF.TrueWins φ U T turn) : Satisfied φ (T ∪ U) := by
  induction hn : U.card using Nat.strong_induction_on generalizing U T turn with
  | h n ih =>
    by_cases he : U = ∅
    · subst U
      simpa using (cnf_empty φ T turn).mp hw
    · cases turn
      · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr he
        have hchild := (cnf_false φ U T he).mp hw i hi
        have hs := ih _ (hn ▸ Finset.card_erase_lt_of_mem hi) _ _ _ hchild rfl
        apply satisfied_mono φ _ hs
        exact Finset.union_subset_union_right (Finset.erase_subset _ _)
      · obtain ⟨i, hi, hchild⟩ := (cnf_true φ U T he).mp hw
        have hs := ih _ (hn ▸ Finset.card_erase_lt_of_mem hi) _ _ _ hchild rfl
        apply satisfied_mono φ _ hs
        intro j hj
        simp only [Finset.mem_union, Finset.mem_insert] at hj ⊢
        rcases hj with (rfl | hj) | hj
        · exact Or.inr hi
        · exact Or.inl hj
        · exact Or.inr (Finset.mem_of_mem_erase hj)

theorem cnf_winning_no_exhausted {φ : Formula} (S : Finset (Vertex φ))
    (hS : VertexReachable φ S) (turn : Bool)
    (hw : PositiveCNF.TrueWins φ (pending S) (trueVars S) turn)
    (j : Fin φ.clauses.length) : ∃ i ∈ φ.clauses[j], Vertex.f i ∈ S := by
  have hpossible := cnf_possible φ (pending S) (trueVars S) turn hw
  have hclause : φ.clauses[j] ∈ φ.clauses := List.getElem_mem _
  obtain ⟨i, hi, himem⟩ := hpossible _ hclause
  refine ⟨i, hi, ?_⟩
  rcases Finset.mem_union.mp himem with ht | hu
  · exact (Finset.mem_filter.mp ht).2.2
  · exact regular_vf S hS i (Finset.mem_filter.mp hu).2

theorem exhausted_after_assignment {φ : Formula} (S : Finset (Vertex φ))
    (hU : pending S = ∅) (hs : ¬ Satisfied φ (trueVars S)) :
    ∃ j : Fin φ.clauses.length, ∀ i ∈ φ.clauses[j], Vertex.f i ∉ S := by
  classical
  have hnot : ¬ ∀ j : Fin φ.clauses.length, ∃ i ∈ φ.clauses[j], i ∈ trueVars S := by
    intro hall
    apply hs
    intro C hC
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hC
    exact hall j
  push Not at hnot
  obtain ⟨j, hj⟩ := hnot
  refine ⟨j, ?_⟩
  intro i hi hf
  have hv : Vertex.v (varIndex i) ∉ S := by
    intro hv
    have hm : i ∈ pending S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    simpa [hU] using hm
  exact hj i hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, hf⟩)

end Lax689614Proofs
