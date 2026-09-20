import Lax689614Proofs.Assignments

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles

inductive RegularEffect {φ : Formula} (S D : Finset (Vertex φ)) : Prop
  | setTrue (i : Fin φ.nvars) (hi : i ∈ pending S)
      (hU : pending D = (pending S).erase i) (hT : trueVars D = insert i (trueVars S))
      (hr : (liveV D).card + 1 = (liveV S).card) (hk : (liveY D).card = (liveY S).card)
  | setFalse (i : Fin φ.nvars) (hi : i ∈ pending S)
      (hU : pending D = (pending S).erase i) (hT : trueVars D = trueVars S)
      (hr : (liveV D).card + 1 = (liveV S).card) (hk : (liveY D).card = (liveY S).card)
  | passV (hU : pending D = pending S) (hT : trueVars D = trueVars S)
      (hr : (liveV D).card + 1 = (liveV S).card) (hk : (liveY D).card = (liveY S).card)
  | passY (hU : pending D = pending S) (hT : trueVars D = trueVars S)
      (hr : (liveV D).card = (liveV S).card) (hk : (liveY D).card + 1 = (liveY S).card)

theorem effect_vt {φ : Formula} (S : Finset (Vertex φ)) (hS : VertexReachable φ S)
    (i : Fin (Construction.R φ)) (hi : Vertex.v i ∈ S) :
    RegularEffect S (remove S (.v i) (.vt i)) := by
  have hr : (liveV (remove S (.v i) (.vt i))).card + 1 = (liveV S).card := by
    have he : liveV (remove S (.v i) (.vt i)) = (liveV S).erase i := by
      ext j; simp [liveV, remove]
    rw [he]
    exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have hk : (liveY (remove S (.v i) (.vt i))).card = (liveY S).card := by
    congr 1; ext j; simp [liveY, remove]
  by_cases hiv : i.val < φ.nvars
  · let j : Fin φ.nvars := ⟨i.val, hiv⟩
    have hij : varIndex j = i := Fin.ext rfl
    have hj : j ∈ pending S := by simp [pending, hij, hi]
    have hf := regular_vf S hS j (hij.symm ▸ hi)
    rw [← hij] at hr hk ⊢
    exact .setTrue j hj (pending_true_move S j) (trueVars_true_move S j hf) hr hk
  · exact .passV (pending_reserve_move S i (by omega))
      (trueVars_reserve_move S i (by omega)) hr hk

theorem effect_vf {φ : Formula} (S : Finset (Vertex φ)) (i : Fin φ.nvars)
    (hi : Vertex.v (varIndex i) ∈ S) :
    RegularEffect S (remove S (.v (varIndex i)) (.f i)) := by
  have hiU : i ∈ pending S := by simp [pending, hi]
  have hr : (liveV (remove S (.v (varIndex i)) (.f i))).card + 1 = (liveV S).card := by
    have he : liveV (remove S (.v (varIndex i)) (.f i)) = (liveV S).erase (varIndex i) := by
      ext j; simp [liveV, remove]
    rw [he]
    exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have hk : (liveY (remove S (.v (varIndex i)) (.f i))).card = (liveY S).card := by
    congr 1; ext j; simp [liveY, remove]
  exact .setFalse i hiU (pending_false_move S i) (trueVars_false_move S i hi) hr hk

theorem effect_yz {φ : Formula} (S : Finset (Vertex φ))
    (i : Fin (Construction.K φ)) (hi : Vertex.y i ∈ S) :
    RegularEffect S (remove S (.y i) (.z i)) := by
  have hr : (liveV (remove S (.y i) (.z i))).card = (liveV S).card := by
    congr 1; ext j; simp [liveV, remove]
  have hk : (liveY (remove S (.y i) (.z i))).card + 1 = (liveY S).card := by
    have he : liveY (remove S (.y i) (.z i)) = (liveY S).erase i := by
      ext j; simp [liveY, remove]
    rw [he]
    exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  exact .passY (pending_pass_move S i) (trueVars_pass_move S i) hr hk

theorem regular_effect {φ : Formula} (S : Finset (Vertex φ)) (hS : VertexReachable φ S)
    (u w : Vertex φ) (hu : u ∈ S) (hw : w ∈ S) (hr : vertexRegular u w) :
    RegularEffect S (remove S u w) := by
  rcases hr with ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ <;>
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact effect_vt S hS i hu
  · rw [remove_swap]; exact effect_vt S hS i hw
  · exact effect_vf S i hu
  · rw [remove_swap]; exact effect_vf S i hw
  · exact effect_yz S i hu
  · rw [remove_swap]; exact effect_yz S i hw

theorem effect_pending_le {φ : Formula} {S D : Finset (Vertex φ)} (h : RegularEffect S D) :
    (pending D).card ≤ (pending S).card := by
  cases h with
  | setTrue i hi hU hT hr hk => rw [hU]; exact Finset.card_erase_le
  | setFalse i hi hU hT hr hk => rw [hU]; exact Finset.card_erase_le
  | passV hU hT hr hk => rw [hU]
  | passY hU hT hr hk => rw [hU]

theorem false_after_regular {φ : Formula} {S D : Finset (Vertex φ)} (h : RegularEffect S D)
    (hw : ¬ PositiveCNF.TrueWins φ (pending S) (trueVars S) true) :
    ¬ PositiveCNF.TrueWins φ (pending D) (trueVars D) false := by
  cases h with
  | setTrue i hi hU hT hr hk =>
    rw [hU, hT]
    intro hw'
    exact hw ((cnf_true φ _ _ (Finset.nonempty_iff_ne_empty.mp ⟨i, hi⟩)).mpr ⟨i, hi, hw'⟩)
  | setFalse i hi hU hT hr hk =>
    rw [hU, hT]
    intro hw'
    apply hw
    apply (cnf_true φ _ _ (Finset.nonempty_iff_ne_empty.mp ⟨i, hi⟩)).mpr
    exact ⟨i, hi, cnf_mono φ _ _ _ false (Finset.subset_insert _ _) hw'⟩
  | passV hU hT hr hk =>
    rw [hU, hT]
    intro hw'
    exact hw ((cnf_strategy_stealing φ _ _).2.2 hw')
  | passY hU hT hr hk =>
    rw [hU, hT]
    intro hw'
    exact hw ((cnf_strategy_stealing φ _ _).2.2 hw')

theorem effect_satisfied {φ : Formula} {S D : Finset (Vertex φ)} (h : RegularEffect S D)
    (hs : Satisfied φ (trueVars S)) : Satisfied φ (trueVars D) := by
  cases h with
  | setTrue i hi hU hT hr hk => rw [hT]; exact satisfied_mono φ (Finset.subset_insert _ _) hs
  | setFalse i hi hU hT hr hk => rwa [hT]
  | passV hU hT hr hk => rwa [hT]
  | passY hU hT hr hk => rwa [hT]

theorem effect_counts {φ : Formula} {S D : Finset (Vertex φ)} (h : RegularEffect S D) :
    ((liveV D).card + 1 = (liveV S).card ∧ (liveY D).card = (liveY S).card) ∨
    ((liveV D).card = (liveV S).card ∧ (liveY D).card + 1 = (liveY S).card) := by
  cases h with
  | setTrue i hi hU hT hr hk => exact Or.inl ⟨hr, hk⟩
  | setFalse i hi hU hT hr hk => exact Or.inl ⟨hr, hk⟩
  | passV hU hT hr hk => exact Or.inl ⟨hr, hk⟩
  | passY hU hT hr hk => exact Or.inr ⟨hr, hk⟩

theorem true_after_regular {φ : Formula} {S D : Finset (Vertex φ)} (h : RegularEffect S D)
    (hw : TrueWins φ (pending S) (trueVars S) false) :
    TrueWins φ (pending D) (trueVars D) true := by
  cases h with
  | setTrue i hi hU hT hr hk =>
    rw [hU, hT]
    apply cnf_mono φ _ _ _ true (Finset.subset_insert _ _)
    exact (cnf_false φ _ _ (Finset.nonempty_iff_ne_empty.mp ⟨i, hi⟩)).mp hw i hi
  | setFalse i hi hU hT hr hk =>
    rw [hU, hT]
    exact (cnf_false φ _ _ (Finset.nonempty_iff_ne_empty.mp ⟨i, hi⟩)).mp hw i hi
  | passV hU hT hr hk => rw [hU, hT]; exact (cnf_strategy_stealing φ _ _).2.2 hw
  | passY hU hT hr hk => rw [hU, hT]; exact (cnf_strategy_stealing φ _ _).2.2 hw

theorem false_resources_after_regular {φ : Formula} {S D : Finset (Vertex φ)}
    (h : RegularEffect S D)
    (hr : φ.clauses.length + 2 * (pending S).card + 2 ≤ (liveV S).card)
    (hk : (pending S).card + 2 ≤ (liveY S).card)
    (hp : ((liveV S).card + (liveY S).card) % 2 = 1) :
    φ.clauses.length + 2 * (pending D).card + 1 ≤ (liveV D).card ∧
    (pending D).card + 1 ≤ (liveY D).card ∧
    ((liveV D).card + (liveY D).card) % 2 = 0 := by
  cases h with
  | setTrue i hi hU hT hv hy =>
    have hcard := Finset.card_erase_add_one hi
    rw [← hU] at hcard
    omega
  | setFalse i hi hU hT hv hy =>
    have hcard := Finset.card_erase_add_one hi
    rw [← hU] at hcard
    omega
  | passV hU hT hv hy => rw [hU]; omega
  | passY hU hT hv hy => rw [hU]; omega

end Lax689614Proofs
