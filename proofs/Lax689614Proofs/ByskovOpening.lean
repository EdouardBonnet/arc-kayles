import Lax689614Proofs.ByskovResponses

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Lax689614Proofs.Byskov

open Lax689614 PositiveCNF

theorem RoundData.both_x_before_y {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (b : Bool) (hw : d.Win U T beforeY (trueBeforeY b) true) : d.Win U T beforeY xPlayed true := by
  have hin : d.claimed T (trueBeforeY b) = insert (d.label .up) (d.claimed T {.x b}) := by
    rw [d.claimed_insert]
    congr 1; ext v; simp [trueBeforeY, or_comm]
  have hout : d.claimed T xPlayed = insert (d.label (.x (!b))) (d.claimed T {.x b}) := by
    rw [d.claimed_insert]
    congr 1; cases b <;> decide
  change TrueWins d.formula (d.remaining U beforeY) _ true at hw ⊢
  rw [hin] at hw
  rw [hout]
  apply cnf_payoff_mono d.formula _ _ _ true ?_ hw
  intro S hs
  simpa only [Finset.insert_union] using d.up_dominance T b S (by
    simpa only [Finset.insert_union] using hs)

theorem RoundData.u_then_x {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (hU : ∀ v, d.label v ∈ U) (hT : ∀ v, d.label v ∉ T) (b : Bool)
    (hY : d.Win U T beforeY (trueBeforeY b) true) : d.Win U T {.u, .x b} {.x b} false := by
  let P : Finset Vertex := {.u, .x b}
  let Q : Finset Vertex := {.x b}
  have hq : d.label (.x (!b)) ∈ d.remaining U P :=
    (d.remaining_mem U P _ (hU _)).mpr (by cases b <;> decide)
  have hup : d.label .up ∈ d.remaining U P := (d.remaining_mem U P _ (hU _)).mpr (by simp [P])
  have he : d.label .e ∈ d.remaining U P := (d.remaining_mem U P _ (hU _)).mpr (by simp [P])
  apply (cnf_false d.formula _ _ (Finset.nonempty_iff_ne_empty.mp ⟨d.label .e, he⟩)).mpr
  intro z hz
  by_cases hzq : z = d.label (.x (!b))
  · subst z
    rw [d.remaining_erase]
    have hp : insert (Vertex.x (!b)) P = beforeUp := by cases b <;> decide
    rw [hp]
    have hnormal := (d.normal_after_x U T hU hT b).mpr hY
    exact d.win_false_move U T xPlayed {.x b} .u (hU _) (by decide) hnormal
  by_cases hzup : z = d.label .up
  · subst z
    rw [d.remaining_erase]
    have hboth := d.both_x_before_y U T b hY
    have hcommon := d.win_common_false U T beforeE xPlayed .e (hU _) (by decide)
      (d.common_from_local T xPlayed .e (Or.inr rfl) (by simp [localClauses, xPlayed]))
    have hwin := hcommon.mpr hboth
    have hp : insert (Vertex.x (!b)) (insert .up P) = beforeE := by cases b <;> decide
    have hQ : insert (Vertex.x (!b)) Q = xPlayed := by cases b <;> decide
    apply d.win_true_move U T (insert .up P) Q (.x (!b)) (hU _) (by cases b <;> decide)
    simpa only [hp, hQ] using hwin
  by_cases hze : z = d.label .e
  · subst z
    rw [d.remaining_erase]
    have hp : insert Vertex.up (insert (.x (!b)) (insert .e P)) = beforeY := by cases b <;> decide
    have hQ : insert Vertex.up Q = trueBeforeY b := by ext v; simp [Q, trueBeforeY, or_comm]
    apply d.win_pair_lift U T (insert .e P) Q (.x (!b)) .up true (by simp)
      (hU _) (hU _) (by cases b <;> decide) (by simp [P]) (d.up_dominance T b)
    simpa only [hp, hQ] using hY
  · apply reply_with_two_choices d.formula (d.remaining U P) (d.claimed T Q)
      (d.label (.x (!b))) (d.label .up) (d.label .e) z
      (by simp [d.label_eq]) (by simp [d.label_eq]) (by simp [d.label_eq]) hq hup he hzq hzup hze
    all_goals
      rw [d.claimed_insert, d.claimed_insert]
      apply d.satisfied_from_named
      · simp
      · cases b <;> simp [localClauses, Q]

theorem RoundData.u_opening {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (hU : ∀ v, d.label v ∈ U) (hT : ∀ v, d.label v ∉ T)
    (hY : d.Win U T beforeY (trueBeforeY false) true) : d.Win U T {.u} ∅ true := by
  apply d.win_true_move U T {.u} ∅ (.x false) (hU _) (by decide)
  have hw := d.u_then_x U T hU hT false hY
  simpa only [Finset.insert_empty, Finset.pair_comm] using hw

theorem RoundData.opening_iff {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (hU : ∀ v, d.label v ∈ U) (hT : ∀ v, d.label v ∉ T) :
    d.Win U T ∅ ∅ false ↔ ∀ b : Bool, d.Win U T beforeY (trueBeforeY b) true := by
  constructor
  · intro hw b
    have hx := d.win_false_move U T ∅ ∅ (.x (!b)) (hU _) (by simp) hw
    exact (d.normal_after_x U T hU hT b).mp ((d.x_response U T hU hT b).mp hx)
  · intro h
    have hne : U ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨d.label .u, hU .u⟩
    have hh : TrueWins d.formula U T false := by
      apply (cnf_false d.formula U T hne).mpr
      intro z hz
      by_cases h₀ : z = d.label (.x false)
      · subst z
        have hw := (d.x_response U T hU hT true).mpr ((d.normal_after_x U T hU hT true).mpr (h true))
        simpa [RoundData.Win, RoundData.remaining, RoundData.claimed, Finset.sdiff_singleton_eq_erase] using hw
      by_cases h₁ : z = d.label (.x true)
      · subst z
        have hw := (d.x_response U T hU hT false).mpr ((d.normal_after_x U T hU hT false).mpr (h false))
        simpa [RoundData.Win, RoundData.remaining, RoundData.claimed, Finset.sdiff_singleton_eq_erase] using hw
      by_cases hu : z = d.label .u
      · subst z
        simpa [RoundData.Win, RoundData.remaining, RoundData.claimed, Finset.sdiff_singleton_eq_erase] using
          d.u_opening U T hU hT (h false)
      · exact d.opening_outside_loses U T hU z h₀ h₁ hu
    simpa [RoundData.Win, RoundData.remaining, RoundData.claimed] using hh

end Lax689614Proofs.Byskov
