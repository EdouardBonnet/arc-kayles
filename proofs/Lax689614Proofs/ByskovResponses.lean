import Lax689614Proofs.ByskovNormal

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Byskov

open Lax689614 PositiveCNF

theorem RoundData.satisfied_from_named {n : ℕ} (d : RoundData n) (T : Finset (Fin n))
    (Q : Finset Vertex) (hc : Vertex.u ∈ Q ∨ Vertex.e ∈ Q)
    (hl : ∀ C ∈ localClauses, ∃ v ∈ C, v ∈ Q) : Satisfied d.formula (d.claimed T Q) := by
  intro C hC
  rcases List.mem_append.mp hC with hC | hC
  · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
    obtain ⟨v, hv, hQ⟩ := hl K hK
    exact ⟨d.label v, (d.mem_image K v).mpr hv,
      Finset.mem_union_right T ((d.mem_image Q v).mpr hQ)⟩
  · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
    rcases hc with hu | he
    · exact ⟨d.label .u, by simp, Finset.mem_union_right T ((d.mem_image Q .u).mpr hu)⟩
    · exact ⟨d.label .e, by simp, Finset.mem_union_right T ((d.mem_image Q .e).mpr he)⟩

theorem RoundData.up_dominance {n : ℕ} (d : RoundData n) (T : Finset (Fin n)) (b : Bool) :
    ∀ S, Satisfied d.formula (insert (d.label .up) (d.claimed T {.x b} ∪ S)) →
      Satisfied d.formula (insert (d.label (.x (!b))) (d.claimed T {.x b} ∪ S)) := by
  apply dominates_of_clauses
  intro C hC hup
  rcases List.mem_append.mp hC with hC | hC
  · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
    have hv := (d.mem_image K .up).mp hup
    have hl : ∀ C ∈ localClauses, Vertex.up ∈ C → Vertex.x (!b) ∈ C ∨ Vertex.x b ∈ C := by
      cases b <;> simp [localClauses]
    rcases hl K hK hv with hq | hx
    · exact Or.inl ((d.mem_image K _).mpr hq)
    · exact Or.inr ⟨d.label (.x b), (d.mem_image K _).mpr hx,
        Finset.mem_union_right T (by simp)⟩
  · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
    have hk : d.label .up ∈ K := by simpa [d.label_eq] using hup
    exact (d.control_not_tail K hK .up rfl hk).elim

theorem RoundData.win_pair_lift {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (P Q : Finset Vertex) (q r : Vertex) (turn : Bool) (hqr : q ≠ r)
    (hqU : d.label q ∈ U) (hrU : d.label r ∈ U) (hqP : q ∉ P) (hrP : r ∉ P)
    (hdom : ∀ S, Satisfied d.formula (insert (d.label r) (d.claimed T Q ∪ S)) →
      Satisfied d.formula (insert (d.label q) (d.claimed T Q ∪ S)))
    (hw : d.Win U T (insert r (insert q P)) (insert r Q) turn) : d.Win U T P Q turn := by
  have hq := (d.remaining_mem U P q hqU).mpr hqP
  have hr := (d.remaining_mem U P r hrU).mpr hrP
  let core := ((d.remaining U P).erase (d.label q)).erase (d.label r)
  have hh : TrueWins d.formula core (insert (d.label r) (d.claimed T Q)) turn := by
    simpa only [core, d.remaining_erase, d.claimed_insert, RoundData.Win] using hw
  have hlift := cnf_pair_lift d.formula core (d.claimed T Q) (d.label q) (d.label r)
    (by simpa [d.label_eq] using hqr) (by simp [core]) (by simp [core]) turn hdom hh
  simpa only [core, restore_two _ _ _ hq hr, RoundData.Win] using hlift

theorem RoundData.opening_outside_loses {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (hU : ∀ v, d.label v ∈ U) (z : Fin n)
    (hz₀ : z ≠ d.label (.x false)) (hz₁ : z ≠ d.label (.x true)) (hzu : z ≠ d.label .u) :
    TrueWins d.formula (U.erase z) T true := by
  apply reply_with_two_choices d.formula U T (d.label (.x false)) (d.label (.x true)) (d.label .u) z
    (by simp [d.label_eq]) (by simp [d.label_eq]) (by simp [d.label_eq])
    (hU _) (hU _) (hU _) hz₀ hz₁ hzu
  all_goals
    have he : T = d.claimed T ∅ := by simp [RoundData.claimed]
    rw [he, d.claimed_insert, d.claimed_insert]
    apply d.satisfied_from_named
    · simp
    · simp [localClauses]

end Lax689614Proofs.Byskov
