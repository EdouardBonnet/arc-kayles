import Lax689614Proofs.ByskovRound

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

namespace Lax689614Proofs.Byskov

open Lax689614 PositiveCNF

theorem RoundData.control_not_tail {n : ℕ} (d : RoundData n) (C : Finset (Fin n))
    (hC : C ∈ d.tail) (v : Vertex) (hv : v.isLiteral = false) : d.label v ∉ C := by
  intro h
  have hh := d.tail_literals C hC v h
  simp [hv] at hh

theorem RoundData.prime_implies_opposite {n : ℕ} (d : RoundData n) (b : Bool)
    (C : Finset (Fin n)) (hC : C ∈ d.formula.clauses) (hp : d.label (.yp b) ∈ C) :
    d.label (.y (!b)) ∈ C := by
  have hlocal : ∀ K ∈ localClauses, Vertex.yp b ∈ K → Vertex.y (!b) ∈ K := by
    cases b <;> simp [localClauses]
  rcases List.mem_append.mp hC with hC | hC
  · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
    exact (d.mem_image K _).mpr (hlocal K hK ((d.mem_image K _).mp hp))
  · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
    have hk : d.label (.yp b) ∈ K := by
      simpa [Finset.mem_insert, d.label_eq] using hp
    exact (d.control_not_tail K hK (.yp b) rfl hk).elim

theorem RoundData.prime_dominance {n : ℕ} (d : RoundData n) (T : Finset (Fin n)) (b : Bool) :
    ∀ S, Satisfied d.formula (insert (d.label (.yp b)) (T ∪ S)) →
      Satisfied d.formula (insert (d.label (.y (!b))) (T ∪ S)) :=
  dominates_of_clauses d.formula T _ _ (fun C hC hp => Or.inl (d.prime_implies_opposite b C hC hp))

theorem RoundData.unused_prime_irrelevant {n : ℕ} (d : RoundData n) (T : Finset (Fin n))
    (b : Bool) (hb : d.label (.y b) ∈ T) : PayoffIrrelevant d.formula T (d.label (.yp (!b))) := by
  apply irrelevant_of_hit_clauses
  intro C hC hp
  have hy := d.prime_implies_opposite (!b) C hC hp
  simp only [Bool.not_not] at hy
  exact ⟨d.label (.y b), hy, hb⟩

theorem RoundData.common_from_local {n : ℕ} (d : RoundData n) (T : Finset (Fin n))
    (Q : Finset Vertex) (v : Vertex) (hv : v = .u ∨ v = .e)
    (hlocal : ∀ C ∈ localClauses, (∃ j ∈ C, j ∈ Q) ∨ v ∈ C) :
    ∀ C ∈ d.formula.clauses, (∃ i ∈ C, i ∈ d.claimed T Q) ∨ d.label v ∈ C := by
  intro C hC
  rcases List.mem_append.mp hC with hC | hC
  · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
    rcases hlocal K hK with ⟨j, hj, hQ⟩ | hvK
    · exact Or.inl ⟨d.label j, (d.mem_image K j).mpr hj,
        Finset.mem_union_right T ((d.mem_image Q j).mpr hQ)⟩
    · exact Or.inr ((d.mem_image K v).mpr hvK)
  · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
    rcases hv with rfl | rfl <;> exact Or.inr (by simp)

theorem RoundData.win_true_move {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (P Q : Finset Vertex) (v : Vertex) (hU : d.label v ∈ U) (hv : v ∉ P)
    (hw : d.Win U T (insert v P) (insert v Q) false) : d.Win U T P Q true := by
  have hm := (d.remaining_mem U P v hU).mpr hv
  apply (cnf_true d.formula _ _ (Finset.nonempty_iff_ne_empty.mp ⟨d.label v, hm⟩)).mpr
  refine ⟨d.label v, hm, ?_⟩
  rw [d.remaining_erase, d.claimed_insert]
  exact hw

theorem RoundData.win_false_move {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (P Q : Finset Vertex) (v : Vertex) (hU : d.label v ∈ U) (hv : v ∉ P)
    (hw : d.Win U T P Q false) : d.Win U T (insert v P) Q true := by
  have hm := (d.remaining_mem U P v hU).mpr hv
  have hc := (cnf_false d.formula _ _ (Finset.nonempty_iff_ne_empty.mp ⟨d.label v, hm⟩)).mp hw _ hm
  rwa [d.remaining_erase] at hc

theorem RoundData.win_forced_true {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (P Q : Finset Vertex) (v : Vertex)
    (ht : ClauseThreat d.formula (d.remaining U P) (d.claimed T Q) {d.label v}) :
    d.Win U T P Q true ↔ d.Win U T (insert v P) (insert v Q) false := by
  change TrueWins d.formula _ _ true ↔ _
  rw [ht.forced_true, d.remaining_erase, d.claimed_insert]
  rfl

theorem RoundData.win_common_false {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (P Q : Finset Vertex) (v : Vertex) (hU : d.label v ∈ U) (hv : v ∉ P)
    (hc : ∀ C ∈ d.formula.clauses, (∃ i ∈ C, i ∈ d.claimed T Q) ∨ d.label v ∈ C) :
    d.Win U T P Q false ↔ d.Win U T (insert v P) Q true := by
  change TrueWins d.formula _ _ false ↔ _
  rw [common_vertex_forced_false d.formula _ _ (d.label v)
    ((d.remaining_mem U P v hU).mpr hv) hc, d.remaining_erase]
  rfl

end Lax689614Proofs.Byskov
