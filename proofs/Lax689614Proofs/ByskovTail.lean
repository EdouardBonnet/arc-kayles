import Lax689614Proofs.ByskovOpening
import Lax689614Proofs.CNFRestriction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Lax689614Proofs.Byskov

open Lax689614 PositiveCNF

def donePlayed (c : Bool) : Finset Vertex :=
  insert (.yp c) (insert (.y (!c)) (insert (.y c) beforeY))

def doneTrue (b c : Bool) : Finset Vertex :=
  insert (.yp c) (insert (.y c) (trueBeforeY b))

def literalsOf (Q : Finset Vertex) : Finset Vertex := Q.filter (fun v => v.isLiteral = true)

theorem RoundData.tail_hit {n : ℕ} (d : RoundData n) (B : Finset (Fin n)) (Q : Finset Vertex)
    (C : Finset (Fin n)) (hC : C ∈ d.tail) :
    (∃ i ∈ C, i ∈ d.claimed B Q) ↔ ∃ i ∈ C, i ∈ d.claimed B (literalsOf Q) := by
  constructor
  · rintro ⟨i, hi, hQ⟩
    rcases Finset.mem_union.mp hQ with hiB | hiQ
    · exact ⟨i, hi, Finset.mem_union_left _ hiB⟩
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hiQ
      have hl := d.tail_literals C hC v hi
      exact ⟨d.label v, hi, Finset.mem_union_right B
        ((d.mem_image (literalsOf Q) v).mpr (Finset.mem_filter.mpr ⟨hv, hl⟩))⟩
  · rintro ⟨i, hi, hQ⟩
    refine ⟨i, hi, ?_⟩
    exact Finset.union_subset_union_right (Finset.image_mono d.label (Finset.filter_subset _ _)) hQ

theorem RoundData.terminal_tail {n : ℕ} (d : RoundData n) (B : Finset (Fin n)) (Q : Finset Vertex)
    (huB : d.label .u ∉ B) (heB : d.label .e ∉ B) (huQ : Vertex.u ∉ Q) (heQ : Vertex.e ∉ Q)
    (hl : ∀ C ∈ localClauses, ∃ v ∈ C, v ∈ Q) :
    Satisfied d.formula (d.claimed B Q) ↔ Satisfied ⟨n, d.tail⟩ (d.claimed B (literalsOf Q)) := by
  have hu : d.label .u ∉ d.claimed B Q := by simpa [d.claimed_mem B Q .u huB] using huQ
  have he : d.label .e ∉ d.claimed B Q := by simpa [d.claimed_mem B Q .e heB] using heQ
  constructor
  · intro hs C hC
    have hm : insert (d.label .u) (insert (d.label .e) C) ∈ d.formula.clauses :=
      List.mem_append_right _ (List.mem_map.mpr ⟨C, hC, rfl⟩)
    obtain ⟨i, hi, hT⟩ := hs _ hm
    have hiC : i ∈ C := by
      rcases Finset.mem_insert.mp hi with hiu | hi
      · exact (hu (hiu ▸ hT)).elim
      · rcases Finset.mem_insert.mp hi with hie | hiC
        · exact (he (hie ▸ hT)).elim
        · exact hiC
    exact (d.tail_hit B Q C hC).mp ⟨i, hiC, hT⟩
  · intro hs C hC
    rcases List.mem_append.mp hC with hC | hC
    · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
      obtain ⟨v, hv, hQ⟩ := hl K hK
      exact ⟨d.label v, (d.mem_image K v).mpr hv, Finset.mem_union_right B ((d.mem_image Q v).mpr hQ)⟩
    · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
      obtain ⟨i, hi, hT⟩ := (d.tail_hit B Q K hK).mpr (hs K hK)
      exact ⟨i, by simp [hi], hT⟩

theorem RoundData.named_not_remaining_all {n : ℕ} (d : RoundData n) (U : Finset (Fin n))
    (v : Vertex) : d.label v ∉ d.remaining U Finset.univ := by
  intro hv
  exact (Finset.mem_sdiff.mp hv).2 ((d.mem_image Finset.univ v).mpr (Finset.mem_univ _))

theorem RoundData.finished_tail {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (hU : ∀ v, d.label v ∈ U) (hT : ∀ v, d.label v ∉ T) (b c : Bool) :
    d.Win U T (donePlayed c) (doneTrue b c) false ↔
      TrueWins ⟨n, d.tail⟩ (d.remaining U Finset.univ) (d.claimed T {.x b, .y c}) false := by
  have hinert := d.unused_prime_irrelevant (d.claimed T (doneTrue b c)) c
    ((d.claimed_mem T (doneTrue b c) (.y c) (hT _)).mpr (by simp [doneTrue]))
  have he : insert (Vertex.yp (!c)) (donePlayed c) = Finset.univ := by cases c <;> decide
  have hav : d.label (.yp (!c)) ∈ d.remaining U (donePlayed c) :=
    (d.remaining_mem U (donePlayed c) _ (hU _)).mpr (by cases c <;> decide)
  have hboard : insert (d.label (.yp (!c))) (d.remaining U Finset.univ) = d.remaining U (donePlayed c) := by
    rw [← he, ← d.remaining_erase]
    exact Finset.insert_erase hav
  have hi := cnf_ignore_inert d.formula (d.remaining U Finset.univ) (d.claimed T (doneTrue b c))
    (d.label (.yp (!c))) (d.named_not_remaining_all U _) hinert false
  rw [hboard] at hi
  change TrueWins d.formula _ _ false ↔ _
  apply hi.trans
  apply cnf_payoff_congr_on n d.formula.clauses d.tail
  intro S hS
  have hB : ∀ v, d.label v ∉ T ∪ S := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hT v hv
    · exact d.named_not_remaining_all U v (hS hv)
  have hf : literalsOf (doneTrue b c) = {.x b, .y c} := by cases b <;> cases c <;> decide
  have ht := d.terminal_tail (T ∪ S) (doneTrue b c) (hB .u) (hB .e)
    (by cases b <;> cases c <;> decide) (by cases b <;> cases c <;> decide)
    (by cases b <;> cases c <;> simp [localClauses, doneTrue, trueBeforeY])
  rw [hf] at ht
  simpa [RoundData.formula, RoundData.claimed, Finset.union_assoc,
    Finset.union_left_comm, Finset.union_comm] using ht

theorem RoundData.round_correct {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (hU : ∀ v, d.label v ∈ U) (hT : ∀ v, d.label v ∉ T) :
    d.Win U T ∅ ∅ false ↔ ∀ b : Bool, ∃ c : Bool,
      TrueWins ⟨n, d.tail⟩ (d.remaining U Finset.univ) (d.claimed T {.x b, .y c}) false := by
  rw [d.opening_iff U T hU hT]
  apply forall_congr'; intro b
  rw [d.y_choice U T hU hT b]
  apply exists_congr; intro c
  rw [d.y_response_pair U T hU hT b c]
  exact d.finished_tail U T hU hT b c

end Lax689614Proofs.Byskov
