import Lax689614Proofs.ByskovLocal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Lax689614Proofs.Byskov

open Lax689614 PositiveCNF

def xPlayed : Finset Vertex := {.x false, .x true}
def beforeUp : Finset Vertex := insert .u xPlayed
def beforeE : Finset Vertex := insert .up beforeUp
def beforeY : Finset Vertex := insert .e beforeE
def trueBeforeY (b : Bool) : Finset Vertex := {.x b, .up}

theorem RoundData.x_response {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (hU : ∀ v, d.label v ∈ U) (hT : ∀ v, d.label v ∉ T) (b : Bool) :
    d.Win U T {.x (!b)} ∅ true ↔ d.Win U T xPlayed {.x b} false := by
  have ht := d.local_threat U T {.x (!b)} ∅ {.x false, .x true} hU hT
    (by decide) (by simp)
  have he : (({Vertex.x false, .x true} : Finset Vertex) \ {.x (!b)}) = {.x b} := by cases b <;> decide
  rw [he] at ht
  simp only [Finset.image_singleton] at ht
  have hh := d.win_forced_true U T {.x (!b)} ∅ (.x b) ht
  have hp : insert (Vertex.x b) {.x (!b)} = xPlayed := by cases b <;> decide
  simpa only [hp, Finset.insert_empty] using hh

theorem RoundData.normal_after_x {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (hU : ∀ v, d.label v ∈ U) (hT : ∀ v, d.label v ∉ T) (b : Bool) :
    d.Win U T xPlayed {.x b} false ↔ d.Win U T beforeY (trueBeforeY b) true := by
  have hu := d.win_common_false U T xPlayed {.x b} .u (hU .u) (by decide)
    (d.common_from_local T {.x b} .u (Or.inl rfl) (by cases b <;> simp [localClauses]))
  have ht := d.local_threat U T beforeUp {.x b} {.x (!b), .u, .up} hU hT
    (by cases b <;> decide) (by cases b <;> decide)
  have hdiff : ({Vertex.x (!b), .u, .up} \ beforeUp) = {.up} := by cases b <;> decide
  rw [hdiff] at ht
  simp only [Finset.image_singleton] at ht
  have hup := d.win_forced_true U T beforeUp {.x b} .up ht
  have hQ : insert Vertex.up {.x b} = trueBeforeY b := by ext v; simp [trueBeforeY, or_comm]
  rw [hQ] at hup
  have he := d.win_common_false U T beforeE (trueBeforeY b) .e (hU .e) (by decide)
    (d.common_from_local T (trueBeforeY b) .e (Or.inr rfl)
      (by cases b <;> simp [localClauses, trueBeforeY]))
  exact hu.trans (hup.trans he)

theorem RoundData.y_choice {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (hU : ∀ v, d.label v ∈ U) (hT : ∀ v, d.label v ∉ T) (b : Bool) :
    d.Win U T beforeY (trueBeforeY b) true ↔
      ∃ c : Bool, d.Win U T (insert (.y c) beforeY) (insert (.y c) (trueBeforeY b)) false := by
  have h₁ := d.local_threat U T beforeY (trueBeforeY b)
    {.x (!b), .u, .e, .y false, .y true} hU hT
    (by cases b <;> decide) (by cases b <;> decide)
  have h₂ := d.local_threat U T beforeY (trueBeforeY b)
    {.x (!b), .u, .e, .y false, .yp true} hU hT
    (by cases b <;> decide) (by cases b <;> decide)
  have h₃ := d.local_threat U T beforeY (trueBeforeY b)
    {.x (!b), .u, .e, .yp false, .y true} hU hT
    (by cases b <;> decide) (by cases b <;> decide)
  have hd₁ : ({Vertex.x (!b), .u, .e, .y false, .y true} \ beforeY) = {.y false, .y true} := by cases b <;> decide
  have hd₂ : ({Vertex.x (!b), .u, .e, .y false, .yp true} \ beforeY) = {.y false, .yp true} := by cases b <;> decide
  have hd₃ : ({Vertex.x (!b), .u, .e, .yp false, .y true} \ beforeY) = {.yp false, .y true} := by cases b <;> decide
  rw [hd₁] at h₁
  rw [hd₂] at h₂
  rw [hd₃] at h₃
  simp only [Finset.image_insert, Finset.image_singleton] at h₁ h₂ h₃
  have hh := three_pairs_choice d.formula (d.remaining U beforeY) (d.claimed T (trueBeforeY b))
    (d.label (.y false)) (d.label (.y true)) (d.label (.yp false)) (d.label (.yp true))
    (by simp [d.label_eq]) (by simp [d.label_eq]) (by simp [d.label_eq]) (by simp [d.label_eq]) h₁ h₂ h₃
  simp only [d.remaining_erase, d.claimed_insert] at hh
  exact hh.trans (by simp only [Bool.exists_bool]; rfl)

theorem RoundData.y_response_pair {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (hU : ∀ v, d.label v ∈ U) (hT : ∀ v, d.label v ∉ T) (b c : Bool) :
    d.Win U T (insert (.y c) beforeY) (insert (.y c) (trueBeforeY b)) false ↔
      d.Win U T (insert (.yp c) (insert (.y (!c)) (insert (.y c) beforeY)))
        (insert (.yp c) (insert (.y c) (trueBeforeY b))) false := by
  let P := insert (Vertex.y c) beforeY
  let Q := insert (Vertex.y c) (trueBeforeY b)
  have ht := d.local_threat U T P Q {.x (!b), .u, .e, .yp c, .y (!c)} hU hT
    (by cases b <;> cases c <;> decide) (by cases b <;> cases c <;> decide)
  have hdiff : ({Vertex.x (!b), .u, .e, .yp c, .y (!c)} \ P) = {.y (!c), .yp c} := by
    cases b <;> cases c <;> decide
  rw [hdiff] at ht
  simp only [Finset.image_insert, Finset.image_singleton] at ht
  have hq := (d.remaining_mem U P (.y (!c)) (hU _)).mpr (by cases c <;> decide)
  have hr := (d.remaining_mem U P (.yp c) (hU _)).mpr (by cases c <;> decide)
  have hh := cnf_pair_eliminate d.formula (d.remaining U P) (d.claimed T Q)
    (d.label (.y (!c))) (d.label (.yp c)) (by simp [d.label_eq]) hq hr ht
    (d.prime_dominance (d.claimed T Q) c)
  simpa only [d.remaining_erase, d.claimed_insert, RoundData.Win, P, Q] using hh

end Lax689614Proofs.Byskov
