import Lax689614Proofs.CNFPairs

set_option backward.isDefEq.respectTransparency false

/-!
The one-round gadget from Byskov, BRICS RS-04-14 (2004), Theorem 4.
https://www.brics.dk/RS/04/14/BRICS-RS-04-14.pdf

True is Breaker and False is Maker. The unprimed `x` and `y` vertices
represent signed literals; the remaining vertices enforce the move order.
-/

namespace Lax689614Proofs.Byskov

open Lax689614 PositiveCNF

inductive Vertex where
  | x (value : Bool)
  | u
  | up
  | e
  | y (value : Bool)
  | yp (value : Bool)
  deriving DecidableEq, Fintype

def Vertex.isLiteral : Vertex → Bool
  | .x _ | .y _ => true
  | _ => false

def localClauses : List (Finset Vertex) :=
  [{.x false, .x true}, {.x false, .u, .up}, {.x true, .u, .up},
    {.x false, .u, .e, .y false, .y true}, {.x true, .u, .e, .y false, .y true},
    {.x false, .u, .e, .y false, .yp true}, {.x true, .u, .e, .y false, .yp true},
    {.x false, .u, .e, .yp false, .y true}, {.x true, .u, .e, .yp false, .y true}]

structure RoundData (n : ℕ) where
  label : Vertex → Fin n
  injective : Function.Injective label
  tail : List (Finset (Fin n))
  tail_literals : ∀ C ∈ tail, ∀ v, label v ∈ C → v.isLiteral = true

def RoundData.formula {n : ℕ} (d : RoundData n) : Formula :=
  ⟨n, localClauses.map (Finset.image d.label) ++
    d.tail.map (fun C => insert (d.label .u) (insert (d.label .e) C))⟩

def RoundData.remaining {n : ℕ} (d : RoundData n) (U : Finset (Fin n)) (P : Finset Vertex) :
    Finset (Fin n) := U \ P.image d.label

def RoundData.claimed {n : ℕ} (d : RoundData n) (T : Finset (Fin n)) (Q : Finset Vertex) :
    Finset (Fin n) := T ∪ Q.image d.label

def RoundData.Win {n : ℕ} (d : RoundData n) (U T : Finset (Fin n)) (P Q : Finset Vertex)
    (turn : Bool) : Prop := TrueWins d.formula (d.remaining U P) (d.claimed T Q) turn

theorem RoundData.label_eq {n : ℕ} (d : RoundData n) (v w : Vertex) :
    d.label v = d.label w ↔ v = w := d.injective.eq_iff

theorem RoundData.mem_image {n : ℕ} (d : RoundData n) (C : Finset Vertex) (v : Vertex) :
    d.label v ∈ C.image d.label ↔ v ∈ C := by
  simp [Finset.mem_image, d.injective.eq_iff]

theorem RoundData.remaining_mem {n : ℕ} (d : RoundData n) (U : Finset (Fin n))
    (P : Finset Vertex) (v : Vertex) (hv : d.label v ∈ U) :
    d.label v ∈ d.remaining U P ↔ v ∉ P := by
  simp [RoundData.remaining, hv, Finset.mem_image, d.injective.eq_iff]

theorem RoundData.claimed_mem {n : ℕ} (d : RoundData n) (T : Finset (Fin n))
    (Q : Finset Vertex) (v : Vertex) (hv : d.label v ∉ T) :
    d.label v ∈ d.claimed T Q ↔ v ∈ Q := by
  simp [RoundData.claimed, hv, Finset.mem_image, d.injective.eq_iff]

theorem RoundData.remaining_erase {n : ℕ} (d : RoundData n) (U : Finset (Fin n))
    (P : Finset Vertex) (v : Vertex) :
    (d.remaining U P).erase (d.label v) = d.remaining U (insert v P) := by
  ext i; simp [RoundData.remaining, and_comm, and_left_comm, and_assoc]

theorem RoundData.claimed_insert {n : ℕ} (d : RoundData n) (T : Finset (Fin n))
    (Q : Finset Vertex) (v : Vertex) :
    insert (d.label v) (d.claimed T Q) = d.claimed T (insert v Q) := by
  ext i; simp [RoundData.claimed, or_comm, or_left_comm, or_assoc]

theorem RoundData.local_mem {n : ℕ} (d : RoundData n) (C : Finset Vertex) (hC : C ∈ localClauses) :
    C.image d.label ∈ d.formula.clauses := by
  simp only [RoundData.formula, List.mem_append, List.mem_map]
  exact Or.inl ⟨C, hC, rfl⟩

theorem RoundData.local_threat {n : ℕ} (d : RoundData n) (U T : Finset (Fin n))
    (P Q C : Finset Vertex) (hU : ∀ v, d.label v ∈ U) (hT : ∀ v, d.label v ∉ T)
    (hC : C ∈ localClauses) (hCQ : Disjoint C Q) :
    ClauseThreat d.formula (d.remaining U P) (d.claimed T Q) ((C \ P).image d.label) := by
  refine ⟨C.image d.label, d.local_mem C hC, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro i hi ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    have hq := (d.claimed_mem T Q v (hT v)).mp ht
    exact Finset.disjoint_left.mp hCQ hv hq
  · ext i
    simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hp⟩
      exact ⟨v, ⟨hv, (d.remaining_mem U P v (hU v)).mp hp⟩, rfl⟩
    · rintro ⟨v, ⟨hv, hp⟩, rfl⟩
      exact ⟨⟨v, hv, rfl⟩, (d.remaining_mem U P v (hU v)).mpr hp⟩

end Lax689614Proofs.Byskov
