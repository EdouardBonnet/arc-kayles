import Lax689614Proofs.ByskovLayers

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Byskov

open Lax689614 PositiveCNF

structure SignedLiteral (r : ℕ) where
  round : Fin r
  existential : Bool
  positive : Bool
  deriving DecidableEq, Fintype

abbrev SignedCNF (r : ℕ) := List (Finset (SignedLiteral r))
abbrev Assignment (r : ℕ) := Fin r → Bool × Bool

def SignedLiteral.vertex {r : ℕ} (l : SignedLiteral r) : Vertex :=
  if l.existential then .y l.positive else .x l.positive

def SignedLiteral.node {r : ℕ} (l : SignedLiteral r) : Fin (9 * r + 1) := Byskov.node l.round l.vertex

def SignedLiteral.value {r : ℕ} (l : SignedLiteral r) (a : Assignment r) : Bool :=
  let b := if l.existential then (a l.round).2 else (a l.round).1
  decide (b = l.positive)

def SignedCNF.Satisfied {r : ℕ} (F : SignedCNF r) (a : Assignment r) : Prop :=
  ∀ C ∈ F, ∃ l ∈ C, l.value a = true

def SignedCNF.TruthFrom {r : ℕ} (F : SignedCNF r) : List (Fin r) → Assignment r → Prop
  | [], a => F.Satisfied a
  | i :: js, a => ∀ b : Bool, ∃ c : Bool, SignedCNF.TruthFrom F js (Function.update a i (b, c))

def SignedCNF.True {r : ℕ} (F : SignedCNF r) : Prop :=
  F.TruthFrom (List.finRange r) (fun _ => (false, false))

def literalClauses {r : ℕ} (F : SignedCNF r) : List (Finset (Fin (9 * r + 1))) :=
  F.map (Finset.image SignedLiteral.node)

theorem literalClauses_support {r : ℕ} (F : SignedCNF r) : BaseLiteralOnly (literalClauses F) := by
  intro C hC i v hv
  obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
  obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hv
  have heq := (node_eq l.round i l.vertex v).mp he
  rw [← heq.2]
  cases hk : l.existential <;> simp [SignedLiteral.vertex, hk, Vertex.isLiteral]

def claims {r : ℕ} (done : Finset (Fin r)) (a : Assignment r) : Finset (Fin (9 * r + 1)) :=
  done.biUnion fun i => {node i (.x (a i).1), node i (.y (a i).2)}

theorem literal_mem_claims {r : ℕ} (l : SignedLiteral r) (done : Finset (Fin r)) (a : Assignment r) :
    l.node ∈ claims done a ↔ l.round ∈ done ∧ l.value a = true := by
  cases l with
  | mk i kind sign =>
    cases kind <;>
      simp [claims, SignedLiteral.node, SignedLiteral.vertex, SignedLiteral.value,
        Finset.mem_biUnion, node_eq, eq_comm, and_assoc]

theorem clauses_satisfied_claims {r : ℕ} (F : SignedCNF r) (a : Assignment r) :
    Satisfied ⟨9 * r + 1, literalClauses F⟩ (claims Finset.univ a) ↔ F.Satisfied a := by
  simp only [Satisfied, literalClauses, List.forall_mem_map, SignedCNF.Satisfied]
  apply forall_congr'; intro C
  apply forall_congr'; intro hC
  constructor
  · rintro ⟨i, hi, hT⟩
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨l, hl, ((literal_mem_claims l Finset.univ a).mp hT).2⟩
  · rintro ⟨l, hl, hv⟩
    exact ⟨l.node, Finset.mem_image.mpr ⟨l, hl, rfl⟩,
      (literal_mem_claims l Finset.univ a).mpr ⟨Finset.mem_univ _, hv⟩⟩

theorem claims_insert_update {r : ℕ} (done : Finset (Fin r)) (a : Assignment r)
    (i : Fin r) (hi : i ∉ done) (b c : Bool) :
    claims (insert i done) (Function.update a i (b, c)) =
      insert (node i (.x b)) (insert (node i (.y c)) (claims done a)) := by
  have he : done.biUnion (fun j => {node j (.x (Function.update a i (b, c) j).1),
      node j (.y (Function.update a i (b, c) j).2)}) = claims done a := by
    apply Finset.biUnion_congr rfl
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [Function.update_of_ne hji]
  simp only [claims, Finset.biUnion_insert, Function.update_self, Finset.insert_union, Finset.empty_union]
  rw [he]
  simp [claims]

theorem complement_cons {r : ℕ} (i : Fin r) (js : List (Fin r)) (hi : i ∉ js) :
    Finset.univ \ js.toFinset = insert i (Finset.univ \ (i :: js).toFinset) := by
  ext j
  by_cases hj : j = i
  · subst j; simp [hi]
  · simp [hj, Ne.symm hj]

theorem alternatingPlay_truth {r : ℕ} (F : SignedCNF r) (js : List (Fin r)) (hjs : js.Nodup)
    (a : Assignment r) :
    AlternatingPlay (literalClauses F) js (claims (Finset.univ \ js.toFinset) a) ↔ F.TruthFrom js a := by
  induction js generalizing a with
  | nil => simpa [AlternatingPlay, SignedCNF.TruthFrom] using clauses_satisfied_claims F a
  | cons i js ih =>
    obtain ⟨hi, hj⟩ := List.nodup_cons.mp hjs
    simp only [AlternatingPlay, SignedCNF.TruthFrom]
    apply forall_congr'; intro b
    apply exists_congr; intro c
    have he : claims (Finset.univ \ js.toFinset) (Function.update a i (b, c)) =
        insert (node i (.x b)) (insert (node i (.y c)) (claims (Finset.univ \ (i :: js).toFinset) a)) := by
      rw [complement_cons i js hi, claims_insert_update _ _ _ (by simp)]
    rw [← he]
    exact ih hj _

theorem signedCNF_maker_first {r : ℕ} (F : SignedCNF r) :
    TrueWins ⟨9 * r + 1, layers (literalClauses F) (List.finRange r)⟩
      (board (List.finRange r)) ∅ false ↔ F.True := by
  rw [layers_correct (literalClauses F) (literalClauses_support F) _ (List.nodup_finRange r) ∅ (by simp)]
  have h := alternatingPlay_truth F (List.finRange r) (List.nodup_finRange r) (fun _ => (false, false))
  simpa [SignedCNF.True, claims] using h

end Lax689614Proofs.Byskov
