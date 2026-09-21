import Lax689614Proofs.ByskovTail

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Lax689614Proofs.Byskov

open Lax689614 PositiveCNF

def Vertex.index : Vertex → ℕ
  | .x false => 0
  | .x true => 1
  | .u => 2
  | .up => 3
  | .e => 4
  | .y false => 5
  | .y true => 6
  | .yp false => 7
  | .yp true => 8

theorem Vertex.index_lt (v : Vertex) : v.index < 9 := by cases v <;> simp_all [Vertex.index] <;> split <;> decide

theorem Vertex.index_injective : Function.Injective Vertex.index := by decide

def node {r : ℕ} (i : Fin r) (v : Vertex) : Fin (9 * r + 1) :=
  ⟨9 * i.val + v.index, by have := i.isLt; have := v.index_lt; omega⟩

theorem node_eq {r : ℕ} (i j : Fin r) (v w : Vertex) :
    node i v = node j w ↔ i = j ∧ v = w := by
  constructor
  · intro h
    have he := congrArg Fin.val h
    change 9 * i.val + v.index = 9 * j.val + w.index at he
    have hv := v.index_lt
    have hw := w.index_lt
    have hij : i.val = j.val := by omega
    refine ⟨Fin.ext hij, Vertex.index_injective (by omega)⟩
  · rintro ⟨rfl, rfl⟩; rfl

def board {r : ℕ} (js : List (Fin r)) : Finset (Fin (9 * r + 1)) :=
  js.toFinset.biUnion (fun i => Finset.univ.image (node i))

theorem node_mem_board {r : ℕ} (js : List (Fin r)) (i : Fin r) (v : Vertex) :
    node i v ∈ board js ↔ i ∈ js := by
  simp [board, Finset.mem_biUnion, Finset.mem_image, node_eq, eq_comm]

theorem board_cons {r : ℕ} (i : Fin r) (js : List (Fin r)) :
    board (i :: js) = Finset.univ.image (node i) ∪ board js := by
  simp [board]

theorem round_disjoint_board {r : ℕ} (i : Fin r) (js : List (Fin r)) (hi : i ∉ js) :
    Disjoint (Finset.univ.image (node i)) (board js) := by
  apply Finset.disjoint_left.mpr
  intro x hx hb
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact hi ((node_mem_board js i v).mp hb)

theorem board_remove_round {r : ℕ} (i : Fin r) (js : List (Fin r)) (hi : i ∉ js) :
    board (i :: js) \ Finset.univ.image (node i) = board js := by
  rw [board_cons]
  ext x
  have hd := Finset.disjoint_left.mp (round_disjoint_board i js hi)
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop

def BaseLiteralOnly {r : ℕ} (base : List (Finset (Fin (9 * r + 1)))) : Prop :=
  ∀ C ∈ base, ∀ i v, node i v ∈ C → v.isLiteral = true

def layers {r : ℕ} (base : List (Finset (Fin (9 * r + 1)))) : List (Fin r) → List (Finset (Fin (9 * r + 1)))
  | [] => base
  | i :: js => localClauses.map (Finset.image (node i)) ++
      (layers base js).map (fun C => insert (node i .u) (insert (node i .e) C))

theorem layers_support {r : ℕ} (base : List (Finset (Fin (9 * r + 1)))) (hb : BaseLiteralOnly base)
    (js : List (Fin r)) (C : Finset (Fin (9 * r + 1))) (hC : C ∈ layers base js)
    (i : Fin r) (v : Vertex) (hv : node i v ∈ C) : v.isLiteral = true ∨ i ∈ js := by
  induction js generalizing C with
  | nil => exact Or.inl (hb C hC i v hv)
  | cons j js ih =>
    rcases List.mem_append.mp hC with hC | hC
    · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
      obtain ⟨w, _, he⟩ := Finset.mem_image.mp hv
      have hij := ((node_eq j i w v).mp he).1
      exact Or.inr (by simp [hij])
    · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
      rcases Finset.mem_insert.mp hv with he | hv
      · have hij := ((node_eq i j v .u).mp he).1
        exact Or.inr (by simp [hij])
      · rcases Finset.mem_insert.mp hv with he | hv
        · have hij := ((node_eq i j v .e).mp he).1
          exact Or.inr (by simp [hij])
        · rcases ih K hK hv with hv | hi
          · exact Or.inl hv
          · exact Or.inr (List.mem_cons_of_mem _ hi)

def layerData {r : ℕ} (base : List (Finset (Fin (9 * r + 1)))) (hb : BaseLiteralOnly base)
    (i : Fin r) (js : List (Fin r)) (hi : i ∉ js) : RoundData (9 * r + 1) where
  label := node i
  injective := fun v w h => ((node_eq i i v w).mp h).2
  tail := layers base js
  tail_literals := by
    intro C hC v hv
    exact (layers_support base hb js C hC i v hv).resolve_right hi

def AlternatingPlay {r : ℕ} (base : List (Finset (Fin (9 * r + 1)))) :
    List (Fin r) → Finset (Fin (9 * r + 1)) → Prop
  | [], T => Satisfied ⟨9 * r + 1, base⟩ T
  | i :: js, T => ∀ b : Bool, ∃ c : Bool,
      AlternatingPlay base js (insert (node i (.x b)) (insert (node i (.y c)) T))

theorem layers_correct {r : ℕ} (base : List (Finset (Fin (9 * r + 1)))) (hb : BaseLiteralOnly base)
    (js : List (Fin r)) (hjs : js.Nodup) (T : Finset (Fin (9 * r + 1))) (hT : Disjoint (board js) T) :
    TrueWins ⟨9 * r + 1, layers base js⟩ (board js) T false ↔ AlternatingPlay base js T := by
  induction js generalizing T with
  | nil => simpa [board, layers, AlternatingPlay] using cnf_empty ⟨9 * r + 1, base⟩ T false
  | cons i js ih =>
    obtain ⟨hi, hj⟩ := List.nodup_cons.mp hjs
    let d := layerData base hb i js hi
    have hU : ∀ v, d.label v ∈ board (i :: js) := by intro v; exact (node_mem_board _ i v).mpr (by simp)
    have ht : ∀ v, d.label v ∉ T := fun v hv => Finset.disjoint_left.mp hT (hU v) hv
    have hh := d.round_correct (board (i :: js)) T hU ht
    have hrem : d.remaining (board (i :: js)) Finset.univ = board js := board_remove_round i js hi
    have hclaim (b c : Bool) : d.claimed T {.x b, .y c} =
        insert (node i (.x b)) (insert (node i (.y c)) T) := by simp [RoundData.claimed, d, layerData]
    rw [hrem] at hh
    simp only [hclaim] at hh
    have hstart : d.Win (board (i :: js)) T ∅ ∅ false ↔
        TrueWins ⟨9 * r + 1, layers base (i :: js)⟩ (board (i :: js)) T false := by
      simp [RoundData.Win, RoundData.remaining, RoundData.claimed, RoundData.formula, d, layerData, layers]
    apply hstart.symm.trans
    apply hh.trans
    apply forall_congr'; intro b
    apply exists_congr; intro c
    apply ih hj
    apply Finset.disjoint_insert_right.mpr
    refine ⟨?_, Finset.disjoint_insert_right.mpr ⟨?_, ?_⟩⟩
    · simpa [node_mem_board] using hi
    · simpa [node_mem_board] using hi
    · exact hT.mono_left (by rw [board_cons]; exact Finset.subset_union_right)

end Lax689614Proofs.Byskov
