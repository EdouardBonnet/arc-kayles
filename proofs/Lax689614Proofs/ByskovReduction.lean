import Lax689614Proofs.AlternatingCNF

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Lax689614Proofs.Byskov

open Lax689614 PositiveCNF

def dummy (r : ℕ) : Fin (9 * r + 1) := ⟨9 * r, by omega⟩

theorem node_ne_dummy {r : ℕ} (i : Fin r) (v : Vertex) : node i v ≠ dummy r := by
  intro he
  have hh := congrArg Fin.val he
  have hi := i.isLt
  have hv := v.index_lt
  simp only [node, dummy] at hh
  omega

theorem Vertex.index_surjective (j : ℕ) (hj : j < 9) : ∃ v : Vertex, v.index = j := by
  interval_cases j <;>
    first | exact ⟨.x false, rfl⟩ | exact ⟨.x true, rfl⟩ | exact ⟨.u, rfl⟩ |
      exact ⟨.up, rfl⟩ | exact ⟨.e, rfl⟩ | exact ⟨.y false, rfl⟩ |
      exact ⟨.y true, rfl⟩ | exact ⟨.yp false, rfl⟩ | exact ⟨.yp true, rfl⟩

theorem node_of_ne_dummy {r : ℕ} (x : Fin (9 * r + 1)) (hx : x ≠ dummy r) :
    ∃ i v, node i v = x := by
  have hval : x.val ≠ 9 * r := by intro h; exact hx (Fin.ext h)
  have hlt : x.val < 9 * r := by have := x.isLt; omega
  have hi : x.val / 9 < r := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  obtain ⟨v, hv⟩ := Vertex.index_surjective (x.val % 9) (Nat.mod_lt _ (by decide))
  refine ⟨⟨x.val / 9, hi⟩, v, ?_⟩
  apply Fin.ext
  change 9 * (x.val / 9) + v.index = x.val
  rw [hv]
  exact Nat.div_add_mod x.val 9

theorem board_all (r : ℕ) : board (List.finRange r) = Finset.univ.erase (dummy r) := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · intro hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact node_ne_dummy i v
  · intro hx
    obtain ⟨i, v, rfl⟩ := node_of_ne_dummy x hx
    exact (node_mem_board _ i v).mpr (List.mem_finRange i)

theorem layers_no_dummy {r : ℕ} (F : SignedCNF r) (js : List (Fin r)) :
    ∀ C ∈ layers (literalClauses F) js, dummy r ∉ C := by
  induction js with
  | nil =>
    intro C hC hx
    obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hx
    exact node_ne_dummy l.round l.vertex he
  | cons i js ih =>
    intro C hC hx
    rcases List.mem_append.mp hC with hC | hC
    · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
      obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hx
      exact node_ne_dummy i v he
    · obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hC
      rcases Finset.mem_insert.mp hx with he | hx
      · exact node_ne_dummy i .u he.symm
      · rcases Finset.mem_insert.mp hx with he | hx
        · exact node_ne_dummy i .e he.symm
        · exact ih K hK hx

def positiveFormula {r : ℕ} (F : SignedCNF r) : Formula :=
  ⟨9 * r + 1, {dummy r} :: layers (literalClauses F) (List.finRange r)⟩

theorem prepend_singleton_payoff (n : ℕ) (cs : List (Finset (Fin n))) (d : Fin n)
    (hd : ∀ C ∈ cs, d ∉ C) (S : Finset (Fin n)) :
    Satisfied ⟨n, {d} :: cs⟩ (insert d S) ↔ Satisfied ⟨n, cs⟩ S := by
  constructor
  · intro hs C hC
    obtain ⟨i, hi, ht⟩ := hs C (List.mem_cons_of_mem _ hC)
    rcases Finset.mem_insert.mp ht with he | ht
    · exact (hd C hC (he ▸ hi)).elim
    · exact ⟨i, hi, ht⟩
  · intro hs C hC
    rcases List.mem_cons.mp hC with he | hC
    · subst C; exact ⟨d, by simp, by simp⟩
    · obtain ⟨i, hi, ht⟩ := hs C hC
      exact ⟨i, hi, Finset.mem_insert_of_mem ht⟩

theorem positiveFormula_correct {r : ℕ} (F : SignedCNF r) : FirstWins (positiveFormula F) ↔ F.True := by
  have ht : ClauseThreat (positiveFormula F) Finset.univ ∅ {dummy r} :=
    ⟨{dummy r}, by simp [positiveFormula], by simp, by simp⟩
  change TrueWins (positiveFormula F) Finset.univ ∅ true ↔ _
  rw [ht.forced_true, ← board_all]
  have hc := cnf_payoff_congr_on (9 * r + 1) (positiveFormula F).clauses
    (layers (literalClauses F) (List.finRange r)) (board (List.finRange r)) {dummy r} ∅ false
    (fun S _ => by
      simpa [positiveFormula] using prepend_singleton_payoff (9 * r + 1)
        (layers (literalClauses F) (List.finRange r)) (dummy r) (layers_no_dummy F _) S)
  apply Iff.trans ?_ (signedCNF_maker_first F)
  simpa [positiveFormula] using hc

theorem layers_length {r : ℕ} (base : List (Finset (Fin (9 * r + 1)))) (js : List (Fin r)) :
    (layers base js).length = 9 * js.length + base.length := by
  induction js with
  | nil => simp [layers]
  | cons i js ih => simp [layers, localClauses, ih] <;> omega

theorem positiveFormula_clause_count {r : ℕ} (F : SignedCNF r) :
    (positiveFormula F).clauses.length = 9 * r + F.length + 1 := by
  simp [positiveFormula, layers_length, literalClauses]

end Lax689614Proofs.Byskov
