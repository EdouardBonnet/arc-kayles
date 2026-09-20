import Lax689614Proofs.TrueSimulation

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles

def oddify (φ : Formula) : Formula :=
  ⟨φ.nvars, if φ.clauses.length % 2 = 1 then φ.clauses else φ.clauses ++ φ.clauses.take 1⟩

theorem oddify_clause_mem (φ : Formula) (C : Finset (Fin φ.nvars)) :
    C ∈ (oddify φ).clauses ↔ C ∈ φ.clauses := by
  change C ∈ (if φ.clauses.length % 2 = 1 then φ.clauses else φ.clauses ++ φ.clauses.take 1) ↔ _
  split_ifs
  · rfl
  · simp only [List.mem_append]
    exact or_iff_left_of_imp (List.mem_of_mem_take)

theorem cnf_clause_congr (φ : Formula) (cs : List (Finset (Fin φ.nvars)))
    (he : ∀ C, C ∈ cs ↔ C ∈ φ.clauses) (U T : Finset (Fin φ.nvars)) (turn : Bool) :
    TrueWins ⟨φ.nvars, cs⟩ U T turn ↔ TrueWins φ U T turn := by
  have hs (T : Finset (Fin φ.nvars)) : Satisfied ⟨φ.nvars, cs⟩ T ↔ Satisfied φ T := by
    unfold Satisfied; simp only [he]
  generalize hn : U.card = n
  induction n using Nat.strong_induction_on generalizing U T turn with
  | h n ih =>
    by_cases hU : U = ∅
    · subst U; rw [cnf_empty, cnf_empty, hs]
    · cases turn
      · rw [cnf_false ⟨φ.nvars, cs⟩ U T hU, cnf_false φ U T hU]
        apply forall_congr'; intro i
        apply forall_congr'; intro hi
        exact ih _ (by have := Finset.card_erase_lt_of_mem hi; omega) _ _ true rfl
      · rw [cnf_true ⟨φ.nvars, cs⟩ U T hU, cnf_true φ U T hU]
        apply exists_congr; intro i
        apply and_congr_right; intro hi
        exact ih _ (by have := Finset.card_erase_lt_of_mem hi; omega) _ _ false rfl

theorem oddify_firstWins (φ : Formula) : FirstWins (oddify φ) ↔ FirstWins φ := by
  exact cnf_clause_congr φ (oddify φ).clauses (oddify_clause_mem φ) _ _ true

theorem oddify_odd (φ : Formula) (hm : φ.clauses ≠ []) :
    (oddify φ).clauses.length % 2 = 1 := by
  simp only [oddify]
  split_ifs with h
  · exact h
  · have hpos : 0 < φ.clauses.length := List.length_pos_iff.mpr hm
    simp only [List.length_append, List.length_take]
    omega

theorem oddify_size (φ : Formula) :
    (oddify φ).clauses.length ≤ φ.clauses.length + 1 := by
  simp only [oddify]
  split_ifs
  · omega
  · simp only [List.length_append, List.length_take]; omega

theorem reduction_correct_nonempty (φ : Formula) (hm : φ.clauses ≠ []) :
    Winning (Construction.graph (oddify φ)) (Construction.board (oddify φ)) ↔ FirstWins φ := by
  constructor
  · intro hw
    by_contra hn
    exact false_strategy (oddify φ) (oddify_odd φ hm)
      (fun ht => hn ((oddify_firstWins φ).mp ht)) hw
  · intro ht
    exact true_strategy (oddify φ) (oddify_odd φ hm) ((oddify_firstWins φ).mpr ht)

theorem labeled_graph_correct (φ : Formula) :
    Winning (Construction.labeledGraph φ).graph Finset.univ ↔
      Winning (Construction.graph φ) (Construction.board φ) := by
  have he (u w : Fin (Construction.size φ)) :
      (Construction.graph φ).Adj u.val w.val ↔ (Construction.labeledGraph φ).graph.Adj u w := by
    simp [Construction.graph, Construction.labeledGraph, SimpleGraph.fromRel_adj, Fin.val_inj]
  have hboard : Construction.board φ = Finset.univ.image (fun i : Fin (Construction.size φ) => i.val) := by
    simp [Construction.board, Finset.image_fin_univ]
  rw [hboard]
  exact (winning_image (Construction.labeledGraph φ).graph (Construction.graph φ)
    (fun i : Fin (Construction.size φ) => i.val) Fin.val_injective he Finset.univ).symm

end Lax689614Proofs
