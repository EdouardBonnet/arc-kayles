import Lax689614Proofs.GraphEncoding
import Lax689614Proofs.Sizes

namespace Lax689614Proofs

open Lax689614 PositiveCNF ArcKayles Encoding

def noGraph : Graph := ⟨0, ⊥⟩
def yesGraph : Graph := ⟨2, ⊤⟩

theorem winning_empty {V : Type} [DecidableEq V] (G : SimpleGraph V) : ¬ Winning G ∅ := by
  rw [winning_iff_move]; simp

theorem noGraph_losing : ¬ Winning noGraph.graph Finset.univ := by
  have he : (Finset.univ : Finset (Fin 0)) = ∅ := by ext i; exact Fin.elim0 i
  change ¬ Winning (⊥ : SimpleGraph (Fin 0)) Finset.univ
  rw [he]; exact winning_empty _

theorem yesGraph_winning : Winning yesGraph.graph Finset.univ := by
  change Winning (⊤ : SimpleGraph (Fin 2)) Finset.univ
  apply (winning_iff_move _ _).mpr
  refine ⟨0, Finset.mem_univ _, 1, Finset.mem_univ _, by decide, ?_⟩
  have he : remove (Finset.univ : Finset (Fin 2)) 0 1 = ∅ := by decide
  rw [he]; exact winning_empty _

noncomputable def reduceWord (w : List Bool) : List Bool :=
  match parseFormula w with
  | none => graphWord noGraph
  | some φ => if φ.clauses = [] then graphWord yesGraph
      else graphWord (Construction.labeledGraph (oddify φ))

theorem formulaWord_mem (φ : Formula) : formulaWord φ ∈ positiveCNF ↔ FirstWins φ := by
  constructor
  · rintro ⟨ψ, he, hw⟩
    exact formulaWord_injective he ▸ hw
  · intro hw; exact ⟨φ, rfl, hw⟩

theorem empty_conjunction_wins (φ : Formula) (h : φ.clauses = []) : FirstWins φ := by
  apply cnf_of_satisfied
  intro C hC
  simp [h] at hC

theorem reduceWord_correct (w : List Bool) :
    w ∈ positiveCNF ↔ reduceWord w ∈ arcKayles := by
  classical
  cases hp : parseFormula w with
  | none =>
    have hn : w ∉ positiveCNF := by
      rintro ⟨φ, rfl, _⟩
      rw [parseFormula_word] at hp
      contradiction
    simp [reduceWord, hp, graphWord_mem, noGraph_losing, hn]
  | some φ =>
    have hw := parseFormula_sound hp
    have hmem : w ∈ positiveCNF ↔ FirstWins φ := hw ▸ formulaWord_mem φ
    rw [hmem]
    by_cases hc : φ.clauses = []
    · simp [reduceWord, hp, hc, graphWord_mem, yesGraph_winning, empty_conjunction_wins φ hc]
    · simp only [reduceWord, hp, hc, ↓reduceIte, graphWord_mem]
      exact ((labeled_graph_correct (oddify φ)).trans (reduction_correct_nonempty φ hc)).symm

theorem reduceWord_length_bound (w : List Bool) :
    (reduceWord w).length ≤ (17 * w.length + 22) ^ 2 + (17 * w.length + 22) + 1 := by
  classical
  cases hp : parseFormula w with
  | none => simp [reduceWord, hp, Sizes.graph_length, noGraph]
  | some φ =>
    have hw := parseFormula_sound hp
    have hlen := Sizes.formula_length φ
    rw [hw] at hlen
    by_cases hc : φ.clauses = []
    · simp [reduceWord, hp, hc, Sizes.graph_length, yesGraph]
      nlinarith [sq_nonneg (17 * (w.length : ℤ) + 22)]
    · simp only [reduceWord, hp, hc, ↓reduceIte, Sizes.graph_length, Construction.labeledGraph]
      have hcsize := Sizes.construction_size (oddify φ)
      have hodd := oddify_size φ
      change Construction.size (oddify φ) =
        13 * φ.nvars + 4 * (oddify φ).clauses.length + 18 at hcsize
      have hs : Construction.size (oddify φ) ≤ 17 * w.length + 22 := by omega
      nlinarith [Nat.mul_self_le_mul_self hs]

end Lax689614Proofs
