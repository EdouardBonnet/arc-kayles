import Lax689614Proofs.GraphEncoding
import Lax689614Proofs.ParserLengths

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs

open Lax689614 Encoding
open scoped Classical

def matrixRow {n : ℕ} (cs : List (Finset (Fin n))) (u : Fin n) : Finset (Fin n) :=
  cs[u.val]?.getD ∅

def GraphRowsValid {n : ℕ} (cs : List (Finset (Fin n))) : Prop :=
  cs.length = n ∧ (∀ u, u ∉ matrixRow cs u) ∧
    ∀ u v, v ∈ matrixRow cs u ↔ u ∈ matrixRow cs v

def matrixGraph (n : ℕ) (cs : List (Finset (Fin n))) : Graph :=
  ⟨n, SimpleGraph.fromRel fun u v => v ∈ matrixRow cs u⟩

theorem graphRows_get (G : Graph) (u : Fin G.vertices) :
    matrixRow (graphRows G) u = Finset.univ.filter (G.graph.Adj u) := by
  simp [matrixRow, graphRows, List.getElem?_eq_getElem, u.isLt]

theorem graphRows_valid (G : Graph) : GraphRowsValid (graphRows G) := by
  refine ⟨graphRows_length G, ?_, ?_⟩
  · intro u; simp [graphRows_get]
  · intro u v; simp only [graphRows_get, Finset.mem_filter, Finset.mem_univ, true_and]
    exact G.graph.adj_comm u v

theorem matrixGraph_adj {n : ℕ} (cs : List (Finset (Fin n))) (h : GraphRowsValid cs) (u v : Fin n) :
    (matrixGraph n cs).graph.Adj u v ↔ v ∈ matrixRow cs u := by
  change (u ≠ v ∧ (v ∈ matrixRow cs u ∨ u ∈ matrixRow cs v)) ↔ _
  constructor
  · rintro ⟨_, hv | hu⟩
    · exact hv
    · exact (h.2.2 u v).mpr hu
  · intro hv
    refine ⟨?_, Or.inl hv⟩
    rintro rfl
    exact h.2.1 u hv

theorem matrixGraph_graphRows (G : Graph) : matrixGraph G.vertices (graphRows G) = G := by
  cases G with
  | mk n g =>
    have he : (matrixGraph n (graphRows ⟨n, g⟩)).graph = g := by
      ext u v
      rw [matrixGraph_adj _ (graphRows_valid ⟨n, g⟩), graphRows_get]
      simp
    exact congrArg (Graph.mk n) he

theorem graphRows_matrixGraph {n : ℕ} (cs : List (Finset (Fin n))) (h : GraphRowsValid cs) :
    graphRows (matrixGraph n cs) = cs := by
  apply List.ext_getElem
  · rw [graphRows_length]; exact h.1.symm
  · intro j hj hj'
    have hjn : j < n := h.1 ▸ hj'
    have hr := graphRows_get (matrixGraph n cs) ⟨j, hjn⟩
    change matrixRow (graphRows (matrixGraph n cs)) ⟨j, hjn⟩ = _ at hr
    have hget : matrixRow (graphRows (matrixGraph n cs)) ⟨j, hjn⟩ =
        (graphRows (matrixGraph n cs))[j] := by
      simp [matrixRow, List.getElem?_eq_getElem, hj]
    rw [hget] at hr
    rw [hr]
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, matrixGraph_adj cs h]
    simp [matrixRow, List.getElem?_eq_getElem, hj']
    rfl

noncomputable def parseGraph (w : List Bool) : Option Graph := do
  let (n, bits) ← readUnary w
  let (cs, rest) ← readClauses n n bits
  if rest = [] ∧ GraphRowsValid cs then some (matrixGraph n cs) else none

theorem parseGraph_word (G : Graph) : parseGraph (graphWord G) = some G := by
  have hc : readClauses G.vertices G.vertices ((graphRows G).flatMap clauseBits) =
      some (graphRows G, []) := by
    simpa only [graphRows_length, List.append_nil] using readClauses_prefix (graphRows G) []
  simp [parseGraph, graphWord_rows, readUnary_prefix, hc, graphRows_valid, matrixGraph_graphRows]

theorem parseGraph_sound {w : List Bool} {G : Graph} (hp : parseGraph w = some G) : graphWord G = w := by
  simp only [parseGraph, bind, Option.bind_eq_some_iff] at hp
  obtain ⟨⟨n, bits⟩, hn, ⟨⟨cs, rest⟩, hcs, hout⟩⟩ := hp
  dsimp only at hcs hout
  split_ifs at hout with hv
  obtain ⟨rfl, hv⟩ := hv
  cases hout
  rw [graphWord_rows, graphRows_matrixGraph cs hv]
  have hs := (readClauses_sound hcs).2
  simp only [List.append_nil] at hs
  rw [← hs]
  exact (readUnary_sound hn).symm

theorem parseGraph_mem (w : List Bool) : w ∈ arcKayles ↔
    ∃ G, parseGraph w = some G ∧ ArcKayles.Winning G.graph Finset.univ := by
  constructor
  · rintro ⟨G, rfl, hw⟩; exact ⟨G, parseGraph_word G, hw⟩
  · rintro ⟨G, hp, hw⟩; exact ⟨G, parseGraph_sound hp, hw⟩

end Lax689614Proofs
