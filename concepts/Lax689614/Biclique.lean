import Lax689614.Grundy

/-!
---
title: Bicliques with pendant neighbors
type: theorem
---
Lemma 6. Partition the surviving vertices into sets $L,R,I$. The sets
$L$ and $R$ induce a complete bipartite graph, $I$ is independent, and
each vertex of $L\cup R$ has a neighbor in $I$ whose only surviving
neighbor is that vertex. Other edges between $L\cup R$ and $I$ are
unrestricted. The value is
$g(|L|,|R|)=(|L|+|R|)\bmod 2+2(\min(|L|,|R|)\bmod 2)$.
Either side of the biclique may be empty.
-/

namespace Lax689614.Biclique

def g (a b : ℕ) : ℕ := (a + b) % 2 + 2 * (min a b % 2)

structure Partition {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S L R I : Finset V) : Prop where
  cover : S = L ∪ R ∪ I
  left_right : Disjoint L R
  left_independent : Disjoint L I
  right_independent : Disjoint R I
  left_stable : ∀ u ∈ L, ∀ v ∈ L, ¬ G.Adj u v
  right_stable : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v
  independent_stable : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v
  complete : ∀ u ∈ L, ∀ v ∈ R, G.Adj u v
  pendant : ∀ u ∈ L ∪ R, ∃ v ∈ I, G.Adj u v ∧
    ∀ w ∈ S, G.Adj v w → w = u

axiom value_eq {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S L R I : Finset V) (h : Partition G S L R I) :
    Grundy.value G S = g L.card R.card

end Lax689614.Biclique
