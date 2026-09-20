import Lax689614.Encoding

/-!
---
title: The reduction graph
type: definition
---
For a formula with $n$ variables and $m$ clauses, put $K=4n+6$ and
$R=m+2n+2$. The vertices are $s,t$, $a_j,b_j$ for clauses,
$v_i,t_i$ for $0\leq i<R$, $f_i$ for variables, and $y_i,z_i$
for $0\leq i<K$. The edges are $st$, $sa_j$, $a_jb_j$, all $b_jv_i$,
$v_it_i$, $v_if_i$ for $i<n$, $b_jf_i$ when $x_i\in C_j$,
and $sy_i,y_iz_i$. Labels use consecutive blocks in the displayed order.
The correctness statements assume an odd number of clauses.
-/

namespace Lax689614.Construction

open PositiveCNF

def K (φ : Formula) : ℕ := 4 * φ.nvars + 6
def R (φ : Formula) : ℕ := φ.clauses.length + 2 * φ.nvars + 2
def size (φ : Formula) : ℕ := 2 + 2 * φ.clauses.length + 2 * R φ + φ.nvars + 2 * K φ

def s : ℕ := 0
def t : ℕ := 1
def a (_φ : Formula) (j : ℕ) : ℕ := 2 + j
def b (φ : Formula) (j : ℕ) : ℕ := 2 + φ.clauses.length + j
def v (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + i
def vt (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + R φ + i
def f (φ : Formula) (i : ℕ) : ℕ := 2 + 2 * φ.clauses.length + 2 * R φ + i
def y (φ : Formula) (i : ℕ) : ℕ :=
  2 + 2 * φ.clauses.length + 2 * R φ + φ.nvars + i
def z (φ : Formula) (i : ℕ) : ℕ :=
  2 + 2 * φ.clauses.length + 2 * R φ + φ.nvars + K φ + i

def Edge (φ : Formula) (u w : ℕ) : Prop :=
  (u = s ∧ w = t) ∨
  (∃ j < φ.clauses.length, u = s ∧ w = a φ j) ∨
  (∃ j < φ.clauses.length, u = a φ j ∧ w = b φ j) ∨
  (∃ j < φ.clauses.length, ∃ i < R φ, u = b φ j ∧ w = v φ i) ∨
  (∃ i < R φ, u = v φ i ∧ w = vt φ i) ∨
  (∃ i < φ.nvars, u = v φ i ∧ w = f φ i) ∨
  (∃ j : Fin φ.clauses.length, ∃ i ∈ φ.clauses[j],
    u = b φ j ∧ w = f φ i) ∨
  (∃ i < K φ, u = s ∧ w = y φ i) ∨
  (∃ i < K φ, u = y φ i ∧ w = z φ i)

def graph (φ : Formula) : SimpleGraph ℕ := SimpleGraph.fromRel (Edge φ)

def board (φ : Formula) : Finset ℕ := Finset.range (size φ)

def labeledGraph (φ : Formula) : Encoding.Graph where
  vertices := size φ
  graph := SimpleGraph.fromRel fun u v : Fin (size φ) => Edge φ u.val v.val

end Lax689614.Construction
