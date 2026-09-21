# Arc Kayles is PSPACE-complete

Local Lax submission **lax-689614**, based on Édouard Bonnet's manuscript
`../main.pdf`. This is work in progress. The PSPACE-completeness theorem is
stated but **not yet proved**. Nothing has been submitted to the remote archive
or registered.

The submission uses the registered, pinned concept packages
[classical complexity, lax-434930](https://github.com/EdouardBonnet/classical-complexity/tree/0c0840319318215fd7b36a9a822b81ce55cf6941)
and [Cook–Levin, lax-429075](https://github.com/EdouardBonnet/cook-levin/tree/905f2da2698d5b38002676f74632aa716e731389).
PSPACE is the former's deterministic work-space class; polynomial many-one
reduction is the latter's `ManyOne`, using an actual polynomial-time Turing
machine on binary words.

## Proof status

All fifteen completed proofs have passed kernel replay and have empty Lax
assumption sets: they use only the archive's allowed background axioms, not
any open concept statements.

| Paper result | Concept module | Status |
| --- | --- | --- |
| Observation 2: smaller values reachable, current value unreachable | `GrundyProperties` | Both proved |
| Lemma 3: losing iff value zero | `GrundyProperties` | Proved |
| Lemma 4: xor on disjoint unions | `GrundyProperties` | Proved for two components; iterate for a finite family |
| Lemma 5: passes and either truth value | `Passes` | Proved |
| Lemma 6: biclique with private neighbors | `Biclique` | Proved, including empty sides |
| Claim 7: deviations lose | `RegularPlay` | Proved |
| Claim 8: exceptional move parity | `RegularPlay` | Proved |
| Claims 9 and 10: transfer winning strategies | `Reduction` | Both proved |
| Polynomial-time many-one reduction | `Reduction` | Proved with a compiled Turing-machine witness |
| Schaefer's positive CNF hardness | `PositiveCNFHardness` | Statement only |
| Theorem 1: PSPACE membership | `Completeness` | Proved with a compiled, halting work-space machine |
| Theorem 1: PSPACE completeness | `Completeness` | Awaiting positive CNF hardness |
| Exact encoding lengths and reduction vertex count | `Sizes` | All three proved |

Concept axioms are the archive's mechanism for declaring proof obligations.
An axiom's presence does not certify it. The proof package contains no
`sorry`, `admit`, or added axioms.

## Definitions and conventions

`ArcKayles` defines normal-play winning positions independently of
`Grundy.value`; both recursions decrease the number of surviving vertices.
Graphs are simple and undirected. Isolated vertices remain in the board and
cannot be played. Legal edges are represented by ordered endpoint pairs;
reversing the pair produces the same position.

`PositiveCNF` allows empty clauses, empty conjunctions, and unused variables.
`Passes` states the finite version of the paper's lemma with a shared pass
budget. This excludes infinite passing and covers the reduction's finite
pass supply. Its statement covers intermediate disjoint assigned/unassigned
positions and either player's turn.

`Encoding` specifies unary size prefixes followed by full row-major matrices.
Malformed strings do not belong to either decision language. `Construction`
uses consecutive numerical blocks for the paper's named vertices, with
exactly `13*n + 4*m + 18` vertices. `RegularPlay` defines reachability by actual
legal assignment/pass moves, rather than assuming arbitrary residual
positions have the required invariants.

The folder contains only a source PDF, not the author's LaTeX sources. No
`paper` entry is declared in the manifest, since Lax's paper integration
requires LaTeX sources.

## Remaining proof work

1. Prove positive CNF hardness from polynomial-space computation, e.g. through
   quantified formulas and Schaefer's strategy-preserving construction.
   Cook–Levin provides reductions and useful encodings, but NP-hardness alone
   does not supply this alternating-game argument. No corresponding archived
   QBF/positive-CNF hardness theorem was found in the local archive snapshot.
   The auxiliary proof now includes a size-controlled quantified reachability
   construction, a truth-preserving conversion to quantified CNF using the
   pinned Cook–Levin circuit proofs, and Byskov's full strategy-preserving
   reduction from alternating quantified CNF to the True-first positive CNF
   game. Its round proof handles all deviations and composes across rounds.
   Block-quantifier normalization and the complete closed-QBF-to-game semantic
   translation are also proved. The alternating-CNF-to-positive-CNF binary
   reduction has a compiled polynomial-time Turing-machine witness, including
   malformed-input handling. Encoded machine configurations are now connected
   to the quantified formulas: `machineFormula_positive` proves that an
   arbitrary space-bounded machine accepts exactly when the resulting game
   is winning. Compiling this source-to-formula transformation with a
   polynomial-time certificate is still required for PSPACE-hardness.
2. Assemble completeness from positive CNF hardness, the proved reduction,
   and the proved PSPACE membership. Polynomial reduction composition is supplied
   by `Lax434930Proofs.PolynomialComposition.comp` in the registered classical
   complexity submission; the pinned mathlib's similarly named
   `proof_wanted` declaration is not used.

These steps remain part of the requested full formalization. The present
proof package completes the Sprague–Grundy results, the pass lemma, the
deviation analysis, and both strategy transfers, including True's endgame.
The binary-word reduction also has a genuine polynomial-time machine
witness, compiled from header validation, clause normalization, and matrix
generation. PSPACE membership is also proved: a validated graph is evaluated
by a terminating depth-first search with a cubically bounded encoded stack.
Each transition is compiled, its temporary workspace is cleared, and the
archived stack-to-tape compiler supplies a deterministic machine with a
polynomial work-space bound. Positive-CNF hardness remains open; completeness
will then follow by the proved reduction-composition lemma.

## Validation and preview

From this directory:

```sh
lax build .
lax build . --replay
lax serve .
```

`build-output.json` is generated and ignored. It records the validated
statements, proofs, and exact computed assumption sets. No remote publication
is needed for local validation and preview.

Validation on 2026-09-21: `lax build . --replay` passed with 14 concepts and
fifteen proofs, all with empty computed assumption sets. This includes
both strategy transfers, the polynomial-time reduction, and PSPACE membership. There are two
open statements. The manuscript's SHA-256 is
`94517c7d6ac1909f101e8485a0eb53fc0c7da415b8496c2950e532cea63b8ad0`.
