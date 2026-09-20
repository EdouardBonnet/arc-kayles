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

All eight completed proofs have empty Lax assumption sets: they use only the
archive's allowed background axioms, not any open concept statements.

| Paper result | Concept module | Status |
| --- | --- | --- |
| Observation 2: smaller values reachable, current value unreachable | `GrundyProperties` | Both proved |
| Lemma 3: losing iff value zero | `GrundyProperties` | Proved |
| Lemma 4: xor on disjoint unions | `GrundyProperties` | Proved for two components; iterate for a finite family |
| Lemma 5: passes and either truth value | `Passes` | Statement only |
| Lemma 6: biclique with private neighbors | `Biclique` | Proved, including empty sides |
| Claim 7: deviations lose | `RegularPlay` | Statement only |
| Claim 8: exceptional move parity | `RegularPlay` | Statement only |
| Claims 9 and 10: transfer winning strategies | `Reduction` | Statements only |
| Polynomial-time many-one reduction | `Reduction` | Statement only |
| Schaefer's positive CNF hardness | `PositiveCNFHardness` | Statement only |
| Theorem 1: membership and completeness | `Completeness` | Statements only |
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

1. Prove the finite pass lemma by strategy simulation, including monotonicity
   under additional variables assigned to the player whose strategy is being
   followed.
2. Derive the residual-graph invariants from `RegularPlay.Reachable`. Apply the
   proved biclique and disjoint-union results to establish Claims 7 and 8.
3. Transfer False's and True's strategies. Formalize True's final invariant:
   even remaining `r`, odd remaining `q`, `r < q`, and a protected surviving
   literal neighbor for each remaining clause vertex.
4. Construct total parsers and the binary-word reduction. Duplicate a clause
   for positive even clause counts; map empty conjunctions to a fixed winning
   graph and invalid words to a fixed losing graph. Prove outcome preservation
   and supply the actual `TM2ComputableInPolyTime` witness. The size bounds
   already proved do not by themselves establish polynomial running time.
5. Prove positive CNF hardness from polynomial-space computation, e.g. through
   quantified formulas and Schaefer's strategy-preserving construction.
   Cook–Levin provides reductions and useful encodings, but NP-hardness alone
   does not supply this alternating-game argument. No corresponding archived
   QBF/positive-CNF hardness theorem was found in the local archive snapshot.
6. Implement the polynomial-space game-tree decider in the imported
   `SpaceMachines` model and prove its work-space bound. Prove any needed
   composition facts for polynomial reductions and assemble completeness.
   In the pinned mathlib, `TM2ComputableInPolyTime.comp` is marked
   `proof_wanted`; it must not be treated as an available checked proof.

These steps remain part of the requested full formalization. The present
proof package completes the Sprague–Grundy part, not the complexity theorem.

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

Validation on 2026-09-21: `lax build . --replay` passed, inspecting 14 concepts
and eight proofs and successfully replaying the kernel proofs. There are
nine open statements. The manuscript's SHA-256 is
`94517c7d6ac1909f101e8485a0eb53fc0c7da415b8496c2950e532cea63b8ad0`.
