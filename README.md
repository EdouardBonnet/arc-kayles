# Arc Kayles is PSPACE-complete

Local Lax submission **lax-689614**, based on Édouard Bonnet's manuscript
`../main.pdf`. All theorem statements, including PSPACE-completeness, have
Lean proofs. Nothing has been submitted to the remote archive or registered.

The submission uses the registered, pinned concept packages
[classical complexity, lax-434930](https://github.com/EdouardBonnet/classical-complexity/tree/0c0840319318215fd7b36a9a822b81ce55cf6941)
and [Cook–Levin, lax-429075](https://github.com/EdouardBonnet/cook-levin/tree/905f2da2698d5b38002676f74632aa716e731389).
PSPACE is the former's deterministic work-space class; polynomial many-one
reduction is the latter's `ManyOne`, using an actual polynomial-time Turing
machine on binary words.

## Proof status

All seventeen proofs have passed full Lax validation and independent kernel
replay, with empty computed assumption sets. There are no open theorem
statements. The final hardness and completeness proofs use only `propext`,
`Classical.choice`, and `Quot.sound`.

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
| Schaefer's positive CNF hardness | `PositiveCNFHardness` | Proved via compiled quantified reachability and Byskov's game reduction |
| Theorem 1: PSPACE membership | `Completeness` | Proved with a compiled, halting work-space machine |
| Theorem 1: PSPACE completeness | `Completeness` | Proved |
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

## Proof architecture

Positive-CNF hardness is proved from the archived definition of PSPACE, not
assumed from a citation. A polynomial-space machine's configuration graph is
encoded by a uniformly generated circuit. Quantified repeated squaring uses
one recursive reachability instance per level; explicit alignment constraints
select either half of the path. The circuit has a checked quantifier layout
and wire bounds. The pinned Cook–Levin gate proofs convert it to quantified
CNF, and block-quantifier normalization gives an alternating-CNF game.

Byskov's strategy-preserving gadgets convert that game to True-first positive
CNF. Their proofs handle every deviation, not only intended play. Both the
machine-to-alternating-CNF and alternating-CNF-to-positive-CNF word maps have
compiled polynomial-time Turing-machine witnesses. The former includes a
verified traversal of the archived CNF encoding; the latter handles malformed
input words as well as valid formulas.

The paper's Arc Kayles reduction is proved through the Sprague–Grundy results,
the pass lemma, the deviation analysis, and both strategy transfers, including
True's endgame. Its word map likewise has a polynomial-time machine witness,
compiled from header validation, clause normalization, and adjacency-matrix
generation.

PSPACE membership uses a terminating depth-first search with a cubically
bounded encoded stack. Each transition is compiled, its temporary workspace
is cleared, and the archived stack-to-tape compiler supplies a deterministic
machine with a polynomial work-space bound.

The final completeness proof composes these results using
`Lax434930Proofs.PolynomialComposition.comp`. The pinned mathlib's similarly
named `proof_wanted` declaration and unproved archived concept statements are
not used as proof dependencies.

Review entry points:

- [Positive-CNF hardness](proofs/Lax689614Proofs/PositiveCNFHardness.lean)
- [Compiled source reduction](proofs/Lax689614Proofs/SpaceReductionCode.lean)
- [Quantified machine-CNF correctness](proofs/Lax689614Proofs/MachineCNF.lean)
- [Arc Kayles completeness](proofs/Lax689614Proofs/Completeness.lean)

The build's advisory warnings concern proof-package dependencies and unused
helpers (including generated constructor lemmas). Proof-package dependencies
are intentional: they reuse the archived compiler and circuit proofs. The
separate closed-QBF semantic construction and size lemmas are retained for
review even where the final uniform compiler uses its numeric counterpart.

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
17 proofs, all with empty computed assumption sets. The build reports 139
advisory warnings of the kinds explained above, and no errors.
The manuscript's SHA-256 is
`94517c7d6ac1909f101e8485a0eb53fc0c7da415b8496c2950e532cea63b8ad0`.
