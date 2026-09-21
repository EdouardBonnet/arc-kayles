import Lax689614Proofs.CodeComputer
import Lax689614Proofs.MatrixBits

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.MachineCode

open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930.PolynomialTime

def pairTest {I : Type} (u w x y : Number I) : Test I :=
  (Test.eq u x).and (Test.eq w y)

def edgeTest {I : Type} (n m : Number I) (bits : I) (u w : Number I) : Test I :=
  let r := (m.add ((Number.constant 2).mul n)).add (.constant 2)
  let k := ((Number.constant 4).mul n).add (.constant 6)
  let b := (Number.constant 2).add m
  let v := (Number.constant 2).add ((Number.constant 2).mul m)
  let vt := v.add r
  let f := vt.add r
  let y := f.add n
  let z := y.add k
  let tests : List (Test I) := [
    pairTest u w (.constant 0) (.constant 1),
    Test.exists m (pairTest (u.rename some) (w.rename some) (.constant 0)
      ((Number.constant 2).add (.length none))),
    Test.exists m (pairTest (u.rename some) (w.rename some)
      ((Number.constant 2).add (.length none)) ((b.rename some).add (.length none))),
    Test.exists m (Test.exists (r.rename some)
      (pairTest (u.rename (some ∘ some)) (w.rename (some ∘ some))
        ((b.rename (some ∘ some)).add (.length (some none)))
        ((v.rename (some ∘ some)).add (.length none)))),
    Test.exists r (pairTest (u.rename some) (w.rename some)
      ((v.rename some).add (.length none)) ((vt.rename some).add (.length none))),
    Test.exists n (pairTest (u.rename some) (w.rename some)
      ((v.rename some).add (.length none)) ((f.rename some).add (.length none))),
    Test.exists m (Test.exists (n.rename some)
      ((Test.input (some (some bits))
        (((Number.length (some none)).mul (n.rename (some ∘ some))).add (.length none))).and
        (pairTest (u.rename (some ∘ some)) (w.rename (some ∘ some))
          ((b.rename (some ∘ some)).add (.length (some none)))
          ((f.rename (some ∘ some)).add (.length none))))),
    Test.exists k (pairTest (u.rename some) (w.rename some) (.constant 0)
      ((y.rename some).add (.length none))),
    Test.exists k (pairTest (u.rename some) (w.rename some)
      ((y.rename some).add (.length none)) ((z.rename some).add (.length none)))
    ]
  tests.foldr Test.or (.constant false)

def rawEdge (n m : ℕ) (bits : Word) (u w : ℕ) : Prop :=
  let r := m + 2 * n + 2
  let k := 4 * n + 6
  let b := 2 + m
  let v := 2 + 2 * m
  let vt := v + r
  let f := vt + r
  let y := f + n
  let z := y + k
  (u = 0 ∧ w = 1) ∨
  (∃ j < m, u = 0 ∧ w = 2 + j) ∨
  (∃ j < m, u = 2 + j ∧ w = b + j) ∨
  (∃ j < m, ∃ i < r, u = b + j ∧ w = v + i) ∨
  (∃ i < r, u = v + i ∧ w = vt + i) ∨
  (∃ i < n, u = v + i ∧ w = f + i) ∨
  (∃ j < m, ∃ i < n, (bits[j * n + i]?).getD false = true ∧ u = b + j ∧ w = f + i) ∨
  (∃ i < k, u = 0 ∧ w = y + i) ∨
  (∃ i < k, u = y + i ∧ w = z + i)

theorem edgeTest_value {I : Type} (n m : Number I) (bits : I) (u w : Number I) (a : I → Word) :
    (edgeTest n m bits u w).value a = true ↔ rawEdge (n.value a) (m.value a) (a bits) (u.value a) (w.value a) := by
  simp only [edgeTest, List.foldr_cons, List.foldr_nil, Test.or,
    Test.constant, Bool.or_false, Bool.or_eq_true, id_eq, Test.exists_true, pairTest, Test.and, Bool.and_eq_true,
    Test.eq_value, decide_eq_true_eq, Number.add, Number.mul, Number.constant,
    Number.rename, Number.length, Test.input, extend_some, extend_two_some,
    extend, Option.elim_none, Option.elim_some, List.length_replicate, rawEdge]

theorem rawEdge_construction (φ : Lax689614.PositiveCNF.Formula) (u w : ℕ) :
    rawEdge φ.nvars φ.clauses.length (φ.clauses.flatMap clauseBits) u w ↔
      Lax689614.Construction.Edge φ u w := by
  have hf (j : ℕ) (hj : j < φ.clauses.length) (i : ℕ) (hi : i < φ.nvars) :
      ((φ.clauses.flatMap clauseBits)[j * φ.nvars + i]?).getD false = true ↔
        (⟨i, hi⟩ : Fin φ.nvars) ∈ φ.clauses[j] := by
    rw [clausesBits_get φ.clauses ⟨j, hj⟩ ⟨i, hi⟩]
    simp
  have hLit (B F : ℕ) :
      (∃ j < φ.clauses.length, ∃ i < φ.nvars,
        ((φ.clauses.flatMap clauseBits)[j * φ.nvars + i]?).getD false = true ∧
        u = B + j ∧ w = F + i) ↔
      (∃ j : Fin φ.clauses.length, ∃ i ∈ φ.clauses[j], u = B + j.val ∧ w = F + i.val) := by
    constructor
    · rintro ⟨j, hj, i, hi, hbit, hu, hw⟩
      exact ⟨⟨j, hj⟩, ⟨i, hi⟩, (hf j hj i hi).mp hbit, hu, hw⟩
    · rintro ⟨j, i, hi, hu, hw⟩
      exact ⟨j.val, j.isLt, i.val, i.isLt, (hf j.val j.isLt i.val i.isLt).mpr hi, hu, hw⟩
  open Lax689614.Construction in
  simp only [rawEdge, Edge, s, t, a, b, v, vt, f, y, z, R, K]
  rw [hLit]
  ring_nf

end Lax689614Proofs.MachineCode
