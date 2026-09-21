import Lax689614Proofs.ByskovMatrix
import Lax689614Proofs.HeaderCode

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Byskov

open Lax434930Proofs.InclusionAux.TimeHelpers.Streaming
open Lax434930.PolynomialTime

def controlTest {I : Type} (r k u : Number I) : Test I :=
  (Test.lt u ((Number.constant 9).mul r)).and
    ((Test.lt (u.div (.constant 9)) k).and
      ((Test.eq (u.mod (.constant 9)) (.constant 2)).or
        (Test.eq (u.mod (.constant 9)) (.constant 4))))

theorem controlTest_value {I : Type} (r k u : Number I) (a : I → Word) :
    (controlTest r k u).value a = true ↔ priorControl (r.value a) (k.value a) (u.value a) := by
  simp [controlTest, priorControl, Test.and, Test.or, Test.lt, Test.eq_value,
    Number.mul, Number.div, Number.mod, Number.constant]

noncomputable def localIndexTest {I : Type} (j u : Number I) : Test I :=
  Test.anyFinite (fun t : Fin 9 => (Test.eq j (.constant t.val)).and
    (Test.anyList (localIndices t.val).toList (fun v => Test.eq u (.constant v))))

theorem localIndexTest_value {I : Type} (j u : Number I) (a : I → Word) :
    (localIndexTest j u).value a = true ↔ u.value a ∈ localIndices (j.value a) := by
  simp only [localIndexTest, Test.anyFinite_true, Test.and, Bool.and_eq_true,
    Test.anyList_true, Test.eq_value, decide_eq_true_eq, Number.constant, Finset.mem_toList]
  constructor
  · rintro ⟨t, ht, v, hv, he⟩
    simpa [ht, he] using hv
  · intro hu
    have hj : j.value a < 9 := by
      by_contra hj
      have hn : localClauses[j.value a]? = none := List.getElem?_eq_none (by simpa [localClauses] using Nat.le_of_not_gt hj)
      simp [localIndices, hn] at hu
    exact ⟨⟨j.value a, hj⟩, rfl, u.value a, hu, rfl⟩

noncomputable def localTest {I : Type} (r i j u : Number I) : Test I :=
  (Test.lt u ((Number.constant 9).mul r)).and
    ((Test.eq (u.div (.constant 9)) i).and (localIndexTest j (u.mod (.constant 9))))

theorem localTest_value {I : Type} (r i j u : Number I) (a : I → Word) :
    (localTest r i j u).value a = true ↔ localCell (r.value a) (i.value a) (j.value a) (u.value a) := by
  simp only [localTest, Test.and, Bool.and_eq_true, Test.lt, Test.eq_value, decide_eq_true_eq,
    Number.mul, Number.constant, Number.div, Number.mod, localIndexTest_value,
    localCell]

def literalOffset (kind sign : Bool) : ℕ := (if kind then 2 else 0) + (if sign then 1 else 0)

def literalVertex (kind sign : Bool) : Vertex := if kind then .y sign else .x sign

noncomputable def literalTest {I : Type} (r : Number I) (bits : I) (j u : Number I) : Test I :=
  Test.exists r (Test.anyFinite fun kb : Bool × Bool =>
    (Test.eq (u.rename some)
      (((Number.constant 9).mul (.length none)).add (.constant (literalVertex kb.1 kb.2).index))).and
    (Test.input (some bits)
      ((((j.rename some).mul ((Number.constant 4).mul (r.rename some))).add
        ((Number.constant 4).mul (.length none))).add (.constant (literalOffset kb.1 kb.2)))))

theorem literalTest_value {I : Type} (r : Number I) (bits : I) (j u : Number I) (a : I → Word) :
    (literalTest r bits j u).value a = true ↔ literalCell (r.value a) (a bits) (j.value a) (u.value a) := by
  simp only [literalTest, Test.exists_true, Test.anyFinite_true, Test.and, Bool.and_eq_true,
    Test.eq_value, Test.input, decide_eq_true_eq, Number.rename, Number.add, Number.mul, Number.constant,
    Number.length, extend, Option.elim_none, Option.elim_some, List.length_replicate, Function.comp_def]
  have hb (v : Option Bool) : v.getD false = true ↔ v = some true := by cases v with
    | none => simp
    | some b => cases b <;> simp
  simp only [hb]
  constructor
  · rintro ⟨i, hi, ⟨k, b⟩, hu, hbit⟩
    let l : SignedLiteral (r.value a) := ⟨⟨i, hi⟩, k, b⟩
    have hnode : l.node.val = u.value a := by simpa [l, SignedLiteral.node, SignedLiteral.vertex,
      literalVertex, node] using hu.symm
    refine ⟨?_, l, hnode, ?_⟩
    · rw [← hnode]; exact node_lt l.round l.vertex
    · simpa [l, SignedLiteral.index, literalOffset, Nat.add_assoc] using hbit
  · rintro ⟨_, ⟨i, k, b⟩, hu, hbit⟩
    refine ⟨i.val, i.isLt, (k, b), ?_, ?_⟩
    · simpa [SignedLiteral.node, SignedLiteral.vertex, literalVertex, node] using hu.symm
    · simpa [SignedLiteral.index, literalOffset, Nat.add_assoc] using hbit

end Lax689614Proofs.Byskov
