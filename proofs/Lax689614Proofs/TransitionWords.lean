import Lax689614Proofs.FrameDecoding
import Lax689614Proofs.HeaderCode

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.DepthFirst

open Lax689614 Encoding

def bit (w : List Bool) (i : ℕ) : Bool := w[i]?.getD false

def clearPair (n u v : ℕ) (w : List Bool) : List Bool :=
  (List.range n).map fun i => bit w i && !(decide (i = u)) && !(decide (i = v))

def rawFrame (fuel count : ℕ) (board : List Bool) : List Bool :=
  List.replicate fuel true ++ false :: (List.replicate count true ++ false :: board)

def nextBody (n fuel count : ℕ) (graph state frames boardRest : List Bool) : List Bool :=
  let board := boardRest.take n
  let rest := boardRest.drop n
  let j := n * n - count
  let u := j / n
  let v := j % n
  let parent := rawFrame fuel (count - 1) board ++ rest
  if bit state 0 then
    if bit state 1 then [false, false] ++ frames else [true, true] ++ rest
  else if fuel = 0 ∨ count = 0 then [true, false] ++ rest
  else if bit boardRest u && bit boardRest v && bit graph (n + 1 + j) then
    [false, false] ++ rawFrame (fuel - 1) (n * n) (clearPair n u v boardRest) ++ parent
  else [false, false] ++ parent

def nextWord (graph state : List Bool) : List Bool :=
  let n := (graph.takeWhile id).length
  let frames := state.drop 2
  let fuel := (frames.takeWhile id).length
  let afterFuel := frames.drop (fuel + 1)
  let count := (afterFuel.takeWhile id).length
  let boardRest := afterFuel.drop (count + 1)
  nextBody n fuel count graph state frames boardRest

theorem clauseBits_bit {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (rest : List Bool) :
    bit (clauseBits S ++ rest) i.val = decide (i ∈ S) := by
  unfold bit
  rw [List.getElem?_append_left (by simpa [clauseBits_length] using i.isLt), clauseBits_get]
  rfl

theorem clearPair_clause {n : ℕ} (S : Finset (Fin n)) (u v : Fin n) (rest : List Bool) :
    clearPair n u.val v.val (clauseBits S ++ rest) = clauseBits (ArcKayles.remove S u v) := by
  rw [clearPair, ← MachineCode.map_finRange_val n, List.map_map]
  apply List.map_congr_left
  intro i hi
  change (bit (clauseBits S ++ rest) i.val && !decide (i.val = u.val) &&
    !decide (i.val = v.val)) = decide (i ∈ ArcKayles.remove S u v)
  rw [clauseBits_bit]
  apply Bool.eq_iff_iff.mpr
  simp [remove_mem, Fin.val_inj, and_comm, and_left_comm, and_assoc]

theorem graphWord_bit (G : Graph) (u v : Fin G.vertices) :
    bit (graphWord G) (G.vertices + 1 + (u.val * G.vertices + v.val)) =
      @decide (G.graph.Adj u v) (Classical.propDecidable _) := by
  classical
  rw [graphWord_rows]
  unfold bit
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate, List.getElem?_cons_succ]
  have he : G.vertices + 1 + (u.val * G.vertices + v.val) - G.vertices =
      u.val * G.vertices + v.val + 1 := by omega
  rw [he, List.getElem?_cons_succ]
  have hj : u.val < (graphRows G).length := by simpa [graphRows_length] using u.isLt
  rw [clausesBits_get (graphRows G) ⟨u.val, hj⟩ v]
  have hr := graphRows_get G u
  simp only [matrixRow, List.getElem?_eq_getElem, hj, Option.getD_some] at hr
  simp [hr]

theorem graphWord_leading (G : Graph) : ((graphWord G).takeWhile id).length = G.vertices := by
  rw [graphWord_rows, takeWhile_unary_prefix]
  simp

theorem drop_unary (n : ℕ) (w : List Bool) :
    (List.replicate n true ++ false :: w).drop (n + 1) = w := by
  simp [List.drop_append]

theorem nextWord_frame (G : Graph) (f : Frame G.vertices) (fs : List (Frame G.vertices))
    (mode result : Bool) :
    nextWord (graphWord G) ([mode, result] ++ (f :: fs).flatMap frameWord) =
      nextBody G.vertices f.fuel f.todo.length (graphWord G)
        ([mode, result] ++ (f :: fs).flatMap frameWord)
        ((f :: fs).flatMap frameWord) (clauseBits f.board ++ fs.flatMap frameWord) := by
  simp only [nextWord, graphWord_leading, List.drop_succ_cons, List.drop_zero, List.nil_append,
    List.flatMap_cons, frameWord, List.append_assoc, List.cons_append,
    takeWhile_unary_prefix, List.length_replicate, drop_unary]

theorem nextWord_step (G : Graph) [DecidableRel G.graph.Adj]
    {s t : State G.vertices} (h : Step G.graph s t) (hs : s.Good) :
    nextWord (graphWord G) (stateWord s) = stateWord t := by
  cases h with
  | zero S es rest =>
    rw [stateWord, nextWord_frame]
    simp [nextBody, bit, stateWord, clauseBits_length]
  | exhausted S fuel rest =>
    rw [stateWord, nextWord_frame]
    simp [nextBody, bit, stateWord, clauseBits_length]
  | childWins parent rest =>
    change nextWord (graphWord G) ([true, true] ++ (parent :: rest).flatMap frameWord) = _
    rw [nextWord_frame]
    simp [nextBody, bit, stateWord]
  | childLoses parent rest =>
    rw [stateWord, nextWord_frame]
    simp [nextBody, bit, stateWord, clauseBits_length]
  | skip S e es fuel rest he =>
    have hf := hs _ List.mem_cons_self
    have hidx := todo_head_index S e es (fuel + 1) hf
    have hind : G.vertices * G.vertices - (e :: es).length =
        e.1.val * G.vertices + e.2.val := by
      rw [hidx.1, hidx.2]
      simpa [Nat.mul_comm] using (Nat.div_add_mod (G.vertices * G.vertices - (e :: es).length) G.vertices).symm
    have hlegal : (bit (clauseBits S ++ rest.flatMap frameWord) e.1.val &&
        bit (clauseBits S ++ rest.flatMap frameWord) e.2.val &&
        bit (graphWord G) (G.vertices + 1 + (e.1.val * G.vertices + e.2.val))) = false := by
      simpa [clauseBits_bit, graphWord_bit, legalEdge, Bool.and_eq_false_iff, not_and_or,
        or_assoc] using he
    simp only [List.length_cons] at hidx hind
    rw [stateWord, nextWord_frame]
    simp only [nextBody, bit, List.getElem?_cons_zero, Option.getD_some, Bool.false_eq_true,
      ↓reduceIte, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, List.length_cons,
      Nat.succ_ne_zero, or_self]
    change (if bit (clauseBits S ++ rest.flatMap frameWord)
        ((G.vertices * G.vertices - (es.length + 1)) / G.vertices) &&
        bit (clauseBits S ++ rest.flatMap frameWord)
        ((G.vertices * G.vertices - (es.length + 1)) % G.vertices) &&
        bit (graphWord G) (G.vertices + 1 + (G.vertices * G.vertices - (es.length + 1))) then _ else _) = _
    rw [← hidx.1, ← hidx.2, hind, hlegal]
    simp [stateWord, rawFrame, frameWord, clauseBits_length, List.append_assoc]
  | descend S e es fuel rest he =>
    have hf := hs _ List.mem_cons_self
    have hidx := todo_head_index S e es (fuel + 1) hf
    have hind : G.vertices * G.vertices - (e :: es).length =
        e.1.val * G.vertices + e.2.val := by
      rw [hidx.1, hidx.2]
      simpa [Nat.mul_comm] using (Nat.div_add_mod (G.vertices * G.vertices - (e :: es).length) G.vertices).symm
    have hlegal : (bit (clauseBits S ++ rest.flatMap frameWord) e.1.val &&
        bit (clauseBits S ++ rest.flatMap frameWord) e.2.val &&
        bit (graphWord G) (G.vertices + 1 + (e.1.val * G.vertices + e.2.val))) = true := by
      simpa [clauseBits_bit, graphWord_bit, legalEdge, Bool.and_eq_true, and_assoc] using he
    simp only [List.length_cons] at hidx hind
    rw [stateWord, nextWord_frame]
    simp only [nextBody, bit, List.getElem?_cons_zero, Option.getD_some, Bool.false_eq_true,
      ↓reduceIte, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, List.length_cons,
      Nat.succ_ne_zero, or_self]
    change (if bit (clauseBits S ++ rest.flatMap frameWord)
        ((G.vertices * G.vertices - (es.length + 1)) / G.vertices) &&
        bit (clauseBits S ++ rest.flatMap frameWord)
        ((G.vertices * G.vertices - (es.length + 1)) % G.vertices) &&
        bit (graphWord G) (G.vertices + 1 + (G.vertices * G.vertices - (es.length + 1))) then _ else _) = _
    rw [← hidx.1, ← hidx.2, hind, hlegal]
    simp [stateWord, rawFrame, frameWord, clauseBits_length, List.append_assoc,
      clearPair_clause, edgeList_length]

end Lax689614Proofs.DepthFirst
