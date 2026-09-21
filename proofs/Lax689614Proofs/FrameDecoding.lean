import Lax689614Proofs.DepthFirstSpace

namespace Lax689614Proofs.DepthFirst

theorem todo_drop {n : ℕ} (f : Frame n) (hf : f.Good) :
    (edgeList n).drop (n * n - f.todo.length) = f.todo := by
  obtain ⟨pre, he⟩ := hf.2
  have hl : n * n - f.todo.length = pre.length := by
    have hh := congrArg List.length he
    rw [List.length_append, edgeList_length] at hh
    omega
  rw [hl, ← he]
  simp

def readFrame (n : ℕ) (w : List Bool) : Option (Frame n × List Bool) := do
  let (fuel, w) ← readUnary w
  let (count, w) ← readUnary w
  let (board, rest) ← readClause n w
  if count ≤ n * n then some (⟨board, (edgeList n).drop (n * n - count), fuel⟩, rest) else none

theorem readFrame_word {n : ℕ} (f : Frame n) (hf : f.Good) (rest : List Bool) :
    readFrame n (frameWord f ++ rest) = some (f, rest) := by
  have hcount : f.todo.length ≤ n * n := by simpa [edgeList_length] using hf.2.length_le
  simp only [readFrame, frameWord, List.append_assoc, List.cons_append,
    readUnary_prefix, bind, Option.bind_some, readClause_prefix, hcount, ↓reduceIte, todo_drop f hf]

theorem frameWord_injective_on {n : ℕ} {f g : Frame n} (hf : f.Good) (hg : g.Good)
    (he : frameWord f = frameWord g) : f = g := by
  have hr := congrArg (fun w => readFrame n (w ++ [])) he
  rw [readFrame_word f hf, readFrame_word g hg] at hr
  exact congrArg Prod.fst (Option.some.inj hr)

theorem flatMap_get_uniform {A : Type} (rows : List (List A)) (n : ℕ)
    (hrows : ∀ row ∈ rows, row.length = n) (j : Fin rows.length) (i : Fin n) :
    rows.flatten[j.val * n + i.val]? = rows[j][i.val]? := by
  induction rows with
  | nil => exact Fin.elim0 j
  | cons row rows ih =>
    have hrow := hrows row List.mem_cons_self
    have hrest := fun r hr => hrows r (List.mem_cons_of_mem _ hr)
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add, List.flatten_cons]
      rw [List.getElem?_append_left (by rw [hrow]; exact i.isLt)]
      rfl
    · simp only [Fin.val_succ, List.flatten_cons]
      rw [List.getElem?_append_right (by rw [hrow]; nlinarith), hrow]
      have he : (k.val + 1) * n + i.val - n = k.val * n + i.val := by
        simp only [Nat.add_mul, Nat.one_mul]; omega
      rw [he]
      exact ih hrest k

theorem edgeList_get_pair {n : ℕ} (u v : Fin n) :
    (edgeList n)[u.val * n + v.val]? = some (u, v) := by
  let rows := (List.finRange n).map fun x => (List.finRange n).map fun y => (x, y)
  have hrows : ∀ row ∈ rows, row.length = n := by simp [rows]
  have hj : u.val < rows.length := by simp [rows]
  have hg := flatMap_get_uniform rows n hrows ⟨u.val, hj⟩ v
  change (edgeList n)[u.val * n + v.val]? = _ at hg
  simpa [rows, List.getElem?_eq_getElem, u.isLt, v.isLt] using hg

theorem edgeList_get {n j : ℕ} (hj : j < n * n) :
    ∃ u v : Fin n, (edgeList n)[j]? = some (u, v) ∧ u.val = j / n ∧ v.val = j % n := by
  have hn : 0 < n := by nlinarith
  have hu : j / n < n := (Nat.div_lt_iff_lt_mul hn).mpr hj
  have hv : j % n < n := Nat.mod_lt _ hn
  refine ⟨⟨j / n, hu⟩, ⟨j % n, hv⟩, ?_, rfl, rfl⟩
  have he : j / n * n + j % n = j := by simpa [Nat.mul_comm] using Nat.div_add_mod j n
  simpa only [he] using edgeList_get_pair (⟨j / n, hu⟩ : Fin n) ⟨j % n, hv⟩

theorem todo_head_index {n : ℕ} (S : Finset (Fin n)) (e : Fin n × Fin n)
    (es : List (Fin n × Fin n)) (fuel : ℕ) (hf : (Frame.mk S (e :: es) fuel).Good) :
    e.1.val = (n * n - (e :: es).length) / n ∧
    e.2.val = (n * n - (e :: es).length) % n := by
  have hlen := hf.2.length_le
  rw [edgeList_length] at hlen
  have hj : n * n - (e :: es).length < n * n := by simp only [List.length_cons] at *; omega
  obtain ⟨u, v, hget, hu, hv⟩ := edgeList_get hj
  have hdrop := todo_drop (Frame.mk S (e :: es) fuel) hf
  have hhead := congrArg List.head? hdrop
  rw [List.head?_drop] at hhead
  change (edgeList n)[n * n - (e :: es).length]? = some e at hhead
  rw [hget] at hhead
  cases Option.some.inj hhead
  exact ⟨hu, hv⟩

end Lax689614Proofs.DepthFirst
