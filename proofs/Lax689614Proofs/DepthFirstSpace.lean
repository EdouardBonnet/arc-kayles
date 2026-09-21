import Lax689614Proofs.DepthFirst
import Lax689614Proofs.ParserLengths

namespace Lax689614Proofs.DepthFirst

def Frame.Good {n : ℕ} (f : Frame n) : Prop :=
  f.fuel ≤ n ∧ f.todo.IsSuffix (edgeList n)

def State.Good {n : ℕ} (s : State n) : Prop := ∀ f ∈ s.frames, f.Good

theorem tail_good {n : ℕ} (S : Finset (Fin n)) (e : Fin n × Fin n)
    (es : List (Fin n × Fin n)) (fuel : ℕ) (h : (Frame.mk S (e :: es) fuel).Good) :
    (Frame.mk S es fuel).Good :=
  ⟨h.1, (List.tail_suffix (e :: es)).trans h.2⟩

theorem step_good {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {s t : State n} (h : Step G s t) (hs : s.Good) : t.Good := by
  cases h with
  | zero S es rest => exact fun f hf => hs f (List.mem_cons_of_mem _ hf)
  | exhausted S fuel rest => exact fun f hf => hs f (List.mem_cons_of_mem _ hf)
  | skip S e es fuel rest he =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact tail_good S e es (fuel + 1) (hs _ (List.mem_cons_self))
    · exact hs f (List.mem_cons_of_mem _ hf)
  | descend S e es fuel rest he =>
    have hp := hs _ List.mem_cons_self
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨Nat.le_trans (Nat.le_succ fuel) hp.1, ⟨[], rfl⟩⟩
    · rcases List.mem_cons.mp hf with rfl | hf
      · exact tail_good S e es (fuel + 1) hp
      · exact hs f (List.mem_cons_of_mem _ hf)
  | childWins parent rest => exact hs
  | childLoses parent rest => exact fun f hf => hs f (List.mem_cons_of_mem _ hf)

theorem trace_good {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {b : ℕ} {s t : State n} (h : Trace G b s t) (hs : s.Good) : t.Good := by
  induction h with
  | refl => exact hs
  | tail hstep hlast ih => exact step_good hlast.1 ih

def frameWord {n : ℕ} (f : Frame n) : List Bool :=
  List.replicate f.fuel true ++ false ::
    (List.replicate f.todo.length true ++ false :: clauseBits f.board)

def stateWord {n : ℕ} (s : State n) : List Bool :=
  match s with
  | .search fs => [false, false] ++ fs.flatMap frameWord
  | .returning b fs => [true, b] ++ fs.flatMap frameWord

theorem frameWord_length {n : ℕ} (f : Frame n) :
    (frameWord f).length = f.fuel + f.todo.length + n + 2 := by
  simp [frameWord, clauseBits_length]; omega

theorem frameWord_length_bound {n : ℕ} (f : Frame n) (hf : f.Good) :
    (frameWord f).length ≤ n * n + 2 * n + 2 := by
  have htodo := hf.2.length_le
  rw [edgeList_length] at htodo
  rw [frameWord_length]
  have hfu := hf.1
  omega

theorem stateWord_length_bound {n : ℕ} (s : State n) (hs : s.Good) (hd : s.depth ≤ n + 1) :
    (stateWord s).length ≤ (n + 1) * (n * n + 2 * n + 2) + 2 := by
  have hframes (fs : List (Frame n)) (hfs : ∀ f ∈ fs, f.Good) :
      (fs.flatMap frameWord).length ≤ fs.length * (n * n + 2 * n + 2) := by
    induction fs with
    | nil => simp
    | cons f fs ih =>
      have hf := frameWord_length_bound f (hfs f List.mem_cons_self)
      have hi := ih (fun g hg => hfs g (List.mem_cons_of_mem _ hg))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      nlinarith
  have hf := hframes s.frames hs
  have hm := Nat.mul_le_mul_right (n * n + 2 * n + 2) hd
  cases s <;> simp only [stateWord, State.depth, State.frames, List.length_append,
    List.length_cons, List.length_nil] at * <;> omega

theorem initial_good (n : ℕ) : (State.search [⟨Finset.univ, edgeList n, n⟩]).Good := by
  intro f hf
  simp only [State.frames, List.mem_singleton] at hf
  subst f
  exact ⟨Nat.le_refl _, ⟨[], rfl⟩⟩

end Lax689614Proofs.DepthFirst
