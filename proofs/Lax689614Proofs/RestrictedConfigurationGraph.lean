import Lax689614Proofs.ConfigurationValidity

/-!
The run-to-path construction specializes the archived configuration encoding
to a fixed input-head field width. Its induction follows
`Lax434930Proofs.SavitchProofs.EncodedGraph.encoded_run` (Apache-2.0).
-/

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified.ConfigurationGraph

open Lax434930Proofs.SavitchProofs
open ConfigurationWords PatternAutomata EncodedGraph
open Lax434930.SpaceMachines Lax434930.PolynomialTime
open Lax434930Proofs.SavitchDefinitions.Reachability
open scoped Classical

noncomputable section

def graph (M : Machine) (w : Word) (k n : ℕ) : Graph (2 ^ (FiniteCoding.width (Payload M) * n)) :=
  fun a b => decide ((∃ p ∈ graphPatterns M,
    Matches p (List.zip (decode M _ a) (decode M _ b))) ∧
      InputForm M w k (decode M _ a) ∧ InputForm M w k (decode M _ b))

theorem edge_iff (M : Machine) (w : Word) (k n : ℕ) (a b : Fin (2 ^ (FiniteCoding.width (Payload M) * n))) :
    graph M w k n a b = true ↔
      (∃ p ∈ graphPatterns M, Matches p (List.zip (decode M _ a) (decode M _ b))) ∧
        InputForm M w k (decode M _ a) ∧ InputForm M w k (decode M _ b) := by
  simp [graph]

theorem edge_sound (M : Machine) (w : Word) (k n : ℕ) (hk : w.length + 1 < 2 ^ k)
    (a b : Fin (2 ^ (FiniteCoding.width (Payload M) * n))) (h : graph M w k n a b = true) :
    EncodedGraph.graph M w _ a b = true := by
  obtain ⟨hp, ha, hb⟩ := (edge_iff M w k n a b).mp h
  exact (EncodedGraph.edge_iff M w _ a b).mpr
    ⟨hp, InputForm.valid M w k _ hk ha, InputForm.valid M w k _ hk hb⟩

theorem reachable_sound (M : Machine) (w : Word) (k n : ℕ)
    (hk : w.length + 1 < 2 ^ k) (hn : 0 < n)
    (h : Reachable (graph M w k n) (first _) (last _)) : M.Accepts w := by
  apply EncodedGraph.reachable_sound M w n hn
  have hmono : ∀ a b, Reachable (graph M w k n) a b →
      Reachable (EncodedGraph.graph M w _) a b := by
    intro a b hab
    induction hab with
    | refl => exact .refl
    | @tail b d h he ih => exact ih.tail (edge_sound M w k n hk b d he)
  exact hmono _ _ h

theorem run_path (M : Machine) (w : Word) (k s : ℕ) (hk : w.length + 1 < 2 ^ k)
    (hspace : M.UsesSpace w s) (t : ℕ) (c : M.Config) (hr : M.Run w t c) :
    ∃ v : TapeZipper.View M, ∃ a : Fin (2 ^ (FiniteCoding.width (Payload M) * (k + s + 2))),
      v.cells = s ∧ v.expand = c ∧ decode M _ a = canonical M w k v ∧
        Reachable (graph M w k (k + s + 2)) (first _) a := by
  have hs : 0 < s := hspace 0 M.initial .zero
  let m := FiniteCoding.width (Payload M) * (k + s + 2)
  induction hr with
  | zero =>
    let v := TapeZipper.padded M (s - 1)
    have hv : v.cells = s := by simp [v]; omega
    let a := vertex M m (canonical M w k v) (by simp [m, hv])
    have hd : decode M m a = canonical M w k v := decode_vertex M m _ _
    refine ⟨v, a, hv, TapeZipper.padded_expand M _, hd, Relation.ReflTransGen.single ?_⟩
    apply (edge_iff M w k (k + s + 2) _ _).mpr
    rw [hd]
    have hfirst : decode M m (first m) = List.replicate (k + (s - 1) + 3) (.inl false) := by
      rw [decode_first]
      congr 1
      omega
    rw [hfirst]
    exact ⟨initial_complete M w k (s - 1), InputForm.special M w k _ false,
      InputForm.canonical M w k v (by simp [v, TapeZipper.padded])⟩
  | @succ t c d hr he ih =>
    obtain ⟨v, a, hv, hvc, hdecode, hpath⟩ := ih
    obtain ⟨action, haction, hd⟩ := he
    let v' := TapeZipper.apply M w v action
    have hvd : v'.expand = d := by rw [TapeZipper.apply_expand, hvc, hd]
    have hhead : v'.left.length < v.cells := by
      rw [hv]
      have hh := hspace (t + 1) d (.succ hr ⟨action, haction, hd⟩)
      simpa only [← hvd, TapeZipper.View.expand] using hh
    have hv' : v'.cells = s := (TapeZipper.cells_eq M w v action hhead).trans hv
    let b := vertex M m (canonical M w k v') (by simp [m, hv'])
    have hdecode' : decode M m b = canonical M w k v' := decode_vertex M m _ _
    have hi : v.inputHead ≤ w.length + 1 := by simpa only [← hvc, TapeZipper.View.expand] using input_bound hr
    have hi' : v'.inputHead ≤ w.length + 1 := by
      simpa only [← hvd, TapeZipper.View.expand] using input_bound (.succ hr ⟨action, haction, hd⟩)
    refine ⟨v', b, hv', hvd, hdecode', hpath.tail ?_⟩
    apply (edge_iff M w k (k + s + 2) a b).mpr
    rw [hdecode, hdecode']
    have ha : action ∈ M.transition v.state (readInput w v.inputHead) v.current := by
      rw [← hvc, TapeZipper.current_scanned] at haction
      exact haction
    exact ⟨canonical_step M w k v action ha hi hk hhead,
      InputForm.canonical M w k v hi, InputForm.canonical M w k v' hi'⟩

theorem reachable_complete (M : Machine) (w : Word) (k s : ℕ) (hk : w.length + 1 < 2 ^ k)
    (hspace : M.UsesSpace w s) (h : M.Accepts w) :
    Reachable (graph M w k (k + s + 2)) (first _) (last _) := by
  obtain ⟨t, c, hr, ht, ha⟩ := h
  obtain ⟨v, a, hv, hvc, hd, hp⟩ := run_path M w k s hk hspace t c hr
  refine hp.tail ((edge_iff M w k (k + s + 2) _ _).mpr ?_)
  rw [hd, decode_last]
  have hi : v.inputHead ≤ w.length + 1 := by simpa only [← hvc, TapeZipper.View.expand] using input_bound hr
  refine ⟨?_, InputForm.canonical M w k v hi, InputForm.special M w k _ true⟩
  simpa only [hv] using terminal_complete M w k v (by simpa only [← hvc] using ht)
    (by change M.accept v.expand.state = true; rw [hvc]; exact ha)

theorem search_correct (M : Machine) (w : Word) (k s : ℕ) (hk : w.length + 1 < 2 ^ k)
    (hspace : M.UsesSpace w s) :
    let m := FiniteCoding.width (Payload M) * (k + s + 2)
    search (graph M w k (k + s + 2)) m (first m) (last m) = true ↔ M.Accepts w := by
  dsimp only
  rw [recursive_reachability]
  constructor
  · rintro ⟨t, _, ht⟩
    exact reachable_sound M w k _ hk (by omega) (walk_reachable ht)
  · intro ha
    obtain ⟨t, ht, hw⟩ := (short_paths _ _ _).mp (reachable_complete M w k s hk hspace ha)
    exact ⟨t, Nat.le_of_lt ht, hw⟩

end

end Lax689614Proofs.Quantified.ConfigurationGraph
