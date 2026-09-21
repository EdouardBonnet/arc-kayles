import Lax689614Proofs.RestrictedConfigurationGraph
import Lax689614Proofs.QuantifiedPositiveCNF

set_option backward.isDefEq.respectTransparency false

namespace Lax689614Proofs.Quantified

open Lax434930Proofs.SavitchProofs
open Lax434930Proofs.SavitchDefinitions.Reachability
open Lax434930.SpaceMachines Lax434930.PolynomialTime
open ConfigurationWords

def vectorNumber {n : ℕ} (v : Vector n) : Fin (2 ^ n) :=
  ⟨BinaryCounter.value (vectorWord v), by simpa only [vectorWord_length] using BinaryCounter.value_lt (vectorWord v)⟩

def numberVector {n : ℕ} (a : Fin (2 ^ n)) : Vector n :=
  fun i => (BinaryCounter.word n a.val)[i.val]'(by simp)

theorem vectorWord_numberVector {n : ℕ} (a : Fin (2 ^ n)) :
    vectorWord (numberVector a) = BinaryCounter.word n a.val := by
  apply List.ext_getElem <;> simp [vectorWord, numberVector]

theorem vectorNumber_numberVector {n : ℕ} (a : Fin (2 ^ n)) : vectorNumber (numberVector a) = a := by
  apply Fin.ext
  simp [vectorNumber, vectorWord_numberVector, BinaryCounter.word_value, Nat.mod_eq_of_lt a.isLt]

theorem numberVector_vectorNumber {n : ℕ} (v : Vector n) : numberVector (vectorNumber v) = v := by
  apply vectorWord_injective n
  rw [vectorWord_numberVector]
  change BinaryCounter.word n (BinaryCounter.value (vectorWord v)) = vectorWord v
  simpa only [vectorWord_length] using BinaryCounter.word_of_value (vectorWord v)

def vectorEquiv (n : ℕ) : Vector n ≃ Fin (2 ^ n) where
  toFun := vectorNumber
  invFun := numberVector
  left_inv := numberVector_vectorNumber
  right_inv := vectorNumber_numberVector

theorem vectorNumber_zero (n : ℕ) : vectorNumber (fun _ : Fin n => false) = EncodedGraph.first n := by
  apply Fin.ext
  simp only [vectorNumber, vectorWord, EncodedGraph.first, List.map_const', List.length_finRange]
  simpa [BinaryCounter.word_zero] using BinaryCounter.word_value n 0

theorem vectorNumber_one (n : ℕ) : vectorNumber (fun _ : Fin n => true) = EncodedGraph.last n := by
  apply Fin.ext
  have h := BinaryCounter.ones_value n
  simp only [vectorNumber, vectorWord, List.map_const', List.length_finRange, EncodedGraph.last]
  omega

theorem walk_map {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ a b, R a b → S (f a) (f b)) {n : ℕ} {a b : α}
    (h : Walk R n a b) : Walk S n (f a) (f b) := by
  induction h with
  | nil a => exact .nil _
  | tail h he ih => exact .tail ih (hf _ _ he)

theorem within_equiv {α β : Type} (e : α ≃ β) (R : α → α → Prop) (S : β → β → Prop)
    (he : ∀ a b, R a b ↔ S (e a) (e b)) (n : ℕ) (a b : α) :
    Within R n a b ↔ Within S n (e a) (e b) := by
  constructor
  · rintro ⟨k, hk, hw⟩
    exact ⟨k, hk, walk_map e (fun a b => (he a b).mp) hw⟩
  · rintro ⟨k, hk, hw⟩
    refine ⟨k, hk, ?_⟩
    have hh := walk_map e.symm (fun a b h =>
      (he (e.symm a) (e.symm b)).mpr (by simpa using h)) hw
    simpa using hh

noncomputable def machineEdge (M : Machine) (w : Word) (k n : ℕ) :
    Expr (Fin (FiniteCoding.width (Payload M) * n) ⊕ Fin (FiniteCoding.width (Payload M) * n)) :=
  transitionExpr M w k n ((List.finRange _).map (fun i => .var (.inl i)))
    ((List.finRange _).map (fun i => .var (.inr i)))

theorem machineEdge_correct (M : Machine) (w : Word) (k n : ℕ)
    (x y : Vector (FiniteCoding.width (Payload M) * n)) :
    edgeRelation (machineEdge M w k n) x y ↔
      ConfigurationGraph.graph M w k n (vectorNumber x) (vectorNumber y) = true := by
  rw [ConfigurationGraph.edge_iff]
  unfold edgeRelation machineEdge
  rw [transitionExpr_correct _ _ _ _ _ _ _ (by simp) (by simp)]
  have hd (v : Vector (FiniteCoding.width (Payload M) * n)) :
      EncodedGraph.decode M _ (vectorNumber v) = FiniteCoding.decodeWord (Payload M) (vectorWord v) := by
    unfold EncodedGraph.decode vectorNumber
    exact congrArg (FiniteCoding.decodeWord (Payload M))
      (by simpa only [vectorWord_length] using BinaryCounter.word_of_value (vectorWord v))
  simp only [hd, vectorWord, List.map_map, Function.comp_def, Expr.eval, Sum.elim_inl, Sum.elim_inr]

noncomputable def machineFormula (M : Machine) (w : Word) (k s : ℕ) : Formula Empty :=
  let n := k + s + 2
  let m := FiniteCoding.width (Payload M) * n
  reach (machineEdge M w k n) m (fun _ => .constant false) (fun _ => .constant true)

theorem machineFormula_correct (M : Machine) (w : Word) (k s : ℕ)
    (hk : w.length + 1 < 2 ^ k) (hspace : M.UsesSpace w s) :
    (machineFormula M w k s).Holds Empty.elim ↔ M.Accepts w := by
  rw [machineFormula, holds_reach]
  rw [within_equiv (vectorEquiv _) _ (fun a b => ConfigurationGraph.graph M w k (k + s + 2) a b = true)
    (machineEdge_correct M w k (k + s + 2))]
  change Within _ _ (vectorNumber (fun _ => false)) (vectorNumber (fun _ => true)) ↔ _
  rw [vectorNumber_zero, vectorNumber_one, ← recursive_reachability]
  exact ConfigurationGraph.search_correct M w k s hk hspace

theorem machineFormula_positive (M : Machine) (w : Word) (k s : ℕ)
    (hk : w.length + 1 < 2 ^ k) (hspace : M.UsesSpace w s) :
    Lax689614.PositiveCNF.FirstWins (machineFormula M w k s).toPositive ↔ M.Accepts w := by
  rw [Formula.toPositive_correct, machineFormula_correct M w k s hk hspace]

end Lax689614Proofs.Quantified
