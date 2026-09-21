import Lax689614Proofs.Grundy
import Lax689614Proofs.Biclique

namespace Lax689614Proofs

open Lax689614 ArcKayles Grundy

theorem remove_union_left {V : Type} [DecidableEq V] (S T : Finset V)
    (hd : Disjoint S T) (u v : V) (hu : u ∈ S) (hv : v ∈ S) :
    remove (S ∪ T) u v = remove S u v ∪ T := by
  have huT : u ∉ T := Finset.disjoint_left.mp hd hu
  have hvT : v ∉ T := Finset.disjoint_left.mp hd hv
  ext w
  simp only [remove_mem, Finset.mem_union]
  aesop

theorem union_move_cases {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S T : Finset V) (hn : ∀ u ∈ S, ∀ v ∈ T, ¬ G.Adj u v)
    (u v : V) (hu : u ∈ S ∪ T) (hv : v ∈ S ∪ T) (he : G.Adj u v) :
    (u ∈ S ∧ v ∈ S) ∨ (u ∈ T ∧ v ∈ T) := by
  rcases Finset.mem_union.mp hu with hu | hu <;>
    rcases Finset.mem_union.mp hv with hv | hv
  · exact Or.inl ⟨hu, hv⟩
  · exact False.elim (hn u hu v hv he)
  · exact False.elim (hn v hv u hu he.symm)
  · exact Or.inr ⟨hu, hv⟩

/--
---
conclusion: Lax689614.GrundyProperties.disjoint_union
---
Induct on the total number of vertices. Each move changes one component.
The xor of the two values is unreachable, while every smaller value is
reachable by the xor comparison lemma and the mex property.
-/
theorem disjoint_union {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S T : Finset V) (hd : Disjoint S T)
    (hn : ∀ u ∈ S, ∀ v ∈ T, ¬ G.Adj u v) :
    value G (S ∪ T) = Nat.xor (value G S) (value G T) := by
  classical
  induction hsize : S.card + T.card using Nat.strong_induction_on generalizing S T with
  | h n ih =>
    have leftChild (u v : V) (hu : u ∈ S) (hv : v ∈ S) :
        value G (remove (S ∪ T) u v) = Nat.xor (value G (remove S u v)) (value G T) := by
      rw [remove_union_left S T hd u v hu hv]
      apply ih ((remove S u v).card + T.card)
      · have hlt : (remove S u v).card < S.card :=
          lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hu)
        omega
      · exact hd.mono_left (remove_subset S u v)
      · intro x hx y hy
        exact hn x (remove_subset S u v hx) y hy
      · rfl
    have rightChild (u v : V) (hu : u ∈ T) (hv : v ∈ T) :
        value G (remove (S ∪ T) u v) = Nat.xor (value G S) (value G (remove T u v)) := by
      rw [Finset.union_comm S T, remove_union_left T S hd.symm u v hu hv,
        Finset.union_comm (remove T u v) S]
      apply ih (S.card + (remove T u v).card)
      · have hlt : (remove T u v).card < T.card :=
          lt_of_le_of_lt Finset.card_erase_le (Finset.card_erase_lt_of_mem hu)
        omega
      · exact hd.mono_right (remove_subset T u v)
      · intro x hx y hy
        exact hn x hx y (remove_subset T u v hy)
      · rfl
    rw [value_eq_mex]
    apply mex_eq
    · intro hi
      obtain ⟨u, hu, v, hv, he, hh⟩ := (option_mem G (S ∪ T) _).mp hi
      rcases union_move_cases G S T hn u v hu hv he with ⟨huS, hvS⟩ | ⟨huT, hvT⟩
      · rw [leftChild u v huS hvS] at hh
        have hc := congrArg (fun x => Nat.xor x (value G T)) hh
        change (value G (remove S u v) ^^^ value G T) ^^^ value G T =
          (value G S ^^^ value G T) ^^^ value G T at hc
        simp only [Nat.xor_xor_cancel_right] at hc
        exact GrundyProperties.value_not_reachable G S u v huS hvS he hc
      · rw [rightChild u v huT hvT] at hh
        have hc := congrArg (fun x => Nat.xor (value G S) x) hh
        change value G S ^^^ (value G S ^^^ value G (remove T u v)) =
          value G S ^^^ (value G S ^^^ value G T) at hc
        simp only [Nat.xor_xor_cancel_left] at hc
        exact GrundyProperties.value_not_reachable G T u v huT hvT he hc
    · intro i hi
      apply (option_mem G (S ∪ T) i).mpr
      rcases Nat.lt_xor_cases hi with hleft | hright
      · obtain ⟨u, hu, v, hv, he, hh⟩ := GrundyProperties.smaller_reachable G S _ hleft
        refine ⟨u, Finset.mem_union_left T hu, v, Finset.mem_union_left T hv, he, ?_⟩
        rw [leftChild u v hu hv, hh]
        change (i ^^^ value G T) ^^^ value G T = i
        exact Nat.xor_xor_cancel_right _ _
      · obtain ⟨u, hu, v, hv, he, hh⟩ := GrundyProperties.smaller_reachable G T _ hright
        refine ⟨u, Finset.mem_union_right S hu, v, Finset.mem_union_right S hv, he, ?_⟩
        rw [rightChild u v hu hv, hh]
        change value G S ^^^ (i ^^^ value G S) = i
        rw [Nat.xor_comm (value G S), Nat.xor_xor_cancel_right]

end Lax689614Proofs
