import Lax689614Proofs.CNFThreats

namespace Lax689614Proofs

open Lax689614 PositiveCNF

theorem cnf_payoff_mono (φ : Formula) (U T T' : Finset (Fin φ.nvars)) (turn : Bool)
    (h : ∀ S, Satisfied φ (T ∪ S) → Satisfied φ (T' ∪ S)) :
    TrueWins φ U T turn → TrueWins φ U T' turn := by
  induction hn : U.card using Nat.strong_induction_on generalizing U T T' turn with
  | h n ih =>
    intro hw
    by_cases he : U = ∅
    · subst U
      rw [cnf_empty] at hw ⊢
      simpa using h ∅ (by simpa using hw)
    · cases turn
      · apply (cnf_false φ U T' he).mpr
        intro x hx
        exact ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) _ _ _ true h rfl
          ((cnf_false φ U T he).mp hw x hx)
      · obtain ⟨x, hx, hw⟩ := (cnf_true φ U T he).mp hw
        apply (cnf_true φ U T' he).mpr
        refine ⟨x, hx, ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) _ _ _ false ?_ rfl hw⟩
        intro S hs
        simpa only [Finset.union_insert, Finset.insert_union] using
          h (insert x S) (by simpa only [Finset.union_insert, Finset.insert_union] using hs)

/-- A response pair can be kept in reserve. The less useful member is
guaranteed to True; if False takes it, True claims the dominating member. -/
theorem cnf_pair_lift (φ : Formula) (U T : Finset (Fin φ.nvars)) (q r : Fin φ.nvars)
    (hqr : q ≠ r) (hq : q ∉ U) (hr : r ∉ U) (turn : Bool)
    (hdom : ∀ S, Satisfied φ (insert r (T ∪ S)) → Satisfied φ (insert q (T ∪ S)))
    (hw : TrueWins φ U (insert r T) turn) :
    TrueWins φ (insert q (insert r U)) T turn := by
  induction hn : U.card using Nat.strong_induction_on generalizing U T turn with
  | h n ih =>
    have smaller (x : Fin φ.nvars) (hx : x ∈ U) :=
      ih _ (hn ▸ Finset.card_erase_lt_of_mem hx) (U.erase x)
    have hne : insert q (insert r U) ≠ ∅ := Finset.insert_ne_empty _ _
    cases turn
    · apply (cnf_false φ _ T hne).mpr
      intro x hx
      rcases Finset.mem_insert.mp hx with he | hx
      · subst x
        have hr' : r ∈ (insert q (insert r U)).erase q := by simp [hqr, Ne.symm hqr]
        apply (cnf_true φ _ _ (Finset.nonempty_iff_ne_empty.mp ⟨r, hr'⟩)).mpr
        refine ⟨r, hr', ?_⟩
        simpa [hq, hr, hqr, Ne.symm hqr] using hw
      · rcases Finset.mem_insert.mp hx with he | hx
        · subst x
          have hq' : q ∈ (insert q (insert r U)).erase r := by simp [hqr]
          apply (cnf_true φ _ _ (Finset.nonempty_iff_ne_empty.mp ⟨q, hq'⟩)).mpr
          refine ⟨q, hq', ?_⟩
          have hwin := cnf_payoff_mono φ U (insert r T) (insert q T) false
            (fun S hs => by simpa only [Finset.insert_union] using hdom S (by
              simpa only [Finset.insert_union] using hs)) hw
          simpa [Finset.erase_insert_of_ne, hq, hr, hqr, Ne.symm hqr] using hwin
        · have hxq : x ≠ q := fun he => hq (he ▸ hx)
          have hxr : x ≠ r := fun he => hr (he ▸ hx)
          have hw' := (cnf_false φ U (insert r T) (Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩)).mp hw x hx
          have hlift := smaller x hx T (by simp [hq]) (by simp [hr]) true hdom hw' rfl
          simpa [Finset.erase_insert_of_ne, hxq, hxr, Ne.symm hxq, Ne.symm hxr] using hlift
    · by_cases hu : U = ∅
      · subst U
        have hs : Satisfied φ (insert q T) := by
          have hh := (cnf_empty φ (insert r T) true).mp hw
          simpa using hdom ∅ (by simpa using hh)
        apply (cnf_true φ _ _ hne).mpr
        exact ⟨q, Finset.mem_insert_self _ _, cnf_of_satisfied φ _ _ false hs⟩
      · obtain ⟨x, hx, hw'⟩ := (cnf_true φ U (insert r T) hu).mp hw
        have hxq : x ≠ q := fun he => hq (he ▸ hx)
        have hxr : x ≠ r := fun he => hr (he ▸ hx)
        apply (cnf_true φ _ _ hne).mpr
        refine ⟨x, by simp [hx], ?_⟩
        have hd : ∀ S, Satisfied φ (insert r (insert x T ∪ S)) →
            Satisfied φ (insert q (insert x T ∪ S)) := by
          intro S hs
          simpa only [Finset.insert_union, Finset.union_insert] using
            hdom (insert x S) (by simpa only [Finset.insert_union, Finset.union_insert] using hs)
        have hlift := smaller x hx (insert x T) (by simp [hq]) (by simp [hr]) false hd
          (by simpa only [Finset.insert_comm] using hw') rfl
        simpa [Finset.erase_insert_of_ne, hxq, hxr, Ne.symm hxq, Ne.symm hxr] using hlift

theorem two_hitting_vertices (φ : Formula) (U T : Finset (Fin φ.nvars))
    (q r : Fin φ.nvars) (hqr : q ≠ r) (hq : q ∈ U) (hr : r ∈ U)
    (hsq : Satisfied φ (insert q T)) (hsr : Satisfied φ (insert r T)) :
    TrueWins φ U T false := by
  apply (cnf_false φ U T (Finset.nonempty_iff_ne_empty.mp ⟨q, hq⟩)).mpr
  intro x hx
  by_cases he : x = q
  · subst x
    have hr' : r ∈ U.erase q := by simp [hr, Ne.symm hqr]
    apply (cnf_true φ _ _ (Finset.nonempty_iff_ne_empty.mp ⟨r, hr'⟩)).mpr
    exact ⟨r, hr', cnf_of_satisfied φ _ _ false hsr⟩
  · have hq' : q ∈ U.erase x := by simp [hq, Ne.symm he]
    apply (cnf_true φ _ _ (Finset.nonempty_iff_ne_empty.mp ⟨q, hq'⟩)).mpr
    exact ⟨q, hq', cnf_of_satisfied φ _ _ false hsq⟩

theorem reply_with_two_choices (φ : Formula) (U T : Finset (Fin φ.nvars))
    (q r u z : Fin φ.nvars) (hqr : q ≠ r) (hqu : q ≠ u) (hru : r ≠ u)
    (hq : q ∈ U) (hr : r ∈ U) (hu : u ∈ U)
    (hzq : z ≠ q) (hzr : z ≠ r) (hzu : z ≠ u)
    (hsq : Satisfied φ (insert q (insert u T)))
    (hsr : Satisfied φ (insert r (insert u T))) :
    TrueWins φ (U.erase z) T true := by
  have hu' : u ∈ U.erase z := by simp [hu, Ne.symm hzu]
  apply (cnf_true φ _ _ (Finset.nonempty_iff_ne_empty.mp ⟨u, hu'⟩)).mpr
  refine ⟨u, hu', two_hitting_vertices φ _ _ q r hqr ?_ ?_ hsq hsr⟩
  · simp [hq, hqu, Ne.symm hzq]
  · simp [hr, hru, Ne.symm hzr]

end Lax689614Proofs
