import Lax689614Proofs.CNFInert

namespace Lax689614Proofs

open Lax689614 PositiveCNF

theorem cnf_pair_eliminate_false (φ : Formula) (U T : Finset (Fin φ.nvars)) (q r : Fin φ.nvars)
    (hqr : q ≠ r) (hq : q ∉ U) (hr : r ∉ U)
    (ht : ClauseThreat φ (insert q (insert r U)) T {q, r})
    (hdom : ∀ S, Satisfied φ (insert r (T ∪ S)) → Satisfied φ (insert q (T ∪ S))) :
    TrueWins φ (insert q (insert r U)) T false ↔ TrueWins φ U (insert r T) false := by
  refine ⟨?_, cnf_pair_lift φ U T q r hqr hq hr false hdom⟩
  intro hw
  have hq' : q ∈ insert q (insert r U) := Finset.mem_insert_self _ _
  have child := (cnf_false φ _ T (Finset.insert_ne_empty _ _)).mp hw q hq'
  have hs : ClauseThreat φ ((insert q (insert r U)).erase q) T {r} := by
    simpa [hqr, Ne.symm hqr] using ht.assignFalse q
  have hnext := hs.forced_true.mp child
  simpa [hq, hr, hqr, Ne.symm hqr] using hnext

theorem dominates_of_clauses (φ : Formula) (T : Finset (Fin φ.nvars)) (q r : Fin φ.nvars)
    (h : ∀ C ∈ φ.clauses, r ∈ C → q ∈ C ∨ ∃ i ∈ C, i ∈ T) :
    ∀ S, Satisfied φ (insert r (T ∪ S)) → Satisfied φ (insert q (T ∪ S)) := by
  intro S hs C hC
  obtain ⟨i, hi, ht⟩ := hs C hC
  rcases Finset.mem_insert.mp ht with he | ht
  · subst i
    rcases h C hC hi with hq | ⟨j, hj, hjT⟩
    · exact ⟨q, hq, Finset.mem_insert_self _ _⟩
    · exact ⟨j, hj, Finset.mem_insert_of_mem (Finset.mem_union_left _ hjT)⟩
  · exact ⟨i, hi, Finset.mem_insert_of_mem ht⟩

theorem restore_two {α : Type} [DecidableEq α] (U : Finset α) (q r : α)
    (hq : q ∈ U) (hr : r ∈ U) : insert q (insert r ((U.erase q).erase r)) = U := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_erase]
  by_cases hxq : x = q <;> by_cases hxr : x = r <;> aesop

theorem cnf_pair_eliminate (φ : Formula) (U T : Finset (Fin φ.nvars)) (q r : Fin φ.nvars)
    (hqr : q ≠ r) (hq : q ∈ U) (hr : r ∈ U) (ht : ClauseThreat φ U T {q, r})
    (hdom : ∀ S, Satisfied φ (insert r (T ∪ S)) → Satisfied φ (insert q (T ∪ S))) :
    TrueWins φ U T false ↔ TrueWins φ ((U.erase q).erase r) (insert r T) false := by
  have he := restore_two U q r hq hr
  have hpair := cnf_pair_eliminate_false φ ((U.erase q).erase r) T q r hqr
    (by simp) (by simp) (by simpa only [he] using ht) hdom
  simpa only [he] using hpair

/-- The three two-element clauses in the existential-variable gadget
force a winning True move to choose one of its two unprimed vertices. -/
theorem three_pairs_choice (φ : Formula) (U T : Finset (Fin φ.nvars))
    (q r qp rp : Fin φ.nvars) (hqr : q ≠ r) (hqqp : q ≠ qp)
    (hrrp : r ≠ rp) (hqprp : qp ≠ rp)
    (h₁ : ClauseThreat φ U T {q, r}) (h₂ : ClauseThreat φ U T {q, rp})
    (h₃ : ClauseThreat φ U T {qp, r}) :
    TrueWins φ U T true ↔
      TrueWins φ (U.erase q) (insert q T) false ∨
      TrueWins φ (U.erase r) (insert r T) false := by
  have hq : q ∈ U := h₁.subset (by simp)
  have hr : r ∈ U := h₁.subset (by simp)
  rw [cnf_true φ U T (Finset.nonempty_iff_ne_empty.mp ⟨q, hq⟩)]
  constructor
  · rintro ⟨x, hx, hw⟩
    by_cases hxq : x = q
    · exact Or.inl (by simpa [hxq] using hw)
    by_cases hxr : x = r
    · exact Or.inr (by simpa [hxr] using hw)
    by_cases hxrp : x = rp
    · have ha := h₁.assignTrue x hx (by simp [hxq, hxr])
      have hb := h₃.assignTrue x hx (by simp [hxrp, Ne.symm hqprp, Ne.symm hrrp])
      have hr' : r ∈ U.erase x := by simp [hr, Ne.symm hxr]
      have child := (cnf_false φ _ _ (Finset.nonempty_iff_ne_empty.mp ⟨r, hr'⟩)).mp hw r hr'
      have ha' : ClauseThreat φ ((U.erase x).erase r) (insert x T) {q} := by
        simpa [Finset.erase_insert_of_ne, hqr, Ne.symm hqr] using ha.assignFalse r
      have hb' : ClauseThreat φ ((U.erase x).erase r) (insert x T) {qp} := by
        have hqp : qp ≠ r := by
          intro he
          subst qp
          have hex : ClauseThreat φ (U.erase x) (insert x T) {r} := by simpa using hb
          exact hex.singleton_false_loses hw
        simpa [Finset.erase_insert_of_ne, hqp, Ne.symm hqp] using hb.assignFalse r
      exact (two_singletons_lose ha' hb' hqqp child).elim
    · have ha := h₁.assignTrue x hx (by simp [hxq, hxr])
      have hb := h₂.assignTrue x hx (by simp [hxq, hxrp])
      have hq' : q ∈ U.erase x := by simp [hq, Ne.symm hxq]
      have child := (cnf_false φ _ _ (Finset.nonempty_iff_ne_empty.mp ⟨q, hq'⟩)).mp hw q hq'
      have ha' : ClauseThreat φ ((U.erase x).erase q) (insert x T) {r} := by
        simpa [hqr, Ne.symm hqr] using ha.assignFalse q
      have hb' : ClauseThreat φ ((U.erase x).erase q) (insert x T) {rp} := by
        have hrp : rp ≠ q := by
          intro he
          subst rp
          have hex : ClauseThreat φ (U.erase x) (insert x T) {q} := by simpa using hb
          exact hex.singleton_false_loses hw
        simpa [hrp, Ne.symm hrp] using hb.assignFalse q
      exact (two_singletons_lose ha' hb' hrrp child).elim
  · rintro (hw | hw)
    · exact ⟨q, hq, hw⟩
    · exact ⟨r, hr, hw⟩

end Lax689614Proofs
