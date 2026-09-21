import Lax689614Proofs.Assignments

namespace Lax689614Proofs

open Lax689614 PositiveCNF

/-- An unhit clause whose still available variables are exactly `R`. -/
def ClauseThreat (φ : Formula) (U T R : Finset (Fin φ.nvars)) : Prop :=
  ∃ C ∈ φ.clauses, Disjoint C T ∧ C ∩ U = R

theorem ClauseThreat.subset {φ : Formula} {U T R : Finset (Fin φ.nvars)}
    (h : ClauseThreat φ U T R) : R ⊆ U := by
  obtain ⟨C, _, _, rfl⟩ := h
  exact Finset.inter_subset_right

theorem ClauseThreat.assignFalse {φ : Formula} {U T R : Finset (Fin φ.nvars)}
    (h : ClauseThreat φ U T R) (x : Fin φ.nvars) :
    ClauseThreat φ (U.erase x) T (R.erase x) := by
  obtain ⟨C, hc, ht, rfl⟩ := h
  refine ⟨C, hc, ht, ?_⟩
  ext i; simp [and_comm, and_left_comm, and_assoc]

theorem ClauseThreat.assignTrue {φ : Formula} {U T R : Finset (Fin φ.nvars)}
    (h : ClauseThreat φ U T R) (x : Fin φ.nvars) (hx : x ∈ U) (hr : x ∉ R) :
    ClauseThreat φ (U.erase x) (insert x T) R := by
  obtain ⟨C, hc, ht, hR⟩ := h
  have hxC : x ∉ C := by intro hm; exact hr (hR ▸ Finset.mem_inter.mpr ⟨hm, hx⟩)
  refine ⟨C, hc, ?_, ?_⟩
  · rw [Finset.disjoint_insert_right]
    exact ⟨hxC, ht⟩
  · rw [← hR]
    ext i; simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro ⟨hi, _, hu⟩; exact ⟨hi, hu⟩
    · rintro ⟨hi, hu⟩; exact ⟨hi, (fun he => hxC (he ▸ hi)), hu⟩

theorem ClauseThreat.empty_loses {φ : Formula} {U T : Finset (Fin φ.nvars)}
    (h : ClauseThreat φ U T ∅) (turn : Bool) : ¬TrueWins φ U T turn := by
  intro hw
  obtain ⟨C, hC, hT, hU⟩ := h
  obtain ⟨i, hiC, hi⟩ := cnf_possible φ U T turn hw C hC
  rcases Finset.mem_union.mp hi with hi | hi
  · exact Finset.disjoint_left.mp hT hiC hi
  · have hh := Finset.mem_inter.mpr ⟨hiC, hi⟩
    rw [hU] at hh
    exact Finset.notMem_empty i hh

theorem ClauseThreat.singleton_false_loses {φ : Formula} {U T : Finset (Fin φ.nvars)}
    {x : Fin φ.nvars} (h : ClauseThreat φ U T {x}) : ¬TrueWins φ U T false := by
  have hx : x ∈ U := h.subset (Finset.mem_singleton_self x)
  intro hw
  have child := (cnf_false φ U T (Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩)).mp hw x hx
  have he : ClauseThreat φ (U.erase x) T ∅ := by simpa using h.assignFalse x
  exact he.empty_loses true child

theorem ClauseThreat.forced_true {φ : Formula} {U T : Finset (Fin φ.nvars)}
    {x : Fin φ.nvars} (h : ClauseThreat φ U T {x}) :
    TrueWins φ U T true ↔ TrueWins φ (U.erase x) (insert x T) false := by
  have hx : x ∈ U := h.subset (Finset.mem_singleton_self x)
  rw [cnf_true φ U T (Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩)]
  constructor
  · rintro ⟨y, hy, hw⟩
    by_cases he : y = x
    · simpa [he] using hw
    · exact ((h.assignTrue y hy (by simpa using he)).singleton_false_loses hw).elim
  · intro hw; exact ⟨x, hx, hw⟩

theorem two_singletons_lose {φ : Formula} {U T : Finset (Fin φ.nvars)}
    {x y : Fin φ.nvars} (hx : ClauseThreat φ U T {x}) (hy : ClauseThreat φ U T {y})
    (hne : x ≠ y) : ¬TrueWins φ U T true := by
  intro hw
  have hu : x ∈ U := hx.subset (Finset.mem_singleton_self x)
  have child := hx.forced_true.mp hw
  exact (hy.assignTrue x hu (by simpa using hne)).singleton_false_loses child

theorem common_vertex_forced_false (φ : Formula) (U T : Finset (Fin φ.nvars))
    (x : Fin φ.nvars) (hx : x ∈ U)
    (hcommon : ∀ C ∈ φ.clauses, (∃ i ∈ C, i ∈ T) ∨ x ∈ C) :
    TrueWins φ U T false ↔ TrueWins φ (U.erase x) T true := by
  rw [cnf_false φ U T (Finset.nonempty_iff_ne_empty.mp ⟨x, hx⟩)]
  refine ⟨fun h => h x hx, ?_⟩
  intro hw y hy
  by_cases he : y = x
  · simpa [he] using hw
  · have hx' : x ∈ U.erase y := Finset.mem_erase.mpr ⟨Ne.symm he, hx⟩
    apply (cnf_true φ _ _ (Finset.nonempty_iff_ne_empty.mp ⟨x, hx'⟩)).mpr
    refine ⟨x, hx', cnf_of_satisfied φ _ _ false ?_⟩
    intro C hC
    rcases hcommon C hC with ⟨i, hi, ht⟩ | hxC
    · exact ⟨i, hi, Finset.mem_insert_of_mem ht⟩
    · exact ⟨x, hxC, Finset.mem_insert_self _ _⟩

end Lax689614Proofs
