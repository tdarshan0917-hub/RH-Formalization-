import RHFormalization.ConcretePrimePowerEnumeration
import RHFormalization.PrimePowerDFiniteStage
import RHFormalization.CorrectedResolventPayload
import Mathlib

/-!
# Eventually-superset: resolventIndices (primePowerStage n) ⊇ any fixed finset, eventually

The correct Finset→ℕ reindex bridge. `PrimePowerPair` is a raw type (IsPrimePowerPair is a
separate predicate), so the cutoff finsets do NOT exhaust the whole type; full
`tendsto_atTop_finset_of_monotone` is unprovable. Instead: any FIXED finset I₀ of pairs is
eventually contained in `resolventIndices (primePowerStage n)`, because I₀ is finite and each
of its valid pairs enters once n+1 exceeds its center. This is exactly what's needed to
transfer `∀ᶠ I in Finset.atTop, P I` to `∀ᶠ n in ℕ.atTop, P (resolventIndices (primePowerStage n))`.
-/

namespace RHFormalization
open Filter Topology
open scoped Classical

/-- `concretePrimePowerBelowCutoff` is monotone in the cutoff. -/
theorem concretePrimePowerBelowCutoff_mono :
    Monotone concretePrimePowerBelowCutoff := by
  intro R1 R2 hR q hq
  unfold concretePrimePowerBelowCutoff at hq ⊢
  rw [Finset.mem_filter] at hq ⊢
  obtain ⟨hqrange, hqpp, hqcenter⟩ := hq
  refine ⟨?_, hqpp, le_trans hqcenter hR⟩
  rw [Finset.mem_product] at hqrange ⊢
  have hexp : ⌈Real.exp R1⌉₊ ≤ ⌈Real.exp R2⌉₊ :=
    Nat.ceil_le_ceil (Real.exp_le_exp.mpr hR)
  refine ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hqrange.1) (by omega)),
          Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hqrange.2) (by omega))⟩

/-- A single valid pair `q` enters `resolventIndices (primePowerStage n)` once `n+1 ≥ center`. -/
theorem mem_resolventIndices_of_large
    (q : PrimePowerPair) (hpp : IsPrimePowerPair q) (n : ℕ) (hn : q.center ≤ (n : ℝ) + 1) :
    q ∈ resolventIndices (primePowerStage n) := by
  unfold resolventIndices
  have := concretePrimePowerEnum.h_mem_belowCutoff (primePowerStage n).R q hpp
  exact this (by show q.center ≤ (n : ℝ) + 1; exact hn)

/-- **The reindex bridge.** Any fixed finset `I₀` of *valid* prime-power pairs is eventually
contained in `resolventIndices (primePowerStage n)`. -/
theorem resolventIndices_eventually_superset
    (I0 : Finset PrimePowerPair) (hI0valid : ∀ q ∈ I0, IsPrimePowerPair q) :
    ∀ᶠ n in atTop, I0 ⊆ resolventIndices (primePowerStage n) := by
  -- pick a threshold exceeding every center in I0
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ q ∈ I0, q.center ≤ (N : ℝ) + 1 := by
    rcases I0.eq_empty_or_nonempty with he | hne
    · exact ⟨0, by simp [he]⟩
    · obtain ⟨qmax, hqmaxmem, hqmax⟩ := I0.exists_max_image (fun q => q.center) hne
      obtain ⟨N, hNge⟩ := exists_nat_ge qmax.center
      refine ⟨N, fun q hq => ?_⟩
      have h1 : q.center ≤ qmax.center := hqmax q hq
      have h2 : qmax.center ≤ (N : ℝ) := hNge
      linarith
  filter_upwards [eventually_ge_atTop N] with n hn
  intro q hq
  have hcenter : q.center ≤ (n : ℝ) + 1 := by
    have := hN q hq
    have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact mem_resolventIndices_of_large q (hI0valid q hq) n hcenter

#print axioms resolventIndices_eventually_superset

end RHFormalization
