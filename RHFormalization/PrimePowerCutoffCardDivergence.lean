import RHFormalization.ConcretePrimePowerEnumeration
import RHFormalization.PrimePowerDFiniteStage
import RHFormalization.CorrectedResolventPayload
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter Finset

private theorem prime_pair_mem_cutoff {p : ℕ} (hp : Nat.Prime p) {M : ℕ} (hpM : p < M)
    {R : ℝ} (hR : Real.log (M : ℝ) ≤ R) (hM1 : 1 ≤ M) :
    ((p, 1) : PrimePowerPair) ∈ concretePrimePowerBelowCutoff R := by
  classical
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM1
  have hexp : (M : ℝ) ≤ Real.exp R := by
    calc (M:ℝ) = Real.exp (Real.log M) := (Real.exp_log hMpos).symm
      _ ≤ Real.exp R := Real.exp_le_exp.mpr hR
  have hpexp : (p:ℝ) ≤ Real.exp R := le_trans (by exact_mod_cast le_of_lt hpM) hexp
  have hp_le_ceil : p ≤ ⌈Real.exp R⌉₊ :=
    Nat.cast_le.mp (le_trans hpexp (Nat.le_ceil _))
  have hp_lt_ceil : p < ⌈Real.exp R⌉₊ + 1 := Nat.lt_succ_of_le hp_le_ceil
  have h1_lt_ceil : 1 < ⌈Real.exp R⌉₊ + 1 := by
    have : 1 ≤ ⌈Real.exp R⌉₊ := le_trans hp.one_lt.le hp_le_ceil
    omega
  have hcenter_le : PrimePowerPair.center (p, 1) ≤ R := by
    have hppos : (0:ℝ) < p := by exact_mod_cast hp.pos
    have hval : PrimePowerPair.center (p, 1) = Real.log (p:ℝ) := by
      unfold PrimePowerPair.center PrimePowerPair.natValue
      norm_num [PrimePowerPair.p, PrimePowerPair.m]
    rw [hval]
    have hlog : Real.log (p:ℝ) ≤ Real.log (M:ℝ) :=
      Real.log_le_log hppos (by exact_mod_cast le_of_lt hpM)
    linarith
  have hvalid : IsPrimePowerPair ((p,1) : PrimePowerPair) := ⟨hp, by unfold PrimePowerPair.m; norm_num⟩
  rw [concretePrimePowerBelowCutoff, Finset.mem_filter]
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hp_lt_ceil,
    Finset.mem_range.mpr h1_lt_ceil⟩, hvalid, hcenter_le⟩

private theorem card_cutoff_ge_primesBelow {M : ℕ} (hM1 : 1 ≤ M) {R : ℝ}
    (hR : Real.log (M : ℝ) ≤ R) :
    (Nat.primesBelow M).card ≤ (concretePrimePowerBelowCutoff R).card := by
  apply Finset.card_le_card_of_injOn (fun p => ((p, 1) : PrimePowerPair))
  · intro p hp
    have hp' := hp
    rw [Finset.mem_coe, Nat.mem_primesBelow] at hp'
    exact prime_pair_mem_cutoff hp'.2 hp'.1 hR hM1
  · intro a _ b _ hab
    simpa using hab

theorem concretePrimePowerBelowCutoff_card_atTop :
    Tendsto (fun R : ℝ => (concretePrimePowerBelowCutoff R).card) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  obtain ⟨M, hM⟩ : ∃ M : ℕ, B ≤ (Nat.primesBelow M).card := by
    refine ⟨Nat.nth Nat.Prime B + 1, ?_⟩
    have hsub : (Finset.range (B+1)).image (Nat.nth Nat.Prime) ⊆
        Nat.primesBelow (Nat.nth Nat.Prime B + 1) := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨i, hi, rfl⟩ := hp
      rw [Finset.mem_range] at hi
      rw [Nat.mem_primesBelow]
      refine ⟨?_, Nat.prime_nth_prime i⟩
      have hmono : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime B :=
        Nat.nth_monotone Nat.infinite_setOf_prime (Nat.lt_succ_iff.mp hi)
      exact Nat.lt_succ_of_le hmono
    have hcard_img : ((Finset.range (B+1)).image (Nat.nth Nat.Prime)).card = B + 1 := by
      rw [Finset.card_image_of_injective _ (Nat.nth_injective Nat.infinite_setOf_prime),
          Finset.card_range]
    calc B ≤ B + 1 := by omega
      _ = ((Finset.range (B+1)).image (Nat.nth Nat.Prime)).card := hcard_img.symm
      _ ≤ (Nat.primesBelow (Nat.nth Nat.Prime B + 1)).card := Finset.card_le_card hsub
  refine ⟨Real.log (M : ℝ), fun R hR => ?_⟩
  rcases Nat.eq_zero_or_pos B with hB0 | hBpos
  · subst hB0; exact Nat.zero_le _
  · have hM1 : 1 ≤ M := by
      by_contra h
      push_neg at h
      interval_cases M
      · rw [Nat.primesBelow_zero] at hM; simp at hM; omega
    exact le_trans hM (card_cutoff_ge_primesBelow hM1 hR)

end
end RHFormalization
