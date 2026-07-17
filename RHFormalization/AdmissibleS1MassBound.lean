import RHFormalization.ConcretePrimePowerEnumeration
import RHFormalization.AppendixDActiveSpikeCodesFromCenterCutoff
import RHFormalization.GalerkinOverlapAndV9
import RHFormalization.SboundUniform
import RHFormalization.AdmissibleWeightNonneg

/-!
# RHFormalization.AdmissibleS1MassBound

**BRICK 4b-iii(c): the elementary S₁ mass bound.**

`S1mass R = Σ_{codes below R} ppWeightReal ≤ 2·(e^R + 2)`.

Route: banked uniform weight bound `abs_ppWeightReal_le_two` × an
elementary count. The count is LINEAR in `e^R` via the injection
`q ↦ p^m` into `[0, ⌈e^R⌉]` (injective on valid pairs by unique
factorization) — the crude product-grid card `(⌈e^R⌉+1)²` would NOT
suffice downstream. At the schedule `admR n = log(n+2)/2` this gives
`S₁ ≲ √(n+2)`, so the second-resolvent residual closes at `~ 1/(n+2)`.
Generic in R; schedule instantiation deferred to the 4b-iv assembly.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/-- The prime-power mass below cutoff `R` (the manuscript's `S₁(R)`). -/
def S1mass (R : ℝ) : ℝ :=
  ∑ k ∈ activePrimePowerCodesCenterBelow R, ppWeightReal k

theorem S1mass_nonneg (R : ℝ) : 0 ≤ S1mass R :=
  Finset.sum_nonneg fun k _ => ppWeightReal_nonneg k

/-- **Linear count**: the concrete cutoff set injects into `[0, ⌈e^R⌉]`
via `q ↦ p^m` (unique factorization), so its card is ≤ `⌈e^R⌉ + 1`. -/
theorem card_concretePrimePowerBelowCutoff_le (R : ℝ) :
    (concretePrimePowerBelowCutoff R).card ≤ ⌈Real.exp R⌉₊ + 1 := by
  classical
  have hmaps : ∀ q ∈ concretePrimePowerBelowCutoff R,
      (fun q : PrimePowerPair => q.p ^ q.m) q
        ∈ Finset.range (⌈Real.exp R⌉₊ + 1) := by
    intro q hq
    have hmem := Finset.mem_filter.mp hq
    have hvalid : IsPrimePowerPair q := hmem.2.1
    have hcenter : q.center ≤ R := hmem.2.2
    have h2 : (2 : ℕ) ≤ q.p ^ q.m := by
      calc (2 : ℕ) ≤ q.p := hvalid.1.two_le
        _ ≤ q.p ^ q.m := Nat.le_self_pow hvalid.2.ne' q.p
    have hpos : (0 : ℝ) < ((q.p ^ q.m : ℕ) : ℝ) := by
      have h0 : 0 < q.p ^ q.m := lt_of_lt_of_le (by norm_num) h2
      exact_mod_cast h0
    have hlog : Real.log ((q.p ^ q.m : ℕ) : ℝ) ≤ R := by
      first
        | exact hcenter
        | simpa [PrimePowerPair.center, PrimePowerPair.natValue] using hcenter
    have hpow_le : ((q.p ^ q.m : ℕ) : ℝ) ≤ Real.exp R := by
      calc ((q.p ^ q.m : ℕ) : ℝ)
          = Real.exp (Real.log ((q.p ^ q.m : ℕ) : ℝ)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp R := Real.exp_le_exp.mpr hlog
    have hle : q.p ^ q.m ≤ ⌈Real.exp R⌉₊ := by
      have hceil : ((q.p ^ q.m : ℕ) : ℝ) ≤ ((⌈Real.exp R⌉₊ : ℕ) : ℝ) :=
        le_trans hpow_le (Nat.le_ceil _)
      exact_mod_cast hceil
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le hle
  have hinj : Set.InjOn (fun q : PrimePowerPair => q.p ^ q.m)
      ↑(concretePrimePowerBelowCutoff R) := by
    intro q hq q' hq' hval
    rw [Finset.mem_coe] at hq hq'
    have hvq : IsPrimePowerPair q := (Finset.mem_filter.mp hq).2.1
    have hvq' : IsPrimePowerPair q' := (Finset.mem_filter.mp hq').2.1
    simp only at hval
    have hpp : q.p = q'.p := by
      have h1 : q.p ∣ q'.p ^ q'.m := by
        rw [← hval]
        exact dvd_pow_self q.p hvq.2.ne'
      have h2 : q.p ∣ q'.p := hvq.1.dvd_of_dvd_pow h1
      exact (Nat.prime_dvd_prime_iff_eq hvq.1 hvq'.1).mp h2
    have hmm : q.m = q'.m := by
      apply Nat.pow_right_injective hvq.1.two_le
      show q.p ^ q.m = q.p ^ q'.m
      rw [hval, hpp]
    first
      | exact Prod.ext hpp hmm
      | exact Prod.ext_iff.mpr ⟨hpp, hmm⟩
      | · obtain ⟨qp, qm⟩ := q
          obtain ⟨qp', qm'⟩ := q'
          simp_all [PrimePowerPair.p, PrimePowerPair.m]
  calc (concretePrimePowerBelowCutoff R).card
      ≤ (Finset.range (⌈Real.exp R⌉₊ + 1)).card :=
        Finset.card_le_card_of_injOn
          (fun q : PrimePowerPair => q.p ^ q.m) hmaps hinj
    _ = ⌈Real.exp R⌉₊ + 1 := Finset.card_range _

/-- Card transfer to the active code set (image contracts, enumerations agree). -/
theorem card_activePrimePowerCodesCenterBelow_le (R : ℝ) :
    (activePrimePowerCodesCenterBelow R).card ≤ ⌈Real.exp R⌉₊ + 1 := by
  classical
  calc (activePrimePowerCodesCenterBelow R).card
      ≤ (activePrimePowerPairsCenterBelow R).card := Finset.card_image_le
    _ = (concretePrimePowerBelowCutoff R).card := by
        rw [activePairs_eq_concrete]
    _ ≤ ⌈Real.exp R⌉₊ + 1 := card_concretePrimePowerBelowCutoff_le R

/-- **THE S₁ BOUND**: `S₁(R) ≤ 2·(e^R + 2)`, fully elementary. -/
theorem S1mass_le (R : ℝ) : S1mass R ≤ 2 * (Real.exp R + 2) := by
  classical
  have hsum : S1mass R
      ≤ ((activePrimePowerCodesCenterBelow R).card : ℝ) * 2 := by
    have h : S1mass R ≤ ∑ _k ∈ activePrimePowerCodesCenterBelow R, (2 : ℝ) :=
      Finset.sum_le_sum fun k _ =>
        le_trans (le_abs_self _) (abs_ppWeightReal_le_two k)
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have hcardR : ((activePrimePowerCodesCenterBelow R).card : ℝ)
      ≤ Real.exp R + 2 := by
    have h1 : ((activePrimePowerCodesCenterBelow R).card : ℝ)
        ≤ ((⌈Real.exp R⌉₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast card_activePrimePowerCodesCenterBelow_le R
    have h2 : ((⌈Real.exp R⌉₊ : ℕ) : ℝ) < Real.exp R + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos R).le
    push_cast at h1
    linarith
  calc S1mass R
      ≤ ((activePrimePowerCodesCenterBelow R).card : ℝ) * 2 := hsum
    _ ≤ (Real.exp R + 2) * 2 :=
        mul_le_mul_of_nonneg_right hcardR (by norm_num)
    _ = 2 * (Real.exp R + 2) := by ring

#print axioms S1mass_nonneg
#print axioms card_concretePrimePowerBelowCutoff_le
#print axioms card_activePrimePowerCodesCenterBelow_le
#print axioms S1mass_le

end

end RHFormalization
