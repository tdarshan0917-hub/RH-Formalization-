import RHFormalization.BTailSummedBound
import RHFormalization.PrimeWellEnvelopeLemmaB
import RHFormalization.ShiftedLaplacePrimeSummable
import Mathlib

/-!
# BTailMassBound — C5: bTailMass ≤ (log4+4)·e^{admR n}/2

ROUTE CARD
1. Target: per-pair ‖w(q)‖·e^{−center/2} = Λ(natValue)/natValue ≤
   Λ(natValue)/2 (natValue ≥ 2); reindex along natValue (banked
   injectivity, Dirichlet-form precedent moves verbatim); Chebyshev
   vonMangoldt_partial_sum_le. Chebyshev-crude √(n+2)-order growth;
   Mertens log refinement is an optional later upgrade.
2. Consumer: composition with C4 → explicit half-plane bTail growth.
3. Raw B on Ω? NO. hstar hypothesis? NONE.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open ArithmeticFunction
open scoped BigOperators

/-- Per-pair: the massed weight equals `Λ(natValue)/natValue`. -/
theorem weight_center_decay_eq (q : PrimePowerPair) (hv : IsPrimePowerPair q) :
    ‖q.weightC‖ * Real.exp (-(q.center / 2))
      = (vonMangoldt q.natValue : ℝ) / ((q.natValue : ℕ) : ℝ) := by
  have h2 : (2 : ℕ) ≤ q.natValue := by
    calc (2 : ℕ) ≤ q.p := hv.1.two_le
      _ ≤ q.p ^ q.m := Nat.le_self_pow hv.2.ne' q.p
      _ = q.natValue := rfl
  have hpos : (0 : ℝ) < ((q.natValue : ℕ) : ℝ) := by
    have : (2:ℝ) ≤ ((q.natValue : ℕ) : ℝ) := by exact_mod_cast h2
    linarith
  have hvm : (vonMangoldt q.natValue : ℝ) = Real.log ((q.p : ℕ) : ℝ) := by
    have hnv : q.natValue = q.p ^ q.m := rfl
    rw [hnv, ArithmeticFunction.vonMangoldt_apply_pow hv.2.ne',
      ArithmeticFunction.vonMangoldt_apply_prime hv.1]
  have hwnorm : ‖q.weightC‖ = Real.log ((q.p : ℕ) : ℝ)
      / Real.sqrt ((q.natValue : ℕ) : ℝ) := by
    unfold PrimePowerPair.weightC PrimePowerPair.weightReal
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [if_pos hv]
    apply abs_of_nonneg
    have hlogp : (0:ℝ) ≤ Real.log ((q.p : ℕ) : ℝ) := by
      apply Real.log_nonneg
      have : (2:ℝ) ≤ ((q.p : ℕ) : ℝ) := by exact_mod_cast hv.1.two_le
      linarith
    positivity
  have hexp : Real.exp (-(q.center / 2))
      = 1 / Real.sqrt ((q.natValue : ℕ) : ℝ) := by
    unfold PrimePowerPair.center
    rw [show -(Real.log ((q.natValue : ℕ) : ℝ) / 2)
        = (-(1/2)) * Real.log ((q.natValue : ℕ) : ℝ) by ring]
    rw [mul_comm, Real.exp_mul, Real.exp_log hpos]
    rw [Real.rpow_neg hpos.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hwnorm, hexp, hvm]
  have hs : Real.sqrt ((q.natValue : ℕ) : ℝ) ≠ 0 := by positivity
  have hss : Real.sqrt ((q.natValue : ℕ) : ℝ)
      * Real.sqrt ((q.natValue : ℕ) : ℝ) = ((q.natValue : ℕ) : ℝ) :=
    Real.mul_self_sqrt hpos.le
  rw [div_mul_div_comm, mul_one, hss]

/-- **C5: the tail mass Chebyshev bound.** -/
theorem bTailMass_le (n : ℕ) :
    bTailMass n ≤ (Real.log 4 + 4) * Real.exp (admR n) / 2 := by
  classical
  have hmem : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      IsPrimePowerPair q ∧ q.center ≤ admR n := by
    intro q hq
    first
      | exact (valid_primePower_center_le_finite (admR n)).mem_toFinset.mp hq
      | simpa using (valid_primePower_center_le_finite (admR n)).mem_toFinset.mp hq
  have hstep1 : bTailMass n
      = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          (vonMangoldt q.natValue : ℝ) / ((q.natValue : ℕ) : ℝ) := by
    unfold bTailMass
    refine Finset.sum_congr rfl (fun q hq => ?_)
    exact weight_center_decay_eq q (hmem q hq).1
  have hstep2 : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      (vonMangoldt q.natValue : ℝ) / ((q.natValue : ℕ) : ℝ)
        ≤ (vonMangoldt q.natValue : ℝ) / 2 := by
    intro q hq
    have hv := (hmem q hq).1
    have h2 : (2 : ℕ) ≤ q.natValue := by
      calc (2 : ℕ) ≤ q.p := hv.1.two_le
        _ ≤ q.p ^ q.m := Nat.le_self_pow hv.2.ne' q.p
        _ = q.natValue := rfl
    have h2r : (2:ℝ) ≤ ((q.natValue : ℕ) : ℝ) := by exact_mod_cast h2
    apply div_le_div_of_nonneg_left _ (by norm_num) h2r
    exact vonMangoldt_nonneg
  have hstep3 : (∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
        (vonMangoldt q.natValue : ℝ) / 2)
      = (∑ k ∈ (activePrimePowerPairsCenterBelow (admR n)).image
          PrimePowerPair.natValue, (vonMangoldt k : ℝ) / 2) := by
    symm
    refine Finset.sum_image ?_
    intro a ha b hb hab
    exact natValue_injOn_valid (hmem a ha).1 (hmem b hb).1 hab
  have hsub : (activePrimePowerPairsCenterBelow (admR n)).image
      PrimePowerPair.natValue ⊆ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊ := by
    intro k hk
    obtain ⟨q, hqmem, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hvalid, hcenter⟩ := hmem q hqmem
    have h2 : (2 : ℕ) ≤ q.natValue := by
      calc (2 : ℕ) ≤ q.p := hvalid.1.two_le
        _ ≤ q.p ^ q.m := Nat.le_self_pow hvalid.2.ne' q.p
        _ = q.natValue := rfl
    have hpos : (0 : ℝ) < ((q.natValue : ℕ) : ℝ) := by
      have : (2:ℝ) ≤ ((q.natValue : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    have hle_exp : ((q.natValue : ℕ) : ℝ) ≤ Real.exp (admR n) := by
      have hexp := Real.exp_le_exp.mpr hcenter
      rwa [PrimePowerPair.center, Real.exp_log hpos] at hexp
    refine Finset.mem_Ioc.mpr ⟨by omega, Nat.le_floor hle_exp⟩
  calc bTailMass n
      = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          (vonMangoldt q.natValue : ℝ) / ((q.natValue : ℕ) : ℝ) := hstep1
    _ ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          (vonMangoldt q.natValue : ℝ) / 2 :=
        Finset.sum_le_sum hstep2
    _ = ∑ k ∈ (activePrimePowerPairsCenterBelow (admR n)).image
          PrimePowerPair.natValue, (vonMangoldt k : ℝ) / 2 := hstep3
    _ ≤ ∑ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊, (vonMangoldt k : ℝ) / 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k _ _ => div_nonneg vonMangoldt_nonneg (by norm_num))
    _ = (∑ k ∈ Finset.Ioc 0 ⌊Real.exp (admR n)⌋₊, (vonMangoldt k : ℝ)) / 2 := by
        rw [← Finset.sum_div]
    _ ≤ (Real.log 4 + 4) * Real.exp (admR n) / 2 := by
        have h := vonMangoldt_partial_sum_le (Real.exp (admR n))
          (Real.exp_nonneg _)
        linarith

#print axioms weight_center_decay_eq
#print axioms bTailMass_le

end

end RHFormalization
