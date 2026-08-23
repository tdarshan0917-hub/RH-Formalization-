import RHFormalization.DenseCenteredTrace
import RHFormalization.DenseFctrRateBound
import Mathlib

/-!
# DenseBridgeIdentity — B(i)-7: the bridge identity and the bounded remainder

GPT-countersigned B7 (η = 0, shortest live remainder E_n = F^ctr − E⁰):

  2·denseFreePairedTransform − compensatorM
      = denseCenteredTrace + denseFctr − denseE0            on Ω,

from 7a (P^gal − I^gal = 2τ(D_s C_n)), 7b (F^ctr = I^gal − I^cont, integral_sub),
and the finite-R identity (I^cont = M − E⁰). The remainder
denseRemainder := denseFctr − denseE0 is compact-uniformly bounded
(B6 `denseFctr_bounded_on_compact` + B5 `denseE0_bounded_on_compact`).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- Weighted finite kernel is interval-integrable on `[0, admR n]`. -/
theorem intervalIntegrable_weight_denseKernelN (n : ℕ) (s : ℂ) :
    IntervalIntegrable
      (fun u : ℝ => ((Real.exp (u/2) : ℝ) : ℂ) * denseKernelN n u s)
      MeasureTheory.volume 0 (admR n) := by
  have hR0 : (0:ℝ) ≤ admR n := (admR_pos n).le
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hR0]
  apply ContinuousOn.mul _ (continuousOn_denseKernelN_u n s)
  apply Continuous.continuousOn
  exact Complex.continuous_ofReal.comp (by fun_prop)

/-- Weighted continuum kernel is interval-integrable. -/
theorem intervalIntegrable_weight_kernel (n : ℕ) (s : ℂ) :
    IntervalIntegrable
      (fun u : ℝ => ((Real.exp (u/2) : ℝ) : ℂ) * shiftedLaplaceHeatKernelC u s)
      MeasureTheory.volume 0 (admR n) := by
  apply Continuous.intervalIntegrable
  exact (Complex.continuous_ofReal.comp (by fun_prop)).mul (continuous_kernel_u s)

/-- **7b**: `F^ctr = I^gal − I^cont`. -/
theorem denseFctr_eq_Igal_sub_Icont (n : ℕ) (s : ℂ) :
    denseFctr n s
      = denseIgal n s
        - ∫ u in (0:ℝ)..(admR n),
            ((Real.exp (u/2) : ℝ) : ℂ) * shiftedLaplaceHeatKernelC u s := by
  unfold denseFctr denseIgal
  rw [← intervalIntegral.integral_sub (intervalIntegrable_weight_denseKernelN n s)
    (intervalIntegrable_weight_kernel n s)]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  ring

/-- **B(i)-7 bridge identity** on Ω. -/
theorem denseBridge_identity (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    (2 : ℂ) * denseFreePairedTransform n s - compensatorM n s
      = denseCenteredTrace n s + denseFctr n s - denseE0 s := by
  have h1 := two_densePaired_sub_Igal_eq_trace n s
  have h2 := denseFctr_eq_Igal_sub_Icont n s
  rw [finiteR_kernel_integral_eq' n hs] at h2
  linear_combination h1 - h2

/-- The B7 remainder `E_n = F^ctr − E⁰`. -/
def denseRemainder (n : ℕ) (s : ℂ) : ℂ := denseFctr n s - denseE0 s

/-- Bridge identity in remainder form. -/
theorem denseBridge_identity' (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    (2 : ℂ) * denseFreePairedTransform n s - compensatorM n s
      = denseCenteredTrace n s + denseRemainder n s := by
  unfold denseRemainder
  rw [denseBridge_identity n hs]
  ring

/-- **B(i)-7 remainder bound**: `E_n` is bounded on every compact `K ⊆ Ω`,
uniformly in `n`. -/
theorem denseRemainder_bounded_on_compact
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ M : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖denseRemainder n s‖ ≤ M := by
  obtain ⟨M₁, hM₁⟩ := denseFctr_bounded_on_compact K hK hKΩ
  obtain ⟨M₂, _, hM₂⟩ := denseE0_bounded_on_compact K hK hKΩ
  refine ⟨M₁ + M₂, fun n s hs => ?_⟩
  unfold denseRemainder
  calc ‖denseFctr n s - denseE0 s‖
      ≤ ‖denseFctr n s‖ + ‖denseE0 s‖ := norm_sub_le _ _
    _ ≤ M₁ + M₂ := add_le_add (hM₁ n s hs) (hM₂ s hs)

#print axioms intervalIntegrable_weight_denseKernelN
#print axioms intervalIntegrable_weight_kernel
#print axioms denseFctr_eq_Igal_sub_Icont
#print axioms denseBridge_identity
#print axioms denseRemainder
#print axioms denseBridge_identity'
#print axioms denseRemainder_bounded_on_compact

end

end RHFormalization
