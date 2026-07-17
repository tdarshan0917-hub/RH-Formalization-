import Mathlib
import RHFormalization.PrimeWellEnvelopeLemmaC
import RHFormalization.PrimePotentialEnvelopeBound
import RHFormalization.EnvDomShellSummable
set_option autoImplicit false
set_option maxHeartbeats 1000000
open ArithmeticFunction Real Finset

namespace RHFormalization

/-- **A6, dyadic shell weighted-bump bound (√n normalization).** On a dyadic shell
`n ∈ (2^k, 2^(k+1)]`, the √n-weighted Gaussian-bump contribution is bounded by the
shell-mass bound (`weighted_shell_bound`, the manuscript `Λ(n)/√n` normalization)
times the bump peak. This is the per-shell head of the A.ENV-DOM bridge: it connects
the live coefficient `Λ(n)/√n` to a `√(2^k)`-growth majorant, which the envelope
ladder then absorbs. Uses the FROZEN `Λ(q)/√q` normalization (manuscript p.101). -/
theorem dyadic_shell_bump_weight_le
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    ∑ n ∈ Finset.Ioc (2^k) (2^(k+1)),
        (vonMangoldt n / Real.sqrt n) * gaussBump δ 0
      ≤ 2 * (Real.log 4 + 4) * Real.sqrt (2^k) * (1 / Real.sqrt (2 * Real.pi * δ ^ 2)) := by
  have hpeak : gaussBump δ 0 ≤ 1 / Real.sqrt (2 * Real.pi * δ ^ 2) :=
    gaussBump_le_peak_delta δ hδ 0
  have hpeak_nn : 0 ≤ gaussBump δ 0 := le_of_lt (gaussBump_pos δ hδ 0)
  -- factor the constant bump peak out of the shell sum
  have hfactor : ∑ n ∈ Finset.Ioc (2^k) (2^(k+1)),
        (vonMangoldt n / Real.sqrt n) * gaussBump δ 0
      = (∑ n ∈ Finset.Ioc (2^k) (2^(k+1)), vonMangoldt n / Real.sqrt n) * gaussBump δ 0 := by
    rw [← Finset.sum_mul]
  rw [hfactor]
  have hmass := weighted_shell_bound k
  calc (∑ n ∈ Finset.Ioc (2^k) (2^(k+1)), vonMangoldt n / Real.sqrt n) * gaussBump δ 0
      ≤ (2 * (Real.log 4 + 4) * Real.sqrt (2^k)) * gaussBump δ 0 :=
        mul_le_mul_of_nonneg_right hmass hpeak_nn
    _ ≤ (2 * (Real.log 4 + 4) * Real.sqrt (2^k)) * (1 / Real.sqrt (2 * Real.pi * δ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hpeak
        positivity
    _ = 2 * (Real.log 4 + 4) * Real.sqrt (2^k) * (1 / Real.sqrt (2 * Real.pi * δ ^ 2)) := by
        ring

#print axioms dyadic_shell_bump_weight_le

end RHFormalization
