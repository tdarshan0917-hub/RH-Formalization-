import RHFormalization.DenseFctrBound
import RHFormalization.DenseFiniteRIdentity
import Mathlib

/-!
# DenseCenteredTrace — B(i)-7a: the centered trace object and its inputs

In the `denseKernelN` normalization (K_n(u,s) = (1/L)·Σ_m T(u)_mm/(s+¼+λ_m)):

  denseIgal n s          := ∫₀^{admR n} e^{u/2}·K_n(u,s) du
  denseCenteredTrace n s := (1/L)·Σ_m (C_n)_mm · 1/(s+¼+λ_m)     ( = 2τ_n(D_s C_n) )

with C_n = denseCenteredMatrix (B(i)-1). This file defines both and banks
the continuity/integrability of each diagonal T-entry in u on [0, admR n],
which the sum/integral swap (7a-I) and the identity
  2·denseFreePairedTransform − denseIgal = denseCenteredTrace   (7a)
consume.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- The Galerkin-side weighted integral `I^gal`. -/
def denseIgal (n : ℕ) (s : ℂ) : ℂ :=
  ∫ u in (0:ℝ)..(admR n), ((Real.exp (u/2) : ℝ) : ℂ) * denseKernelN n u s

/-- **The centered trace** `2τ_n(D_s C_n)` in the `denseKernelN` normalization. -/
def denseCenteredTrace (n : ℕ) (s : ℂ) : ℂ :=
  ((1 / denseL n : ℝ) : ℂ) *
    ∑ m : Fin (denseN n),
      ((denseCenteredMatrix n m m : ℝ) : ℂ) *
        (1 / (s + (1/4 : ℂ) + ((galerkinLam (denseL n) (m : ℕ) : ℝ) : ℂ)))

/-- Each diagonal `T`-entry is continuous in the center on `[0, admR n]`
(closed form `TmatrixElement_diag_eval`, as in `continuousOn_denseKernelN_u`). -/
theorem continuousOn_galerkinT_diag (n : ℕ) (m : Fin (denseN n)) :
    ContinuousOn (fun u : ℝ => galerkinT (N := denseN n) (denseL n) u m m)
      (Set.Icc (0:ℝ) (admR n)) := by
  have hL0 : (0:ℝ) < denseL n := denseL_pos n
  have hentry : ∀ u ∈ Set.Icc (0:ℝ) (admR n),
      galerkinT (N := denseN n) (denseL n) u m m
        = (2 / denseL n) *
            ((denseL n - u) / 2
              * Real.cos ((((m:ℕ)+1 : ℕ) : ℝ) * Real.pi * u / denseL n)
            + denseL n / (2 * (((m:ℕ)+1 : ℕ) : ℝ) * Real.pi)
              * Real.sin ((((m:ℕ)+1 : ℕ) : ℝ) * Real.pi * u / denseL n)) := by
    intro u hu
    show (2 / denseL n) * TmatrixElement (denseL n) u ((m:ℕ)+1) ((m:ℕ)+1) = _
    rw [TmatrixElement_diag_eval (denseL n) u hL0 hu.1
      (le_of_lt (lt_of_le_of_lt hu.2 (admR_lt_denseL n)))
      ((m:ℕ)+1) (Nat.succ_ne_zero _)]
  apply ContinuousOn.congr _ hentry
  apply Continuous.continuousOn
  fun_prop

/-- The weighted diagonal entry `e^{u/2}·T(u)_mm` is interval-integrable on `[0, admR n]`. -/
theorem intervalIntegrable_weight_galerkinT_diag (n : ℕ) (m : Fin (denseN n)) :
    IntervalIntegrable
      (fun u : ℝ => Real.exp (u/2) * galerkinT (N := denseN n) (denseL n) u m m)
      MeasureTheory.volume 0 (admR n) := by
  have hR0 : (0:ℝ) ≤ admR n := (admR_pos n).le
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hR0]
  exact ((by fun_prop : Continuous fun u : ℝ => Real.exp (u/2)).continuousOn).mul
    (continuousOn_galerkinT_diag n m)


/-! ## 7a: sum/integral swap and the trace identity
`2·denseFreePairedTransform − denseIgal = denseCenteredTrace`. -/

/-- Complex-coerced weighted diagonal entry times a constant is integrable. -/
theorem intervalIntegrable_weight_galerkinT_diag_C (n : ℕ) (m : Fin (denseN n)) (c : ℂ) :
    IntervalIntegrable
      (fun u : ℝ =>
        ((Real.exp (u/2) * galerkinT (N := denseN n) (denseL n) u m m : ℝ) : ℂ) * c)
      MeasureTheory.volume 0 (admR n) := by
  have hR0 : (0:ℝ) ≤ admR n := (admR_pos n).le
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hR0]
  apply ContinuousOn.mul _ continuousOn_const
  apply Complex.continuous_ofReal.comp_continuousOn
  exact ((by fun_prop : Continuous fun u : ℝ => Real.exp (u/2)).continuousOn).mul
    (continuousOn_galerkinT_diag n m)

/-- **7a-I**: `I^gal` in trace form — the integral passes inside the finite sum. -/
theorem denseIgal_eq_trace_form (n : ℕ) (s : ℂ) :
    denseIgal n s
      = ((1 / denseL n : ℝ) : ℂ) *
          ∑ m : Fin (denseN n),
            (((∫ u in (0:ℝ)..(admR n),
                Real.exp (u/2) * galerkinT (N := denseN n) (denseL n) u m m) : ℝ) : ℂ) *
              (1 / (s + (1/4 : ℂ) + ((galerkinLam (denseL n) (m : ℕ) : ℝ) : ℂ))) := by
  unfold denseIgal
  have hint : (fun u : ℝ => ((Real.exp (u/2) : ℝ) : ℂ) * denseKernelN n u s)
      = fun u : ℝ => ((1 / denseL n : ℝ) : ℂ) *
          ∑ m : Fin (denseN n),
            ((Real.exp (u/2) * galerkinT (N := denseN n) (denseL n) u m m : ℝ) : ℂ) *
              (1 / (s + (1/4 : ℂ) + ((galerkinLam (denseL n) (m : ℕ) : ℝ) : ℂ))) := by
    funext u
    unfold denseKernelN
    rw [galerkinSpikeTransform_eq_diag_pairing]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    push_cast
    ring
  rw [hint, intervalIntegral.integral_const_mul (𝕜 := ℂ),
    intervalIntegral.integral_finset_sum
      (fun m _ => intervalIntegrable_weight_galerkinT_diag_C n m _)]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [intervalIntegral.integral_mul_const (𝕜 := ℂ), intervalIntegral.integral_ofReal]

/-- **7a-S**: `P^gal = 2·denseFreePairedTransform` in trace form. -/
theorem two_densePaired_eq_trace_form (n : ℕ) (s : ℂ) :
    (2 : ℂ) * denseFreePairedTransform n s
      = ((1 / denseL n : ℝ) : ℂ) *
          ∑ m : Fin (denseN n),
            (((∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
                q.weightReal * galerkinT (N := denseN n) (denseL n) q.center m m) : ℝ) : ℂ) *
              (1 / (s + (1/4 : ℂ) + ((galerkinLam (denseL n) (m : ℕ) : ℝ) : ℂ))) := by
  rw [two_densePaired_eq_Pgal]
  unfold denseKernelN
  simp only [galerkinSpikeTransform_eq_diag_pairing,
    PrimePowerPair.weightC_eq_coe_weightReal]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun m _ => ?_))
  ring

/-- **B(i)-7a**: `P^gal − I^gal = 2τ_n(D_s C_n)`. -/
theorem two_densePaired_sub_Igal_eq_trace (n : ℕ) (s : ℂ) :
    (2 : ℂ) * denseFreePairedTransform n s - denseIgal n s
      = denseCenteredTrace n s := by
  rw [two_densePaired_eq_trace_form, denseIgal_eq_trace_form]
  unfold denseCenteredTrace
  simp only [denseCenteredMatrix_apply, denseCenteredEntry]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun m _ => ?_)
  push_cast
  ring

#print axioms denseIgal
#print axioms denseCenteredTrace
#print axioms continuousOn_galerkinT_diag
#print axioms intervalIntegrable_weight_galerkinT_diag

#print axioms intervalIntegrable_weight_galerkinT_diag_C
#print axioms denseIgal_eq_trace_form
#print axioms two_densePaired_eq_trace_form
#print axioms two_densePaired_sub_Igal_eq_trace

end

end RHFormalization
