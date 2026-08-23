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

#print axioms denseIgal
#print axioms denseCenteredTrace
#print axioms continuousOn_galerkinT_diag
#print axioms intervalIntegrable_weight_galerkinT_diag

end

end RHFormalization
