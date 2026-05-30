import RHFormalization.CanonicalPrimePowerProductWindowError

/-!
# RHFormalization.CanonicalPrimePowerMassGrowthWindow

Mass-growth/window-rate control for the canonical prime-power package.

This is not an RH endpoint.

The previous product-window layer reduced the D/H finite-to-limit passage to

  (∑ q in indices(alpha n), ‖q.weightC‖) * windowError s n → 0.

This file reduces that product condition to two more concrete estimates:

* a finite prime-weight mass growth bound
    ∑ q in indices(alpha n), ‖q.weightC‖ ≤ massGrowth n;

* a rate condition
    massGrowth n * windowError s n → 0.

This is closer to the actual Appendix-D cutoff/window analysis.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If the finite prime-weight mass is bounded by `massGrowth n`, and
`massGrowth n * windowError n → 0`, then the actual finite mass/window product
also tends to zero.
-/
theorem weightC_window_product_tendsto_zero_of_massGrowth
    (X : DFiniteStagePackageFromOperatorLayer)
    (alpha : ℕ → DFiniteStage)
    (windowError : ℕ → ℝ)
    (massGrowth : ℕ → ℝ)
    (h_massGrowth_nonneg :
      ∀ n : ℕ, 0 ≤ massGrowth n)
    (h_weightC_mass_le_growth :
      ∀ n : ℕ,
        (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
          (fun q : PrimePowerPair => ‖q.weightC‖) ≤
            massGrowth n)
    (h_windowError_nonneg :
      ∀ n : ℕ, 0 ≤ windowError n)
    (h_massGrowth_window_tendsto_zero :
      Tendsto
        (fun n : ℕ => massGrowth n * windowError n)
        Filter.atTop
        (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        ((X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
          (fun q : PrimePowerPair => ‖q.weightC‖)) *
            windowError n)
      Filter.atTop
      (𝓝 0) := by
  exact
    real_tendsto_zero_of_nonneg_bound
      (u := fun n : ℕ =>
        ((X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
          (fun q : PrimePowerPair => ‖q.weightC‖)) *
            windowError n)
      (b := fun n : ℕ => massGrowth n * windowError n)
      (by
        intro n
        exact
          mul_nonneg
            (Finset.sum_nonneg
              (fun q hq => norm_nonneg q.weightC))
            (h_windowError_nonneg n))
      (by
        intro n
        exact
          mul_le_mul_of_nonneg_right
            (h_weightC_mass_le_growth n)
            (h_windowError_nonneg n))
      (by
        intro n
        exact
          mul_nonneg
            (h_massGrowth_nonneg n)
            (h_windowError_nonneg n))
      h_massGrowth_window_tendsto_zero

/--
Mass-growth/window-rate data for the canonical prime-power package.

Compared with `CanonicalPrimePowerProductWindowErrorData`, this removes the
direct product-decay field

  `h_weightC_window_product_tendsto_zero`

and replaces it with:

* an explicit mass-growth function;
* a finite prime-weight mass bound;
* a rate condition saying mass growth times window error tends to zero.
-/
structure CanonicalPrimePowerMassGrowthWindowData
    (X : DFiniteStagePackageFromOperatorLayer) where
  alpha : ℕ → DFiniteStage

  /-- The common limiting kernel for the shared canonical prime-power series. -/
  Kshared : CanonicalKernelC

  /--
  Concrete finite-stage exhaustion: every prime-power index eventually appears
  in the finite stage index sets.
  -/
  h_indices_eventually_contains :
    ∀ q : PrimePowerPair,
      ∃ N : ℕ,
        ∀ n : ℕ,
          N ≤ n →
            q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

  /-- Unweighted majorant for the shared kernel. -/
  kernelMajorant : PrimePowerPair → ℝ

  /-- Nonnegativity of the unweighted kernel majorant. -/
  h_kernelMajorant_nonneg :
    ∀ q : PrimePowerPair, 0 ≤ kernelMajorant q

  /--
  Pointwise unweighted shared-kernel bound on the D overlap half-plane.
  -/
  h_sharedKernel_norm_le_majorant :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ q : PrimePowerPair,
        ‖Kshared q.center s‖ ≤ kernelMajorant q

  /--
  Summability of the weighted shared-kernel majorant.
  -/
  h_weightedKernelMajorant_summable :
    Summable
      (fun q : PrimePowerPair =>
        ‖q.weightC‖ * kernelMajorant q)

  /--
  Scalar window error.
  -/
  windowError : ℂ → ℕ → ℝ

  /-- Nonnegativity of the window error. -/
  h_windowError_nonneg :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 ≤ windowError s n

  /--
  Mass growth controlling the finite prime-weight mass.
  -/
  massGrowth : ℕ → ℝ

  /-- Nonnegativity of the mass-growth bound. -/
  h_massGrowth_nonneg :
    ∀ n : ℕ, 0 ≤ massGrowth n

  /--
  Finite prime-weight mass bound.
  -/
  h_weightC_mass_le_growth :
    ∀ n : ℕ,
      (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
        (fun q : PrimePowerPair => ‖q.weightC‖) ≤
          massGrowth n

  /--
  Rate condition: the mass-growth bound times the window error tends to zero.
  -/
  h_massGrowth_window_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ => massGrowth n * windowError s n)
        Filter.atTop
        (𝓝 0)

  /--
  Unweighted D.CANONICAL-WINDOW estimate on active finite-stage indices.
  -/
  h_kernel_window_error_le :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
          ‖X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n) q.center s -
              Kshared q.center s‖ ≤
            windowError s n

/--
Convert mass-growth/window-rate data into product-window data.
-/
def CanonicalPrimePowerMassGrowthWindowData.toProductWindowErrorData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerMassGrowthWindowData X) :
    CanonicalPrimePowerProductWindowErrorData X :=
  { alpha := S.alpha
    Kshared := S.Kshared
    h_indices_eventually_contains := S.h_indices_eventually_contains

    kernelMajorant := S.kernelMajorant
    h_kernelMajorant_nonneg := S.h_kernelMajorant_nonneg
    h_sharedKernel_norm_le_majorant := S.h_sharedKernel_norm_le_majorant
    h_weightedKernelMajorant_summable := S.h_weightedKernelMajorant_summable

    windowError := S.windowError
    h_windowError_nonneg := S.h_windowError_nonneg

    h_weightC_window_product_tendsto_zero := by
      intro s hs
      exact
        weightC_window_product_tendsto_zero_of_massGrowth
          X
          S.alpha
          (S.windowError s)
          S.massGrowth
          S.h_massGrowth_nonneg
          S.h_weightC_mass_le_growth
          (S.h_windowError_nonneg s hs)
          (S.h_massGrowth_window_tendsto_zero s hs)

    h_kernel_window_error_le := S.h_kernel_window_error_le }

/--
Build `CanonicalPrimePowerExhaustionData` from mass-growth/window-rate data.
-/
def CanonicalPrimePowerMassGrowthWindowData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerMassGrowthWindowData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toProductWindowErrorData.toExhaustionData

/--
Build `DBcanLimitData` directly from mass-growth/window-rate data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerMassGrowthWindow
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerMassGrowthWindowData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerProductWindowError
    X
    S.toProductWindowErrorData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once mass-growth/window-rate data is supplied.
-/
theorem canonicalPrimePowerMassGrowthWindow_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerMassGrowthWindowData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerMassGrowthWindow X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerProductWindowError_h_Bcan_matches_tsum
      X
      S.toProductWindowErrorData
      s
      hs

end

end RHFormalization
