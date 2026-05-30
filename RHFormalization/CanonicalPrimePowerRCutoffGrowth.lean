import RHFormalization.FinalRHFromRCutoffEstimate

/-!
# RHFormalization.CanonicalPrimePowerRCutoffGrowth

Concrete growth version of the R-cutoff estimate package.

This file is not an RH endpoint.

It replaces the abstract field

  `Tendsto (fun n => (alpha n).R) atTop atTop`

by the concrete cutoff-growth estimate

  `(n : ℝ) ≤ (alpha n).R`.

This is a real discharge of one R-cutoff frontier obligation.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If a real sequence dominates the natural numbers, then it tends to `atTop`.

This is the elementary cutoff-growth lemma used to discharge
`h_R_tendsto_atTop`.
-/
theorem tendsto_atTop_of_nat_le_real
    (f : ℕ → ℝ)
    (hf : ∀ n : ℕ, (n : ℝ) ≤ f n) :
    Tendsto f Filter.atTop Filter.atTop := by
  rw [tendsto_atTop]
  intro b

  rcases exists_nat_ge b with ⟨N, hN⟩

  refine eventually_atTop.2 ⟨N, ?_⟩
  intro n hn

  have hNn : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  exact le_trans hN (le_trans hNn (hf n))

/--
Growth-version of the current R-cutoff / mass-growth / window-error package.

Compared with `CanonicalPrimePowerRCutoffMassGrowthWindowData`, this replaces
the abstract cutoff convergence field by the concrete lower bound

  `(n : ℝ) ≤ (alpha n).R`.
-/
structure CanonicalPrimePowerRCutoffGrowthMassWindowData
    (X : DFiniteStagePackageFromOperatorLayer) where
  alpha : ℕ → DFiniteStage

  /-- The common limiting kernel for the shared canonical prime-power series. -/
  Kshared : CanonicalKernelC

  /--
  Concrete cutoff growth: the prime-power cutoff dominates the stage index.
  -/
  h_R_ge_nat :
    ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R

  /--
  The finite stage index set contains every prime-power pair whose center lies
  below the stage cutoff.
  -/
  h_indices_contains_of_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q.center ≤ (alpha n).R →
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
Convert the concrete growth-version data into the existing R-cutoff estimate
package.
-/
def CanonicalPrimePowerRCutoffGrowthMassWindowData.toRCutoffMassGrowthWindowData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerRCutoffGrowthMassWindowData X) :
    CanonicalPrimePowerRCutoffMassGrowthWindowData X :=
  { alpha := S.alpha
    Kshared := S.Kshared

    h_R_tendsto_atTop :=
      tendsto_atTop_of_nat_le_real
        (fun n : ℕ => (S.alpha n).R)
        S.h_R_ge_nat

    h_indices_contains_of_center_le_R :=
      S.h_indices_contains_of_center_le_R

    kernelMajorant := S.kernelMajorant
    h_kernelMajorant_nonneg := S.h_kernelMajorant_nonneg
    h_sharedKernel_norm_le_majorant := S.h_sharedKernel_norm_le_majorant
    h_weightedKernelMajorant_summable := S.h_weightedKernelMajorant_summable

    windowError := S.windowError
    h_windowError_nonneg := S.h_windowError_nonneg

    massGrowth := S.massGrowth
    h_massGrowth_nonneg := S.h_massGrowth_nonneg
    h_weightC_mass_le_growth := S.h_weightC_mass_le_growth
    h_massGrowth_window_tendsto_zero := S.h_massGrowth_window_tendsto_zero

    h_kernel_window_error_le := S.h_kernel_window_error_le }

/--
Build `CanonicalPrimePowerExhaustionData` from the concrete growth-version
R-cutoff package.
-/
def CanonicalPrimePowerRCutoffGrowthMassWindowData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerRCutoffGrowthMassWindowData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toRCutoffMassGrowthWindowData.toExhaustionData

/--
Build `DBcanLimitData` directly from the concrete growth-version package.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerRCutoffGrowth
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffGrowthMassWindowData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerRCutoffMassGrowthWindow
    X
    S.toRCutoffMassGrowthWindowData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once concrete R-growth data is supplied.
-/
theorem canonicalPrimePowerRCutoffGrowth_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffGrowthMassWindowData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerRCutoffGrowth X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerRCutoffMassGrowthWindow_h_Bcan_matches_tsum
      X
      S.toRCutoffMassGrowthWindowData
      s
      hs

end

end RHFormalization
