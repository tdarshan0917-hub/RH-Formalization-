import RHFormalization.CanonicalPrimePowerMassGrowthWindow

/-!
# RHFormalization.CanonicalPrimePowerRCutoffExhaustion

R-cutoff exhaustion for the canonical prime-power package.

This is not an RH endpoint.

The previous mass-growth/window layer still carried the abstract field

  `h_indices_eventually_contains`.

But each finite Appendix-D stage already has a prime-power cutoff parameter

  `α.R`.

This file replaces abstract eventual index inclusion by the concrete cutoff facts:

* `α n .R → ∞`;
* every prime-power pair with `q.center ≤ α n .R` belongs to the finite index set.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If the finite-stage cutoffs `α n .R` tend to infinity and the finite index set
contains every prime-power pair with center at most `α n .R`, then every fixed
prime-power pair eventually belongs to the finite index sets.
-/
theorem primePower_indices_eventually_contains_of_R_cutoff
    (X : DFiniteStagePackageFromOperatorLayer)
    (alpha : ℕ → DFiniteStage)
    (h_R_tendsto_atTop :
      Tendsto
        (fun n : ℕ => (alpha n).R)
        Filter.atTop
        Filter.atTop)
    (h_indices_contains_of_center_le_R :
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        IsPrimePowerPair q →
        q.center ≤ (alpha n).R →
          q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)) :
    ∀ q : PrimePowerPair,
      IsPrimePowerPair q →
      ∃ N : ℕ,
        ∀ n : ℕ,
          N ≤ n →
            q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) := by
  intro q hq

  have h_eventually_center_le_R :
      ∀ᶠ n in Filter.atTop, q.center ≤ (alpha n).R := by
    exact (tendsto_atTop.1 h_R_tendsto_atTop) q.center

  rcases eventually_atTop.1 h_eventually_center_le_R with ⟨N, hN⟩

  exact
    ⟨N, by
      intro n hn
      exact h_indices_contains_of_center_le_R n q hq (hN n hn)⟩

/--
R-cutoff version of the mass-growth/window data.

Compared with `CanonicalPrimePowerMassGrowthWindowData`, this removes the
abstract eventual index-inclusion field and replaces it by:

* `h_R_tendsto_atTop`;
* `h_indices_contains_of_center_le_R`.
-/
structure CanonicalPrimePowerRCutoffMassGrowthWindowData
    (X : DFiniteStagePackageFromOperatorLayer) where
  alpha : ℕ → DFiniteStage

  /-- The common limiting kernel for the shared canonical prime-power series. -/
  Kshared : CanonicalKernelC

  /--
  The prime-power cutoff tends to infinity.
  -/
  h_R_tendsto_atTop :
    Tendsto
      (fun n : ℕ => (alpha n).R)
      Filter.atTop
      Filter.atTop

  /--
  The finite stage index set contains every prime-power pair whose center lies
  below the stage cutoff.
  -/
  h_indices_contains_of_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      IsPrimePowerPair q →
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
Convert R-cutoff data into the previous mass-growth/window data.

This discharges `h_indices_eventually_contains` from the concrete cutoff
mechanism.
-/
def CanonicalPrimePowerRCutoffMassGrowthWindowData.toMassGrowthWindowData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerRCutoffMassGrowthWindowData X) :
    CanonicalPrimePowerMassGrowthWindowData X :=
  { alpha := S.alpha
    Kshared := S.Kshared

    h_indices_eventually_contains :=
      primePower_indices_eventually_contains_of_R_cutoff
        X
        S.alpha
        S.h_R_tendsto_atTop
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
Build `CanonicalPrimePowerExhaustionData` from R-cutoff mass-growth/window data.
-/
def CanonicalPrimePowerRCutoffMassGrowthWindowData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerRCutoffMassGrowthWindowData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toMassGrowthWindowData.toExhaustionData

/--
Build `DBcanLimitData` directly from R-cutoff mass-growth/window data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerRCutoffMassGrowthWindow
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffMassGrowthWindowData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerMassGrowthWindow
    X
    S.toMassGrowthWindowData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once R-cutoff mass-growth/window data is supplied.
-/
theorem canonicalPrimePowerRCutoffMassGrowthWindow_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffMassGrowthWindowData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerRCutoffMassGrowthWindow X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerMassGrowthWindow_h_Bcan_matches_tsum
      X
      S.toMassGrowthWindowData
      s
      hs

end

end RHFormalization
