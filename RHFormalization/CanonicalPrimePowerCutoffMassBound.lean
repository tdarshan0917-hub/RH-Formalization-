import RHFormalization.CanonicalPrimePowerRCutoffGrowth

/-!
# RHFormalization.CanonicalPrimePowerCutoffMassBound

Cutoff mass-bound version of the R-cutoff estimate package.

This file is not an RH endpoint.

It attacks the actual mass-growth estimate.  Instead of carrying

  `h_weightC_mass_le_growth`

as an abstract field, it derives it from a cutoff mass estimate:

  if every active prime-power index satisfies `q.center ≤ R`,
  then

    ∑ q in active, ‖q.weightC‖ ≤ massBound R.

This is the next concrete Appendix-D estimate shape.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
A finite cutoff mass bound for prime-power weights.

This is the theorem-shaped estimate replacing the abstract finite-stage mass
growth field.
-/
structure PrimePowerWeightMassBoundData where
  /--
  A real function bounding the total prime-power weight mass below cutoff `R`.
  -/
  massBound : ℝ → ℝ

  /-- Nonnegativity of the mass bound. -/
  h_massBound_nonneg :
    ∀ R : ℝ, 0 ≤ massBound R

  /--
  Cutoff mass estimate.

  If every index in `I` has center at most `R`, then the total weighted mass over
  `I` is bounded by `massBound R`.
  -/
  h_weightC_mass_le_of_center_le :
    ∀ I : Finset PrimePowerPair,
    ∀ R : ℝ,
      (∀ q : PrimePowerPair, q ∈ I → q.center ≤ R) →
        I.sum (fun q : PrimePowerPair => ‖q.weightC‖) ≤ massBound R

/--
R-cutoff growth/window data with a concrete cutoff mass-bound estimate.

Compared with `CanonicalPrimePowerRCutoffGrowthMassWindowData`, this removes the
abstract fields

  `massGrowth`,
  `h_massGrowth_nonneg`,
  `h_weightC_mass_le_growth`

and replaces them by:

* a cutoff mass-bound object;
* proof that the finite-stage indices lie below the stage cutoff;
* the rate condition using `massBound ((alpha n).R)`.
-/
structure CanonicalPrimePowerRCutoffMassBoundWindowData
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
      IsPrimePowerPair q →
      q.center ≤ (alpha n).R →
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

  /--
  The finite stage index set contains only indices below the stage cutoff.

  This is the converse inclusion needed for the mass estimate.
  -/
  h_indices_subset_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        q.center ≤ (alpha n).R

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
  Cutoff mass-bound estimate for the frozen prime-power weights.
  -/
  massData : PrimePowerWeightMassBoundData

  /--
  Rate condition using the cutoff mass bound:

    massBound(R_n) * windowError_n → 0.
  -/
  h_massBound_window_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          massData.massBound ((alpha n).R) * windowError s n)
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
Convert cutoff mass-bound data into the existing R-cutoff growth/mass/window
package.

This discharges the abstract finite mass-growth field using the cutoff mass
estimate.
-/
def CanonicalPrimePowerRCutoffMassBoundWindowData.toRCutoffGrowthMassWindowData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerRCutoffMassBoundWindowData X) :
    CanonicalPrimePowerRCutoffGrowthMassWindowData X :=
  { alpha := S.alpha
    Kshared := S.Kshared

    h_R_ge_nat := S.h_R_ge_nat
    h_indices_contains_of_center_le_R := S.h_indices_contains_of_center_le_R

    kernelMajorant := S.kernelMajorant
    h_kernelMajorant_nonneg := S.h_kernelMajorant_nonneg
    h_sharedKernel_norm_le_majorant := S.h_sharedKernel_norm_le_majorant
    h_weightedKernelMajorant_summable := S.h_weightedKernelMajorant_summable

    windowError := S.windowError
    h_windowError_nonneg := S.h_windowError_nonneg

    massGrowth := fun n : ℕ => S.massData.massBound ((S.alpha n).R)

    h_massGrowth_nonneg := by
      intro n
      exact S.massData.h_massBound_nonneg ((S.alpha n).R)

    h_weightC_mass_le_growth := by
      intro n
      exact
        S.massData.h_weightC_mass_le_of_center_le
          (X.toFiniteCanonicalPrimePowerFormula.indices (S.alpha n))
          ((S.alpha n).R)
          (fun q hq => S.h_indices_subset_center_le_R n q hq)

    h_massGrowth_window_tendsto_zero := by
      intro s hs
      exact S.h_massBound_window_tendsto_zero s hs

    h_kernel_window_error_le := S.h_kernel_window_error_le }

/--
Build `CanonicalPrimePowerExhaustionData` from cutoff mass-bound data.
-/
def CanonicalPrimePowerRCutoffMassBoundWindowData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerRCutoffMassBoundWindowData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toRCutoffGrowthMassWindowData.toExhaustionData

/--
Build `DBcanLimitData` directly from cutoff mass-bound data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerRCutoffMassBound
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffMassBoundWindowData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerRCutoffGrowth
    X
    S.toRCutoffGrowthMassWindowData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once cutoff mass-bound data is supplied.
-/
theorem canonicalPrimePowerRCutoffMassBound_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffMassBoundWindowData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerRCutoffMassBound X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerRCutoffGrowth_h_Bcan_matches_tsum
      X
      S.toRCutoffGrowthMassWindowData
      s
      hs

end

end RHFormalization
