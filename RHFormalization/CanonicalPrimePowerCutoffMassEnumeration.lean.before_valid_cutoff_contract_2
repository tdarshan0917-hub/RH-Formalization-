import RHFormalization.CanonicalPrimePowerCutoffMassBound

/-!
# RHFormalization.CanonicalPrimePowerCutoffMassEnumeration

Concrete finite-enumeration version of the prime-power cutoff mass bound.

This file is not an RH endpoint.

The previous layer introduced an abstract cutoff mass estimate:

  `PrimePowerWeightMassBoundData`.

This file makes that estimate concrete by using a finite enumeration

  `belowCutoff R : Finset PrimePowerPair`

which contains every prime-power pair with `q.center ≤ R`.

Then the mass bound is definitionally

  `∑ q in belowCutoff R, ‖q.weightC‖`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Finite enumeration of all prime-power pairs below a real cutoff.

This is the concrete finite-combinatorial input behind the cutoff mass bound.
-/
structure PrimePowerWeightCutoffEnumerationData where
  /--
  Finite set enumerating all prime-power pairs below cutoff `R`.
  -/
  belowCutoff : ℝ → Finset PrimePowerPair

  /--
  Completeness of the finite enumeration.
  -/
  h_mem_belowCutoff :
    ∀ R : ℝ,
    ∀ q : PrimePowerPair,
      q.center ≤ R →
        q ∈ belowCutoff R

/--
Build the abstract cutoff mass-bound data from a concrete finite enumeration.

The mass bound is exactly the finite weighted mass of the enumerated cutoff set.
-/
def PrimePowerWeightCutoffEnumerationData.toMassBoundData
    (E : PrimePowerWeightCutoffEnumerationData) :
    PrimePowerWeightMassBoundData :=
  { massBound := fun R : ℝ =>
      (E.belowCutoff R).sum
        (fun q : PrimePowerPair => ‖q.weightC‖)

    h_massBound_nonneg := by
      intro R
      exact
        Finset.sum_nonneg
          (fun q hq => norm_nonneg q.weightC)

    h_weightC_mass_le_of_center_le := by
      intro I R hcenter

      exact
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun q hq =>
            E.h_mem_belowCutoff R q (hcenter q hq))
          (fun q hq hqnot =>
            norm_nonneg q.weightC) }

/--
R-cutoff/window data using a concrete finite cutoff enumeration.

Compared with `CanonicalPrimePowerRCutoffMassBoundWindowData`, this removes the
abstract `massData` field and replaces it with the concrete finite enumeration
`massEnum`.
-/
structure CanonicalPrimePowerRCutoffEnumeratedMassWindowData
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

  /--
  The finite stage index set contains only indices below the stage cutoff.
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
  Concrete finite enumeration of prime-power pairs below cutoff.
  -/
  massEnum : PrimePowerWeightCutoffEnumerationData

  /--
  Rate condition using the enumerated cutoff mass:

    `(∑ q in belowCutoff R_n, ‖q.weightC‖) * windowError_n → 0`.
  -/
  h_enumeratedMass_window_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          (massEnum.belowCutoff ((alpha n).R)).sum
            (fun q : PrimePowerPair => ‖q.weightC‖)
          * windowError s n)
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
Convert concrete cutoff-enumeration data into the cutoff mass-bound data.
-/
def CanonicalPrimePowerRCutoffEnumeratedMassWindowData.toRCutoffMassBoundWindowData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerRCutoffEnumeratedMassWindowData X) :
    CanonicalPrimePowerRCutoffMassBoundWindowData X :=
  { alpha := S.alpha
    Kshared := S.Kshared

    h_R_ge_nat := S.h_R_ge_nat
    h_indices_contains_of_center_le_R := S.h_indices_contains_of_center_le_R
    h_indices_subset_center_le_R := S.h_indices_subset_center_le_R

    kernelMajorant := S.kernelMajorant
    h_kernelMajorant_nonneg := S.h_kernelMajorant_nonneg
    h_sharedKernel_norm_le_majorant := S.h_sharedKernel_norm_le_majorant
    h_weightedKernelMajorant_summable := S.h_weightedKernelMajorant_summable

    windowError := S.windowError
    h_windowError_nonneg := S.h_windowError_nonneg

    massData := S.massEnum.toMassBoundData

    h_massBound_window_tendsto_zero := by
      intro s hs
      exact S.h_enumeratedMass_window_tendsto_zero s hs

    h_kernel_window_error_le := S.h_kernel_window_error_le }

/--
Build `CanonicalPrimePowerExhaustionData` from concrete cutoff-enumeration data.
-/
def CanonicalPrimePowerRCutoffEnumeratedMassWindowData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerRCutoffEnumeratedMassWindowData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toRCutoffMassBoundWindowData.toExhaustionData

/--
Build `DBcanLimitData` directly from concrete cutoff-enumeration data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerRCutoffEnumeration
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffEnumeratedMassWindowData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerRCutoffMassBound
    X
    S.toRCutoffMassBoundWindowData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once concrete cutoff-enumeration data is supplied.
-/
theorem canonicalPrimePowerRCutoffEnumeration_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerRCutoffEnumeratedMassWindowData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerRCutoffEnumeration X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerRCutoffMassBound_h_Bcan_matches_tsum
      X
      S.toRCutoffMassBoundWindowData
      s
      hs

end

end RHFormalization
