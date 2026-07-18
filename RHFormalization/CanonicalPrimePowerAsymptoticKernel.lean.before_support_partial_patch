import RHFormalization.CanonicalPrimePowerSummabilityMajorant

/-!
# RHFormalization.CanonicalPrimePowerAsymptoticKernel

Asymptotic kernel-error realization of the canonical prime-power package.

This is not an RH endpoint.

The previous majorant layer still required exact finite-stage kernel agreement:

  `kernel (alpha n) q.center s = Kshared q.center s`

on finite index sets.

For Appendix D this is usually too strong: the canonical-window theorem gives a
finite-stage kernel whose finite weighted error tends to zero. This file replaces
exact kernel equality by the sharper analytic target:

  finiteCanonical(stage kernel)
    - finite partial sum(shared kernel)
      → 0.

This is the D.CANONICAL-WINDOW-shaped convergence input.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If the shared-kernel finite partial sums converge to the `tsum`, and the
finite-stage kernel error tends to zero, then the finite-stage canonical packages
converge to the same `tsum`.
-/
theorem finiteCanonical_tendsto_tsum_of_kernel_error_tendsto_zero
    (I : ℕ → Finset PrimePowerPair)
    (Kstage : ℕ → CanonicalKernelC)
    (Kshared : CanonicalKernelC)
    (s : ℂ)
    (hI : Tendsto I Filter.atTop (Filter.atTop : Filter (Finset PrimePowerPair)))
    (hsummable :
      Summable
        (fun q : PrimePowerPair => q.weightC * Kshared q.center s))
    (herror :
      Tendsto
        (fun n : ℕ =>
          finiteCanonicalPrimePowerPackage
              (I n)
              (Kstage n)
              s
            -
          (I n).sum
            (fun q : PrimePowerPair => q.weightC * Kshared q.center s))
        Filter.atTop
        (𝓝 0)) :
    Tendsto
      (fun n : ℕ =>
        finiteCanonicalPrimePowerPackage
          (I n)
          (Kstage n)
          s)
      Filter.atTop
      (𝓝
        (∑' q : PrimePowerPair,
          q.weightC * Kshared q.center s)) := by
  have hpartial :
      Tendsto
        (fun n : ℕ =>
          (I n).sum
            (fun q : PrimePowerPair => q.weightC * Kshared q.center s))
        Filter.atTop
        (𝓝
          (∑' q : PrimePowerPair,
            q.weightC * Kshared q.center s)) :=
    finite_sum_tendsto_of_hasSum_finset_exhaustion
      I
      hI
      hsummable.hasSum

  have hsum :=
    hpartial.add herror

  simpa [finiteCanonicalPrimePowerPackage, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm] using hsum

/--
Asymptotic-kernel majorant data for the concrete canonical prime-power package.

This replaces exact stage-kernel equality by the finite weighted kernel-error
limit.
-/
structure CanonicalPrimePowerAsymptoticKernelMajorantData
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
      IsPrimePowerPair q →
      ∃ N : ℕ,
        ∀ n : ℕ,
          N ≤ n →
            q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

  /-- Real nonnegative majorant for the shared prime-power kernel terms. -/
  majorant : PrimePowerPair → ℝ

  /-- Nonnegativity of the majorant. -/
  h_majorant_nonneg :
    ∀ q : PrimePowerPair, 0 ≤ majorant q

  /--
  Pointwise norm bound for the shared prime-power kernel term on the D overlap
  half-plane.
  -/
  h_term_norm_le_majorant :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ q : PrimePowerPair,
        ‖q.weightC * Kshared q.center s‖ ≤ majorant q

  /-- Summability of the real majorant. -/
  h_majorant_summable :
    Summable majorant

  /--
  The finite weighted shared-kernel partial sums converge to the shared package.

  This is the support-aware replacement for full raw `PrimePowerPair`
  exhaustion.
  -/
  h_weighted_partial_tendsto :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
            (fun q : PrimePowerPair => q.weightC * Kshared q.center s))
        Filter.atTop
        (𝓝 ((canonicalPrimePowerPackageFromKernelTsum
              X.toStagePackage.sigma0
              Kshared).Bshared s))

  /--
  D.CANONICAL-WINDOW-shaped finite weighted kernel error.

  This is the real replacement for exact finite-stage kernel equality.
  -/
  h_stage_kernel_error_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (fun n : ℕ =>
          finiteCanonicalPrimePowerPackage
              (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n))
              (X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n))
              s
            -
          (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
            (fun q : PrimePowerPair =>
              q.weightC * Kshared q.center s))
        Filter.atTop
        (𝓝 0)

/--
Convert asymptotic-kernel majorant data into canonical prime-power exhaustion
data.

This directly proves the finite-to-limit convergence needed by Appendix D.
-/
def CanonicalPrimePowerAsymptoticKernelMajorantData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerAsymptoticKernelMajorantData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  { alpha := S.alpha
    h_Cshared_sigma_le := le_rfl
    h_tendsto := by
      intro s hs

      have hpartial :=
        S.h_weighted_partial_tendsto s hs

      have herror :=
        S.h_stage_kernel_error_tendsto_zero s hs

      have hsum := hpartial.add herror

      simpa [canonicalPrimePowerPackageFromKernelTsum,
        finiteCanonicalPrimePowerPackage, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm] using hsum }

/--
Build `DBcanLimitData` directly from asymptotic-kernel majorant data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerAsymptoticKernel
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerAsymptoticKernelMajorantData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerExhaustion
    X
    (canonicalPrimePowerPackageFromKernelTsum
      X.toStagePackage.sigma0
      S.Kshared)
    S.toExhaustionData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once asymptotic kernel-error and majorant data are supplied.
-/
theorem canonicalPrimePowerAsymptoticKernel_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerAsymptoticKernelMajorantData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerAsymptoticKernel X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  simpa [canonicalPrimePowerPackageFromKernelTsum] using
    (buildDBcanLimitDataFromCanonicalPrimePowerAsymptoticKernel X S).h_Bcan_matches_shared
      s
      hs

end

end RHFormalization
