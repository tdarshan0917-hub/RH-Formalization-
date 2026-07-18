import RHFormalization.CanonicalPrimePowerExhaustion

/-!
# RHFormalization.CanonicalPrimePowerSeries

Series/exhaustion realization of the shared canonical prime-power package.

This is not an RH endpoint.

The previous layer reduced Appendix D to the convergence of finite canonical
prime-power packages. This file reduces that convergence to a standard
`HasSum` statement plus a finite-set exhaustion.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
If a series has sum `a`, then its finite partial sums over any `Finset`
exhaustion tend to `a`.

This is the abstract summability lemma needed for the canonical prime-power
finite-to-limit passage.
-/
theorem finite_sum_tendsto_of_hasSum_finset_exhaustion
    {ι : Type*}
    {f : ι → ℂ}
    {a : ℂ}
    (I : ℕ → Finset ι)
    (hI : Tendsto I Filter.atTop (Filter.atTop : Filter (Finset ι)))
    (h : HasSum f a) :
    Tendsto
      (fun n : ℕ => (I n).sum f)
      Filter.atTop
      (𝓝 a) := by
  change Tendsto (fun S : Finset ι => S.sum f) Filter.atTop (𝓝 a) at h
  exact h.comp hI

/--
Series/exhaustion data realizing the shared canonical prime-power package along
the finite operator stages.

This is the precise analytic data needed after the finite spike-sum formula:

* `alpha` chooses the finite cutoff stages;
* the finite stage index sets exhaust the prime-power index type;
* each finite canonical package is identified with a partial sum of `term`;
* the infinite series of `term` has sum `C.Bshared`.
-/
structure CanonicalPrimePowerSeriesData
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage) where
  alpha : ℕ → DFiniteStage

  /--
  The shared package is legal on the D-side overlap half-plane.
  -/
  h_Cshared_sigma_le :
    C.sigma0 ≤ X.toStagePackage.sigma0

  /--
  Infinite prime-power term represented by the shared canonical package.
  -/
  term : PrimePowerPair → ℂ → ℂ

  /--
  The finite prime-power index sets from the operator formula exhaust the full
  prime-power index type.
  -/
  h_indices_tendsto_top :
    Tendsto
      (fun n : ℕ =>
        X.toFiniteCanonicalPrimePowerFormula.indices (alpha n))
      Filter.atTop
      (Filter.atTop : Filter (Finset PrimePowerPair))

  /--
  The finite canonical package is the corresponding finite partial sum of
  `term`.
  -/
  h_finite_eq_partial :
    ∀ n : ℕ,
    ∀ s : ℂ,
      finiteCanonicalPrimePowerPackage
          (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n))
          (X.toFiniteCanonicalPrimePowerFormula.kernel (alpha n))
          s =
        (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
          (fun q : PrimePowerPair => term q s)

  /--
  The infinite prime-power series has sum `C.Bshared` on the D overlap
  half-plane.
  -/
  h_hasSum :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      HasSum
        (fun q : PrimePowerPair => term q s)
        (C.Bshared s)

/--
Convert series/exhaustion data into the canonical prime-power exhaustion data
already consumed by Appendix D.
-/
def CanonicalPrimePowerSeriesData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    {C : CanonicalPrimePowerPackage}
    (S : CanonicalPrimePowerSeriesData X C) :
    CanonicalPrimePowerExhaustionData X C :=
  { alpha := S.alpha
    h_Cshared_sigma_le := S.h_Cshared_sigma_le
    h_tendsto := by
      intro s hs

      have hpartial :
          Tendsto
            (fun n : ℕ =>
              (X.toFiniteCanonicalPrimePowerFormula.indices (S.alpha n)).sum
                (fun q : PrimePowerPair => S.term q s))
            Filter.atTop
            (𝓝 (C.Bshared s)) :=
        finite_sum_tendsto_of_hasSum_finset_exhaustion
          (fun n : ℕ =>
            X.toFiniteCanonicalPrimePowerFormula.indices (S.alpha n))
          S.h_indices_tendsto_top
          (S.h_hasSum s hs)

      have hseq :
          (fun n : ℕ =>
            finiteCanonicalPrimePowerPackage
              (X.toFiniteCanonicalPrimePowerFormula.indices (S.alpha n))
              (X.toFiniteCanonicalPrimePowerFormula.kernel (S.alpha n))
              s)
            =
          (fun n : ℕ =>
            (X.toFiniteCanonicalPrimePowerFormula.indices (S.alpha n)).sum
              (fun q : PrimePowerPair => S.term q s)) := by
        funext n
        exact S.h_finite_eq_partial n s

      simpa [hseq] using hpartial }

/--
Build `DBcanLimitData` directly from the series/exhaustion realization.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerSeries
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (S : CanonicalPrimePowerSeriesData X C) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerExhaustion
    X
    C
    S.toExhaustionData

/--
The D-side canonical package matches the shared canonical package once the
series/exhaustion realization is supplied.
-/
theorem canonicalPrimePowerSeries_h_Bcan_matches_shared
    (X : DFiniteStagePackageFromOperatorLayer)
    (C : CanonicalPrimePowerPackage)
    (S : CanonicalPrimePowerSeriesData X C)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerSeries X C S).Bcan s =
      C.Bshared s := by
  exact
    (buildDBcanLimitDataFromCanonicalPrimePowerSeries X C S).h_Bcan_matches_shared
      s
      hs

end

end RHFormalization
