import RHFormalization.CanonicalPrimePowerActualKernelError

/-!
# RHFormalization.CanonicalPrimePowerWindowMassError

Window-uniform mass bound for the canonical prime-power actual kernel error.

This is not an RH endpoint.

The previous layer reduced the D/H finite-to-limit passage to the actual finite
weighted kernel-error sum

  ∑ q in indices(alpha n),
    ‖q.weightC * Kstage_n q.center s
      - q.weightC * Kshared q.center s‖ → 0.

This file reduces that convergence to the D.CANONICAL-WINDOW-shaped estimate:

  actual weighted error at q
    ≤ weightMass q * windowError s n,

with

  ∑ q in indices(alpha n), weightMass q ≤ weightMassBound

and

  windowError s n → 0.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
A real-valued sequence tends to zero if it is nonnegative and bounded above by a
nonnegative real sequence tending to zero.
-/
theorem real_tendsto_zero_of_nonneg_bound
    {u : ℕ → ℝ}
    {b : ℕ → ℝ}
    (hu_nonneg : ∀ n : ℕ, 0 ≤ u n)
    (h_bound : ∀ n : ℕ, u n ≤ b n)
    (hb_nonneg : ∀ n : ℕ, 0 ≤ b n)
    (hb_zero : Tendsto b Filter.atTop (𝓝 0)) :
    Tendsto u Filter.atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε

  have hb_eventually :
      ∀ᶠ n in Filter.atTop, b n < ε := by
    have hdist :=
      (Metric.tendsto_nhds.mp hb_zero) ε hε
    filter_upwards [hdist] with n hn

    have hdist_eq : dist (b n) 0 = b n := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hb_nonneg n)]

    simpa [hdist_eq] using hn

  filter_upwards [hb_eventually] with n hn

  have hdist_u : dist (u n) 0 = u n := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu_nonneg n)]

  have hu_lt : u n < ε :=
    lt_of_le_of_lt (h_bound n) hn

  simpa [hdist_u] using hu_lt

/--
If the actual weighted kernel error is bounded pointwise by
`weightMass q * windowError n`, the finite weight mass is uniformly bounded, and
`windowError n → 0`, then the finite weighted kernel-error sum tends to zero.
-/
theorem actual_kernel_error_sum_tendsto_zero_of_window_mass_bound
    (X : DFiniteStagePackageFromOperatorLayer)
    (alpha : ℕ → DFiniteStage)
    (Kshared : CanonicalKernelC)
    (s : ℂ)
    (weightMass : PrimePowerPair → ℝ)
    (weightMassBound : ℝ)
    (windowError : ℕ → ℝ)
    (h_weightMass_nonneg :
      ∀ q : PrimePowerPair, 0 ≤ weightMass q)
    (h_weightMassBound_nonneg :
      0 ≤ weightMassBound)
    (h_weightMass_sum_le_bound :
      ∀ n : ℕ,
        (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
          (fun q : PrimePowerPair => weightMass q) ≤
            weightMassBound)
    (h_windowError_nonneg :
      ∀ n : ℕ, 0 ≤ windowError n)
    (h_windowError_tendsto_zero :
      Tendsto windowError Filter.atTop (𝓝 0))
    (h_actualTermError_le_window :
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
          canonicalPrimePowerActualTermError
              X
              alpha
              Kshared
              s
              n
              q ≤
            weightMass q * windowError n) :
    Tendsto
      (fun n : ℕ =>
        (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
          (fun q : PrimePowerPair =>
            canonicalPrimePowerActualTermError
              X
              alpha
              Kshared
              s
              n
              q))
      Filter.atTop
      (𝓝 0) := by
  let u : ℕ → ℝ :=
    fun n : ℕ =>
      (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
        (fun q : PrimePowerPair =>
          canonicalPrimePowerActualTermError
            X
            alpha
            Kshared
            s
            n
            q)

  let b : ℕ → ℝ :=
    fun n : ℕ => weightMassBound * windowError n

  have hu_nonneg : ∀ n : ℕ, 0 ≤ u n := by
    intro n
    dsimp [u]
    exact
      Finset.sum_nonneg
        (fun q hq =>
          norm_nonneg _)

  have h_bound : ∀ n : ℕ, u n ≤ b n := by
    intro n
    dsimp [u, b]

    let I : Finset PrimePowerPair :=
      X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

    calc
      I.sum
          (fun q : PrimePowerPair =>
            canonicalPrimePowerActualTermError
              X
              alpha
              Kshared
              s
              n
              q)
          ≤
        I.sum
          (fun q : PrimePowerPair =>
            weightMass q * windowError n) := by
          exact
            Finset.sum_le_sum
              (fun q hq =>
                h_actualTermError_le_window n q hq)
      _ =
        (I.sum (fun q : PrimePowerPair => weightMass q)) *
          windowError n := by
          simpa using
            (Finset.sum_mul
              (s := I)
              (f := fun q : PrimePowerPair => weightMass q)
              (a := windowError n)).symm
      _ ≤
        weightMassBound * windowError n := by
          exact
            mul_le_mul_of_nonneg_right
              (h_weightMass_sum_le_bound n)
              (h_windowError_nonneg n)

  have hb_nonneg : ∀ n : ℕ, 0 ≤ b n := by
    intro n
    dsimp [b]
    exact mul_nonneg h_weightMassBound_nonneg (h_windowError_nonneg n)

  have hb_zero : Tendsto b Filter.atTop (𝓝 0) := by
    dsimp [b]

    have hconst :
        Tendsto
          (fun _ : ℕ => weightMassBound)
          Filter.atTop
          (𝓝 weightMassBound) :=
      tendsto_const_nhds

    have hmul :
        Tendsto
          (fun n : ℕ => weightMassBound * windowError n)
          Filter.atTop
          (𝓝 (weightMassBound * 0)) :=
      hconst.mul h_windowError_tendsto_zero

    simpa [mul_zero] using hmul

  exact
    real_tendsto_zero_of_nonneg_bound
      hu_nonneg
      h_bound
      hb_nonneg
      hb_zero

/--
Window/mass controlled data for the canonical prime-power actual kernel error.

Compared with `CanonicalPrimePowerActualKernelErrorData`, this removes the direct
field

  `h_actual_error_sum_tendsto_zero`

and replaces it by:

* a finite weight mass;
* a uniform finite-stage mass bound;
* a scalar window error tending to zero;
* a pointwise actual weighted-error bound by `weightMass q * windowError`.
-/
structure CanonicalPrimePowerWindowMassErrorData
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

  /-- Nonnegativity of the shared-series majorant. -/
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

  /-- Summability of the shared-series majorant. -/
  h_majorant_summable :
    Summable majorant

  /--
  Weight mass used to control the finite window-error sum.
  Typically this is comparable to `‖q.weightC‖`, possibly with an additional
  harmless local factor.
  -/
  weightMass : PrimePowerPair → ℝ

  /-- Nonnegativity of the finite weight mass. -/
  h_weightMass_nonneg :
    ∀ q : PrimePowerPair, 0 ≤ weightMass q

  /-- Uniform bound for finite-stage weight masses. -/
  weightMassBound : ℝ

  /-- Nonnegativity of the uniform mass bound. -/
  h_weightMassBound_nonneg :
    0 ≤ weightMassBound

  /--
  The finite-stage index-set mass is uniformly bounded.
  -/
  h_weightMass_sum_le_bound :
    ∀ n : ℕ,
      (X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)).sum
        (fun q : PrimePowerPair => weightMass q) ≤
          weightMassBound

  /--
  Scalar window error. It may depend on `s`, but it must tend to zero for each
  `s` in the overlap half-plane.
  -/
  windowError : ℂ → ℕ → ℝ

  /-- Nonnegativity of the window error. -/
  h_windowError_nonneg :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
        0 ≤ windowError s n

  /-- The scalar window error tends to zero on the D overlap half-plane. -/
  h_windowError_tendsto_zero :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      Tendsto
        (windowError s)
        Filter.atTop
        (𝓝 0)

  /--
  Pointwise actual weighted kernel-error bound by mass times window error.
  -/
  h_actualTermError_le_window :
    ∀ s : ℂ, s ∈ RightHalfPlane X.toStagePackage.sigma0 →
      ∀ n : ℕ,
      ∀ q : PrimePowerPair,
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
          canonicalPrimePowerActualTermError
              X
              alpha
              Kshared
              s
              n
              q ≤
            weightMass q * windowError s n

/--
Convert window/mass controlled data into the previous actual-kernel-error data.

This discharges the actual finite weighted error sum convergence using the
window-error/mass-bound estimate.
-/
def CanonicalPrimePowerWindowMassErrorData.toActualKernelErrorData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerWindowMassErrorData X) :
    CanonicalPrimePowerActualKernelErrorData X :=
  { alpha := S.alpha
    Kshared := S.Kshared
    h_indices_eventually_contains := S.h_indices_eventually_contains
    majorant := S.majorant
    h_majorant_nonneg := S.h_majorant_nonneg
    h_term_norm_le_majorant := S.h_term_norm_le_majorant
    h_majorant_summable := S.h_majorant_summable
    h_actual_error_sum_tendsto_zero := by
      intro s hs
      exact
        actual_kernel_error_sum_tendsto_zero_of_window_mass_bound
          X
          S.alpha
          S.Kshared
          s
          S.weightMass
          S.weightMassBound
          (S.windowError s)
          S.h_weightMass_nonneg
          S.h_weightMassBound_nonneg
          S.h_weightMass_sum_le_bound
          (S.h_windowError_nonneg s hs)
          (S.h_windowError_tendsto_zero s hs)
          (S.h_actualTermError_le_window s hs) }

/--
Build `CanonicalPrimePowerExhaustionData` from window/mass error data.
-/
def CanonicalPrimePowerWindowMassErrorData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerWindowMassErrorData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toActualKernelErrorData.toExhaustionData

/--
Build `DBcanLimitData` directly from window/mass error data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerWindowMassError
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerWindowMassErrorData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerActualKernelError
    X
    S.toActualKernelErrorData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once window/mass error data is supplied.
-/
theorem canonicalPrimePowerWindowMassError_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerWindowMassErrorData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerWindowMassError X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerActualKernelError_h_Bcan_matches_tsum
      X
      S.toActualKernelErrorData
      s
      hs

end

end RHFormalization
