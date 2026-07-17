import RHFormalization.CanonicalPrimePowerSharpCutoffMassEnvelope
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLength

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope

Chosen-length sharp-cutoff mass-envelope package.

This is the field-removing version.

The previous theorem proved the chosen-length rate, but still took the full
`CanonicalPrimePowerSharpCutoffMassEnvelopeData`, which already contained the
target field.

This file removes that circularity: the new data structure does not ask for

  h_massEnvelope_div_windowSpeed_tendsto_zero.

Instead it asks for the concrete chosen-length equation

  L_n = (massEnvelope(R_n) + 1) * (n + 1),

and then proves the mass/window-speed quotient field.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The concrete chosen sharp-cutoff speed formula.
-/
theorem sharpCutoffConcreteChosenSpeed_speed_eq
    {G : ℝ → ℂ}
    {Lstage : DFiniteStage → ℝ}
    {alpha : ℕ → DFiniteStage}
    (S : DCanonicalWindowSharpCutoffConcreteChosenSpeedData G Lstage alpha)
    (A : Set ℝ)
    (n : ℕ) :
    S.toCompactSpeedAPI.speed A n =
      (2 * Lstage (alpha n)) /
        (S.Gbound A * S.compactRadius A + 1) := by
  rfl

/--
Sharp-cutoff mass-envelope data with chosen length.

Compared with `CanonicalPrimePowerSharpCutoffMassEnvelopeData`, this removes
`h_massEnvelope_div_windowSpeed_tendsto_zero` and replaces it by `hL_chosen`.
-/
structure CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
    (X : DFiniteStagePackageFromOperatorLayer) where

  G : ℝ → ℂ
  Lstage : DFiniteStage → ℝ
  alpha : ℕ → DFiniteStage

  sharpSpeed :
    DCanonicalWindowSharpCutoffConcreteChosenSpeedData G Lstage alpha

  Kshared : CanonicalKernelC

  h_R_ge_nat :
    ∀ n : ℕ, (n : ℝ) ≤ (alpha n).R

  h_indices_contains_of_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      IsPrimePowerPair q →
      q.center ≤ (alpha n).R →
        q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n)

  h_indices_subset_center_le_R :
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        q.center ≤ (alpha n).R

  kernelMajorant : PrimePowerPair → ℝ

  h_kernelMajorant_nonneg :
    ∀ q : PrimePowerPair, 0 ≤ kernelMajorant q

  kernelID :
    PrimePowerDWindowKernelIdentificationData
      X
      (sharpCutoffDCanonicalWindowData G Lstage)
      alpha
      Kshared

  coordSet : ℂ → Set ℝ

  h_coordSet_compact :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
      IsCompact (coordSet s)

  h_coord_mem :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ n : ℕ,
    ∀ q : PrimePowerPair,
      q ∈ X.toFiniteCanonicalPrimePowerFormula.indices (alpha n) →
        kernelID.coord s q ∈ coordSet s

  h_windowLimit_norm_le_majorant :
    ∀ s : ℂ,
    ∀ hs : s ∈ RightHalfPlane X.toStagePackage.sigma0,
    ∀ q : PrimePowerPair,
      ‖(sharpCutoffDCanonicalWindowData G Lstage).G_limit
          (kernelID.coord s q)‖ ≤ kernelMajorant q

  summabilityEnvelope : PrimePowerPair → ℝ

  h_weightedKernelMajorant_le_envelope :
    ∀ q : PrimePowerPair,
      ‖q.weightC‖ * kernelMajorant q ≤ summabilityEnvelope q

  h_summabilityEnvelope_summable :
    Summable summabilityEnvelope

  massEnum : PrimePowerWeightCutoffEnumerationData

  massEnvelopeData : PrimePowerMassEnvelopeData massEnum

  /--
  Chosen sharp-cutoff length.

  This is the replacement for the old raw field
  `h_massEnvelope_div_windowSpeed_tendsto_zero`.
  -/
  hL_chosen :
    ∀ n : ℕ,
      Lstage (alpha n) =
        (massEnvelopeData.massEnvelope ((alpha n).R) + 1) *
          ((n : ℝ) + 1)

/--
The chosen-length mass/window-speed quotient tends to zero.

This is the actual field-killer proof.
-/
theorem CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData.massEnvelope_div_windowSpeed_tendsto_zero
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData X) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane X.toStagePackage.sigma0 →
        Tendsto
          (fun n : ℕ =>
            S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
              S.sharpSpeed.toCompactSpeedAPI.speed (S.coordSet s) n)
          Filter.atTop
          (𝓝 0) := by
  intro s hs

  have h_mass_div_L :
      Tendsto
        (fun n : ℕ =>
          S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
            S.Lstage (S.alpha n))
        Filter.atTop
        (𝓝 0) := by
    -- Same estimate as the already-built chosen-length theorem,
    -- but now proved from the new structure that does not contain
    -- the target mass/speed field.
    have hbound :
        ∀ n : ℕ,
          S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
              S.Lstage (S.alpha n)
            ≤
          (1 : ℝ) / ((n : ℝ) + 1) := by
      intro n
      rw [S.hL_chosen n]
      exact
        mass_div_chosenLength_le_inv
          (S.massEnvelopeData.massEnvelope ((S.alpha n).R))
          ((n : ℝ) + 1)
          (S.massEnvelopeData.h_massEnvelope_nonneg ((S.alpha n).R))
          (by positivity)

    have hnonneg :
        ∀ n : ℕ,
          0 ≤
            S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
              S.Lstage (S.alpha n) := by
      intro n
      rw [S.hL_chosen n]
      have hm :
          0 ≤ S.massEnvelopeData.massEnvelope ((S.alpha n).R) :=
        S.massEnvelopeData.h_massEnvelope_nonneg ((S.alpha n).R)
      have hden_pos :
          0 <
            (S.massEnvelopeData.massEnvelope ((S.alpha n).R) + 1) *
              ((n : ℝ) + 1) := by
        have h1 :
            0 < S.massEnvelopeData.massEnvelope ((S.alpha n).R) + 1 := by
          nlinarith
        have hn : 0 < (n : ℝ) + 1 := by
          positivity
        exact mul_pos h1 hn
      exact div_nonneg hm (le_of_lt hden_pos)

    have h_to_atTop :
        Tendsto (fun n : ℕ => (n : ℝ) + 1)
          Filter.atTop
          Filter.atTop := by
      have hnat :
          Tendsto (fun n : ℕ => (n : ℝ))
            Filter.atTop
            Filter.atTop :=
        tendsto_natCast_atTop_atTop
      rw [tendsto_atTop]
      intro b
      have h_ev := (tendsto_atTop.1 hnat) (b - 1)
      filter_upwards [h_ev] with n hn
      nlinarith

    have hinv_tendsto :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          Filter.atTop
          (𝓝 0) := by
      simpa [one_div] using
        (tendsto_inv_atTop_zero.comp h_to_atTop)

    exact squeeze_zero hnonneg hbound hinv_tendsto

  let C : ℝ :=
    S.sharpSpeed.Gbound (S.coordSet s) *
      S.sharpSpeed.compactRadius (S.coordSet s) + 1

  have hC_pos : 0 < C := by
    have hA : IsCompact (S.coordSet s) :=
      S.h_coordSet_compact s hs
    have hG :
        0 ≤ S.sharpSpeed.Gbound (S.coordSet s) :=
      S.sharpSpeed.h_Gbound_nonneg (S.coordSet s) hA
    have hR :
        0 ≤ S.sharpSpeed.compactRadius (S.coordSet s) :=
      S.sharpSpeed.h_compactRadius_nonneg (S.coordSet s) hA
    have hGR :
        0 ≤ S.sharpSpeed.Gbound (S.coordSet s) *
          S.sharpSpeed.compactRadius (S.coordSet s) :=
      mul_nonneg hG hR
    dsimp [C]
    nlinarith

  have hC_ne : C ≠ 0 :=
    ne_of_gt hC_pos

  have hscaled :
      Tendsto
        (fun n : ℕ =>
          (C / 2) *
            (S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
              S.Lstage (S.alpha n)))
        Filter.atTop
        (𝓝 0) := by
    simpa using h_mass_div_L.const_mul (C / 2)

  refine hscaled.congr' ?_
  filter_upwards with n

  have hL_pos : 0 < S.Lstage (S.alpha n) :=
    S.sharpSpeed.hL_pos n

  have hL_ne : S.Lstage (S.alpha n) ≠ 0 :=
    ne_of_gt hL_pos

  rw [sharpCutoffConcreteChosenSpeed_speed_eq S.sharpSpeed (S.coordSet s) n]

  dsimp [C]
  field_simp [hL_ne, hC_ne]

/--
Convert chosen-length data into the existing sharp-cutoff mass-envelope package.
This is where the old field is actually discharged.
-/
def CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData.toSharpCutoffMassEnvelopeData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData X) :
    CanonicalPrimePowerSharpCutoffMassEnvelopeData X :=
  { G := S.G
    Lstage := S.Lstage
    alpha := S.alpha
    sharpSpeed := S.sharpSpeed
    Kshared := S.Kshared
    h_R_ge_nat := S.h_R_ge_nat
    h_indices_contains_of_center_le_R :=
      S.h_indices_contains_of_center_le_R
    h_indices_subset_center_le_R :=
      S.h_indices_subset_center_le_R
    kernelMajorant := S.kernelMajorant
    h_kernelMajorant_nonneg := S.h_kernelMajorant_nonneg
    kernelID := S.kernelID
    coordSet := S.coordSet
    h_coordSet_compact := S.h_coordSet_compact
    h_coord_mem := S.h_coord_mem
    h_windowLimit_norm_le_majorant :=
      S.h_windowLimit_norm_le_majorant
    summabilityEnvelope := S.summabilityEnvelope
    h_weightedKernelMajorant_le_envelope :=
      S.h_weightedKernelMajorant_le_envelope
    h_summabilityEnvelope_summable :=
      S.h_summabilityEnvelope_summable
    massEnum := S.massEnum
    massEnvelopeData := S.massEnvelopeData
    h_massEnvelope_div_windowSpeed_tendsto_zero :=
      CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData.massEnvelope_div_windowSpeed_tendsto_zero S }

/--
Build `CanonicalPrimePowerExhaustionData` from chosen-length sharp-cutoff data.
-/
def CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData.toExhaustionData
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData X) :
    CanonicalPrimePowerExhaustionData
      X
      (canonicalPrimePowerPackageFromKernelTsum
        X.toStagePackage.sigma0
        S.Kshared) :=
  S.toSharpCutoffMassEnvelopeData.toExhaustionData

/--
Build `DBcanLimitData` from chosen-length sharp-cutoff data.
-/
def buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData X) :
    DBcanLimitData X.toStagePackage :=
  buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffMassEnvelope
    X
    S.toSharpCutoffMassEnvelopeData

/--
The D-side canonical package matches the concrete tsum-defined shared package
once chosen-length sharp-cutoff mass-envelope data is supplied.
-/
theorem canonicalPrimePowerSharpCutoffChosenLengthMassEnvelope_h_Bcan_matches_tsum
    (X : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData X)
    (s : ℂ)
    (hs : s ∈ RightHalfPlane X.toStagePackage.sigma0) :
    (buildDBcanLimitDataFromCanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope X S).Bcan s =
      ∑' q : PrimePowerPair,
        q.weightC * S.Kshared q.center s := by
  exact
    canonicalPrimePowerSharpCutoffMassEnvelope_h_Bcan_matches_tsum
      X
      S.toSharpCutoffMassEnvelopeData
      s
      hs

end

end RHFormalization
