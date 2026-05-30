import RHFormalization.CanonicalPrimePowerSharpCutoffMassEnvelopeExplicitRate

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffMassEnvelopeLinearRate

Collapse the explicit sharp-cutoff mass/speed rate to the real growth target:

  massEnvelope(R_n) / L_n → 0.

This is not another endpoint and not another broad wrapper.

The previous file reduced the abstract speed denominator to

  2 * L_n / (Gbound(A_s) * radius(A_s) + 1).

This file proves that it is enough to show

  massEnvelope(R_n) / L_n → 0,

because the compact factor

  (Gbound(A_s) * radius(A_s) + 1) / 2

is constant in `n`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The explicit sharp-cutoff quotient tends to zero if the mass envelope is
little-o of the sharp cutoff length `L_n`.
-/
theorem sharpCutoff_explicit_rate_of_massEnvelope_div_L_tendsto_zero
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffMassEnvelopeData X)
    (h_massEnvelope_div_L_tendsto_zero :
      ∀ s : ℂ,
        s ∈ RightHalfPlane X.toStagePackage.sigma0 →
          Tendsto
            (fun n : ℕ =>
              S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
                S.Lstage (S.alpha n))
            Filter.atTop
            (𝓝 0)) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane X.toStagePackage.sigma0 →
        Tendsto
          (fun n : ℕ =>
            S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
              ((2 * S.Lstage (S.alpha n)) /
                (S.sharpSpeed.Gbound (S.coordSet s) *
                  S.sharpSpeed.compactRadius (S.coordSet s) + 1)))
          Filter.atTop
          (𝓝 0) := by
  intro s hs

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

  have hbase :=
    h_massEnvelope_div_L_tendsto_zero s hs

  have hscaled :
      Tendsto
        (fun n : ℕ =>
          (C / 2) *
            (S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
              S.Lstage (S.alpha n)))
        Filter.atTop
        (𝓝 0) := by
    simpa using (hbase.const_mul (C / 2))

  refine hscaled.congr' ?_
  filter_upwards with n

  have hL_pos : 0 < S.Lstage (S.alpha n) :=
    S.sharpSpeed.hL_pos n

  have hL_ne : S.Lstage (S.alpha n) ≠ 0 :=
    ne_of_gt hL_pos

  dsimp [C]
  field_simp [hL_ne, hC_ne]

/--
Directly discharge the sharp-cutoff mass-envelope/window-speed field from the
growth estimate

  massEnvelope(R_n) / L_n → 0.
-/
theorem sharpCutoffMassEnvelope_div_windowSpeed_tendsto_zero_of_massEnvelope_div_L
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffMassEnvelopeData X)
    (h_massEnvelope_div_L_tendsto_zero :
      ∀ s : ℂ,
        s ∈ RightHalfPlane X.toStagePackage.sigma0 →
          Tendsto
            (fun n : ℕ =>
              S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
                S.Lstage (S.alpha n))
            Filter.atTop
            (𝓝 0)) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane X.toStagePackage.sigma0 →
        Tendsto
          (fun n : ℕ =>
            S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
              S.sharpSpeed.toCompactSpeedAPI.speed (S.coordSet s) n)
          Filter.atTop
          (𝓝 0) :=
  sharpCutoffMassEnvelope_div_windowSpeed_tendsto_zero_of_explicit_rate
    S
    (sharpCutoff_explicit_rate_of_massEnvelope_div_L_tendsto_zero
      S
      h_massEnvelope_div_L_tendsto_zero)

end

end RHFormalization
