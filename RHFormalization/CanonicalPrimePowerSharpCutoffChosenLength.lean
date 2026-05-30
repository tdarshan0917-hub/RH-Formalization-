import RHFormalization.CanonicalPrimePowerSharpCutoffMassEnvelopeLinearRate

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffChosenLength

Chosen sharp-cutoff length for the mass-envelope / speed quotient.

This is a real estimate step.

The previous file reduced the sharp-cutoff mass/window-speed quotient to

  massEnvelope(R_n) / L_n → 0.

This file proves that target from the concrete choice

  L_n = (massEnvelope(R_n) + 1) * (n + 1).

Thus the remaining quotient is bounded by `1 / (n + 1)`, which tends to zero.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Algebraic bound behind the chosen-length estimate.

If `0 ≤ m` and `N > 0`, then

  m / ((m + 1) * N) ≤ 1 / N.
-/
theorem mass_div_chosenLength_le_inv
    (m N : ℝ)
    (hm : 0 ≤ m)
    (hN : 0 < N) :
    m / ((m + 1) * N) ≤ (1 : ℝ) / N := by
  have hm1_pos : 0 < m + 1 := by
    nlinarith
  have hden_pos : 0 < (m + 1) * N :=
    mul_pos hm1_pos hN
  have hN_nonneg : 0 ≤ N := le_of_lt hN

  have hmul :
      m ≤ m + 1 := by
    nlinarith

  calc
    m / ((m + 1) * N)
        = (m / (m + 1)) * (1 / N) := by
            field_simp [ne_of_gt hm1_pos, ne_of_gt hN]
    _ ≤ 1 * (1 / N) := by
            have hfrac : m / (m + 1) ≤ 1 := by
              exact div_le_one_of_le₀ hmul (le_of_lt hm1_pos)
            have hinv_nonneg : 0 ≤ (1 : ℝ) / N :=
              div_nonneg zero_le_one hN_nonneg
            exact mul_le_mul_of_nonneg_right hfrac hinv_nonneg
    _ = (1 : ℝ) / N := by
            ring

/--
If the sharp cutoff length is chosen as

  Lstage (alpha n) =
    (massEnvelope(R_n) + 1) * (n + 1),

then the required mass-envelope/length quotient tends to zero.

This is the actual rate estimate needed by
`sharpCutoffMassEnvelope_div_windowSpeed_tendsto_zero_of_massEnvelope_div_L`.
-/
theorem sharpCutoff_massEnvelope_div_chosenLength_tendsto_zero
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffMassEnvelopeData X)
    (hL_chosen :
      ∀ n : ℕ,
        S.Lstage (S.alpha n) =
          (S.massEnvelopeData.massEnvelope ((S.alpha n).R) + 1) *
            ((n : ℝ) + 1)) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane X.toStagePackage.sigma0 →
        Tendsto
          (fun n : ℕ =>
            S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
              S.Lstage (S.alpha n))
          Filter.atTop
          (𝓝 0) := by
  intro s hs

  have hbound :
      ∀ n : ℕ,
        S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
            S.Lstage (S.alpha n)
          ≤
        (1 : ℝ) / ((n : ℝ) + 1) := by
    intro n
    rw [hL_chosen n]
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
    rw [hL_chosen n]
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

  exact
    squeeze_zero hnonneg hbound hinv_tendsto

/--
Directly discharge the concrete sharp-cutoff mass/window-speed quotient from the
chosen cutoff length.
-/
theorem sharpCutoffMassEnvelope_div_windowSpeed_tendsto_zero_of_chosenLength
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffMassEnvelopeData X)
    (hL_chosen :
      ∀ n : ℕ,
        S.Lstage (S.alpha n) =
          (S.massEnvelopeData.massEnvelope ((S.alpha n).R) + 1) *
            ((n : ℝ) + 1)) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane X.toStagePackage.sigma0 →
        Tendsto
          (fun n : ℕ =>
            S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
              S.sharpSpeed.toCompactSpeedAPI.speed (S.coordSet s) n)
          Filter.atTop
          (𝓝 0) :=
  sharpCutoffMassEnvelope_div_windowSpeed_tendsto_zero_of_massEnvelope_div_L
    S
    (sharpCutoff_massEnvelope_div_chosenLength_tendsto_zero
      S
      hL_chosen)

end

end RHFormalization
