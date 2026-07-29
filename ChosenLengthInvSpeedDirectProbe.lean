import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFR
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelope
import RHFormalization.CanonicalPrimePowerSharpCutoffMassEnvelopeExplicitRate
import RHFormalization.CanonicalPrimePowerSharpCutoffMassEnvelopeLinearRate

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

variable (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
variable (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)

/--
Scratch probe for the chosen-length inverse-speed target.

If this builds, promote it to
`RHFormalization/CanonicalPrimePowerSharpCutoffChosenLengthInvSpeed.lean`.
-/
theorem chosenLength_inv_speed_tendsto_zero_probe :
    ∀ (K : Set ℝ),
      IsCompact K →
        ∀ (ε : ℝ),
          0 < ε →
            ∀ᶠ (n : ℕ) in Filter.atTop,
              (1 : ℝ) / S.sharpSpeed.toCompactSpeedAPI.speed K n < ε := by
  intro K hK ε hε

  let C : ℝ :=
    S.sharpSpeed.Gbound K * S.sharpSpeed.compactRadius K + 1

  have hG_nonneg : 0 ≤ S.sharpSpeed.Gbound K :=
    S.sharpSpeed.h_Gbound_nonneg K hK

  have hR_nonneg : 0 ≤ S.sharpSpeed.compactRadius K :=
    S.sharpSpeed.h_compactRadius_nonneg K hK

  have hC_pos : 0 < C := by
    dsimp [C]
    have hmul :
        0 ≤ S.sharpSpeed.Gbound K * S.sharpSpeed.compactRadius K :=
      mul_nonneg hG_nonneg hR_nonneg
    nlinarith

  obtain ⟨N, hN⟩ := exists_nat_gt (C / (2 * ε))

  refine (Filter.eventually_ge_atTop N).mono ?_
  intro n hn

  have hn_real : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  have hmass_nonneg :
      0 ≤ S.massEnvelopeData.massEnvelope (S.alpha n).R :=
    S.massEnvelopeData.h_massEnvelope_nonneg (S.alpha n).R

  have hL_lower :
      ((n : ℝ) + 1) ≤ S.Lstage (S.alpha n) := by
    rw [S.hL_chosen n]
    have hfactor :
        (1 : ℝ) ≤ S.massEnvelopeData.massEnvelope (S.alpha n).R + 1 := by
      nlinarith
    have hn1_nonneg : 0 ≤ ((n : ℝ) + 1) := by
      positivity
    have hmul :=
      mul_le_mul_of_nonneg_right hfactor hn1_nonneg
    simpa [one_mul] using hmul

  have hL_pos : 0 < S.Lstage (S.alpha n) :=
    S.sharpSpeed.hL_pos n

  have hden_pos : 0 < 2 * ε := by
    positivity

  have hN' : C / (2 * ε) < (N : ℝ) := hN

  have hC_lt_N_right :
      C < (N : ℝ) * (2 * ε) := by
    exact (div_lt_iff₀ hden_pos).mp hN'

  have hC_lt_N :
      C < 2 * ε * (N : ℝ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hC_lt_N_right

  have hN_le_n1 : (N : ℝ) ≤ (n : ℝ) + 1 := by
    nlinarith [hn_real]

  have hC_bound :
      C < 2 * ε * ((n : ℝ) + 1) := by
    have hscale :
        (2 * ε) * (N : ℝ) ≤ (2 * ε) * ((n : ℝ) + 1) := by
      exact mul_le_mul_of_nonneg_left hN_le_n1 (by positivity)
    nlinarith [hC_lt_N, hscale]

  have hC_bound_L :
      C < 2 * ε * S.Lstage (S.alpha n) := by
    have hscale :
        2 * ε * ((n : ℝ) + 1) ≤ 2 * ε * S.Lstage (S.alpha n) := by
      exact mul_le_mul_of_nonneg_left hL_lower (by positivity)
    nlinarith [hC_bound, hscale]

  have hspeed_eq :
      S.sharpSpeed.toCompactSpeedAPI.speed K n =
        2 * S.Lstage (S.alpha n) / C := by
    simpa [C] using
      sharpCutoffConcreteChosenSpeed_speed_eq S.sharpSpeed K n

  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  have hL_ne : S.Lstage (S.alpha n) ≠ 0 := ne_of_gt hL_pos
  have h2L_pos : 0 < 2 * S.Lstage (S.alpha n) := by
    positivity

  rw [hspeed_eq]

  have hcalc :
      (1 : ℝ) / (2 * S.Lstage (S.alpha n) / C)
        =
      C / (2 * S.Lstage (S.alpha n)) := by
    field_simp [hC_ne, hL_ne]

  rw [hcalc]
  exact (div_lt_iff₀ h2L_pos).mpr (by
    nlinarith [hC_bound_L])

end

end RHFormalization
