import RHFormalization.CanonicalPrimePowerSharpCutoffMassEnvelope

/-!
# RHFormalization.CanonicalPrimePowerSharpCutoffMassEnvelopeExplicitRate

Explicit-rate form of the sharp-cutoff mass-envelope / window-speed estimate.

The current sharp-cutoff mainline has already inserted the concrete
D.CANONICAL-WINDOW speed:

  speed A n =
    (2 * Lstage (alpha n)) /
      (Gbound A * compactRadius A + 1).

This file isolates the real remaining analytic rate:

  massEnvelope(R_n)
    /
  ((2 L_n) / (Gbound(A_s) * radius(A_s) + 1)) → 0.

That is the next actual proof target.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The explicit sharp-cutoff speed formula along the chosen compact coordinate set.

This theorem is intentionally small: it exposes the exact denominator now used
by the concrete sharp-cutoff D-window speed.
-/
theorem sharpCutoffConcreteChosen_speed_coordSet_eq
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffMassEnvelopeData X)
    (s : ℂ)
    (n : ℕ) :
    S.sharpSpeed.toCompactSpeedAPI.speed (S.coordSet s) n =
      (2 * S.Lstage (S.alpha n)) /
        (S.sharpSpeed.Gbound (S.coordSet s) *
            S.sharpSpeed.compactRadius (S.coordSet s) + 1) := by
  rfl

/--
If the explicit sharp-cutoff mass/speed quotient tends to zero, then the
`h_massEnvelope_div_windowSpeed_tendsto_zero` field of the sharp-cutoff
mass-envelope package is discharged.

This is the real rate theorem we need to prove from the manuscript estimates.
-/
theorem sharpCutoffMassEnvelope_div_windowSpeed_tendsto_zero_of_explicit_rate
    {X : DFiniteStagePackageFromOperatorLayer}
    (S : CanonicalPrimePowerSharpCutoffMassEnvelopeData X)
    (h_explicit_rate :
      ∀ s : ℂ,
        s ∈ RightHalfPlane X.toStagePackage.sigma0 →
          Tendsto
            (fun n : ℕ =>
              S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
                ((2 * S.Lstage (S.alpha n)) /
                  (S.sharpSpeed.Gbound (S.coordSet s) *
                    S.sharpSpeed.compactRadius (S.coordSet s) + 1)))
            Filter.atTop
            (𝓝 0)) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane X.toStagePackage.sigma0 →
        Tendsto
          (fun n : ℕ =>
            S.massEnvelopeData.massEnvelope ((S.alpha n).R) /
              S.sharpSpeed.toCompactSpeedAPI.speed (S.coordSet s) n)
          Filter.atTop
          (𝓝 0) := by
  intro s hs
  simpa [sharpCutoffConcreteChosen_speed_coordSet_eq S s] using
    h_explicit_rate s hs

end

end RHFormalization
