import RHFormalization.HMeromorphicWithNormalFormChosenCshared

/-!
# HSplitTarget

This scratch file exposes the exact remaining H/E split theorem needed by

  finalRHSpine_from_HChosenDSharedC.

Do not add this file to root.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

variable
  (Y : DDetailedConstructionWithOperatorLegality)
  (M : ZeroMultiplicityData)
  (E : ZeroExhaustion)
  (Zpole : ℂ → ℂ)
  (convergence : ZeroPoleLocalUniformConvergenceAPI M E Zpole)
  (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M E Zpole)
  (HarchPackage : HArchPackage)
  (sigma0 : ℝ)
  (h_Cshared_sigma_le : Y.B.Cshared.sigma0 ≤ sigma0)

/--
This is the current real H/E frontier.

Proving this is what lets `finalRHSpine_from_HChosenDSharedC` consume the
chosen-D-shared H package.
-/
example :
    ∀ s : ℂ,
      s ∈ RightHalfPlane sigma0 →
        Y.B.Cshared.Bshared s =
          HarchPackage.Harch s - Zpole s := by
  intro s hs
  -- This is the exact explicit-formula split goal.
  -- Next proof must come from the manuscript's Harch/Zpole construction,
  -- not from another compatibility wrapper.
  fail_if_success rfl
  -- Leave this file as a target probe only.
  -- Replace this scratch example with a real theorem once the source theorem is identified.
  sorry

end

end RHFormalization
