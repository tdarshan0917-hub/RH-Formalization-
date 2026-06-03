import RHFormalization.AppendixDPrimePowerLimitComparison
import RHFormalization.DFHLimitConcrete
import RHFormalization.DMasterResidualConcrete
import RHFormalization.DOperatorExport

/-!
# RHFormalization.DOverlapFromStageSplitLimits

Generic Appendix-D overlap builder from the finite-stage split and pointwise
limits of the F, B, and R stage packages.

This file does not construct the selected D package by itself. It supplies the
generic lemma needed to build the `overlapBuilder` input for selected D routes.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
Build the D-side overlap identity from the finite-stage split and pointwise
convergence of the three stage terms along the same alpha sequence.

Finite-stage identity:
`F_stage = B_stage + R_stage`.

Limit identity:
`FH = Bcan + RH`.
-/
theorem DOverlapIdentityAPI_from_pointwise_stage_limits
    {P : DFiniteStagePackage}
    {B : DBcanLimitData P}
    {F : DFHLimitData P}
    {R : DMasterResidualData P}
    (stageSplit : DFiniteStageSplitAPI P)
    (hF :
      ∀ s ∈ RightHalfPlane P.sigma0,
        Filter.Tendsto
          (fun n : ℕ => P.F_stage (F.alpha n) s)
          Filter.atTop
          (nhds (F.FH s)))
    (hB :
      ∀ s ∈ RightHalfPlane P.sigma0,
        Filter.Tendsto
          (fun n : ℕ => P.B_stage (F.alpha n) s)
          Filter.atTop
          (nhds (B.Bcan s)))
    (hR :
      ∀ s ∈ RightHalfPlane P.sigma0,
        Filter.Tendsto
          (fun n : ℕ => P.R_stage (F.alpha n) s)
          Filter.atTop
          (nhds (R.RH s))) :
    DOverlapIdentityAPI P B F R := by
  refine ⟨?_⟩
  intro s hs

  have hFlim :
      Filter.Tendsto
        (fun n : ℕ => P.F_stage (F.alpha n) s)
        Filter.atTop
        (nhds (F.FH s)) :=
    hF s hs

  have hBRlim :
      Filter.Tendsto
        (fun n : ℕ => P.B_stage (F.alpha n) s + P.R_stage (F.alpha n) s)
        Filter.atTop
        (nhds (B.Bcan s + R.RH s)) := by
    exact (hB s hs).add (hR s hs)

  have hFeqBR :
      (fun n : ℕ => P.F_stage (F.alpha n) s) =
      (fun n : ℕ => P.B_stage (F.alpha n) s + P.R_stage (F.alpha n) s) := by
    funext n
    exact stageSplit.h_stage_split (F.alpha n) s hs

  have hBR_to_FH :
      Filter.Tendsto
        (fun n : ℕ => P.B_stage (F.alpha n) s + P.R_stage (F.alpha n) s)
        Filter.atTop
        (nhds (F.FH s)) := by
    simpa [hFeqBR] using hFlim

  exact tendsto_nhds_unique hBR_to_FH hBRlim

end

end RHFormalization
