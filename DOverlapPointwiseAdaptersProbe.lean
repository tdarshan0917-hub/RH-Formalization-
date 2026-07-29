import RHFormalization.DOverlapFromStageSplitLimits
import RHFormalization.DFHLimitConcrete
import RHFormalization.DMasterResidualConcrete
import RHFormalization.HalfPlaneGeometry

namespace RHFormalization

open Filter Topology
open scoped Topology

#check Metric.tendsto_nhds
#check isCompact_singleton
#check RightHalfPlane
#print RightHalfPlane
#check Omega
#print Omega

/--
Pointwise F-stage convergence from the compact-uniform F convergence field,
assuming the right half-plane is inside Ω.
-/
theorem DFHLimitData.pointwise_F_stage_tendsto_of_RHP_subset_Omega
    {P : DFiniteStagePackage}
    (F : DFHLimitData P)
    (hRHP : RightHalfPlane P.sigma0 ⊆ Ω) :
    ∀ s ∈ RightHalfPlane P.sigma0,
      Filter.Tendsto
        (fun n : ℕ => P.F_stage (F.alpha n) s)
        Filter.atTop
        (nhds (F.FH s)) := by
  intro s hs
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsingle : ({s} : Set ℂ) ⊆ Ω := by
    intro z hz
    have hz' : z = s := by simpa using hz
    subst z
    exact hRHP hs
  have h :=
    F.h_F_stage_to_FH ({s} : Set ℂ)
      isCompact_singleton
      hsingle
      ε
      hε
  filter_mono h with n hn
  exact hn s (by simp)

/--
Pointwise R-stage convergence from the compact-uniform residual convergence field,
assuming the right half-plane is inside Ω.
-/
theorem DMasterResidualData.pointwise_R_stage_tendsto_of_RHP_subset_Omega
    {P : DFiniteStagePackage}
    (R : DMasterResidualData P)
    (hRHP : RightHalfPlane P.sigma0 ⊆ Ω) :
    ∀ s ∈ RightHalfPlane P.sigma0,
      Filter.Tendsto
        (fun n : ℕ => P.R_stage (R.alpha n) s)
        Filter.atTop
        (nhds (R.RH s)) := by
  intro s hs
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsingle : ({s} : Set ℂ) ⊆ Ω := by
    intro z hz
    have hz' : z = s := by simpa using hz
    subst z
    exact hRHP hs
  have h :=
    R.h_R_stage_to_RH ({s} : Set ℂ)
      isCompact_singleton
      hsingle
      ε
      hε
  filter_mono h with n hn
  exact hn s (by simp)

end RHFormalization
