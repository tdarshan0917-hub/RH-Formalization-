import RHFormalization.DBFFGate2WindowError
import RHFormalization.DBFFAdmissibleRStageOverlap
import RHFormalization.AdmissibleFreeTailAssembly
import RHFormalization.AdmissibleResidualUniform
import RHFormalization.DBFFBcorr
import RHFormalization.HalfPlaneGeometry
import Mathlib

set_option autoImplicit false

namespace RHFormalization

open Complex Filter
open scoped Topology BigOperators

/-- `RightHalfPlane 1 ⊆ Ω`, proved directly from the definitions. -/
theorem rightHalfPlane_one_subset_Omega : RightHalfPlane 1 ⊆ Ω := by
  intro s hs
  have hre : (1 : ℝ) < s.re := hs
  rw [mem_Omega_iff]
  rintro ⟨_him, hle⟩
  linarith

/-- Free-stage overlap limit, pointwise, from the compact ε-δ form at `{s}`. -/
theorem admissibleFreeStage_tendsto_pointwise (s : ℂ) (hsΩ : s ∈ Ω) :
    Tendsto (fun n => admissibleFreeStage n s) atTop (nhds (FHadmFree s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h :=
    admissibleFreeStage_to_FHadmFree ({s} : Set ℂ) isCompact_singleton
      (Set.singleton_subset_iff.mpr hsΩ) ε hε
  obtain ⟨N, hN⟩ := h.exists_forall_of_atTop
  exact ⟨N, fun n hn => hN n hn s (by simp)⟩

/-- Second-resolvent residual → 0 pointwise on Ω, from the `C/(n+2)` bound. -/
theorem secondResolventResidual_tendsto_zero_pointwise (s : ℂ) (hsΩ : s ∈ Ω) :
    Tendsto (fun n => SecondResolventResidual n s) atTop (nhds 0) := by
  obtain ⟨C, _hCpos, hbound⟩ :=
    SecondResolventResidual_uniform_bound ({s} : Set ℂ) isCompact_singleton
      (Set.singleton_subset_iff.mpr hsΩ)
  have hb : ∀ n, ‖SecondResolventResidual n s‖ ≤ C / ((n : ℝ) + 2) :=
    fun n => hbound n s (by simp)
  have hden : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => C / ((n : ℝ) + 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  exact squeeze_zero_norm hb hlim

/-- **Gate 2A — overlap convergence.** On the overlap half-plane the Gate-2
window error tends to `-Bshared` (NOT to 0). -/
theorem gate2WindowError_tendsto_neg_Bshared_on_overlap
    (s : ℂ) (hs : s ∈ RightHalfPlane 1) :
    Tendsto (fun n => gate2WindowError n s) atTop
      (nhds (-(shiftedLaplacePrimePackageAt 1).Bshared s)) := by
  have hsΩ : s ∈ Ω := rightHalfPlane_one_subset_Omega hs
  have hrw : (fun n => gate2WindowError n s)
      = (fun n =>
          (galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
            + Bcorr n s)
          - admissibleFreeStage n s
          - SecondResolventResidual n s) := by
    funext n
    linear_combination -correctedResidual_eq_free_add_gate2_add_second n hsΩ
  rw [hrw]
  have hR := admissible_R_stage_to_DBFF_overlap s hs
  have hB := Bcorr_overlap0 hs
  have hFree := admissibleFreeStage_tendsto_pointwise s hsΩ
  have hSecond := secondResolventResidual_tendsto_zero_pointwise s hsΩ
  have hfin := ((hR.add hB).sub hFree).sub hSecond
  have hval :
      (FHadmFree s - (shiftedLaplacePrimePackageAt 1).Bshared s) + 0
          - FHadmFree s - 0
        = -(shiftedLaplacePrimePackageAt 1).Bshared s := by ring
  rw [hval] at hfin
  exact hfin

#print axioms gate2WindowError_tendsto_neg_Bshared_on_overlap

end RHFormalization
