/-
GalerkinOverlapAndV9.lean

1. Finset bridge: activePrimePowerPairsCenterBelow R = concretePrimePowerBelowCutoff R.
2. hB along galerkinStageSeq: B_stage -> Bcan pointwise on Re s > 1.
3. V9 endpoint: RH from (F, R) on the genuine galerkin stage package.
-/
import RHFormalization.GalerkinBcanLimitData
import RHFormalization.HonestEndpointV8
import RHFormalization.ArithmeticShiftedLaplaceBStageConvergence
import RHFormalization.DOverlapFromStageSplitLimits
import RHFormalization.DOverlapPointwiseFromCompactUniform

namespace RHFormalization
noncomputable section
open Filter Topology Classical

attribute [local instance] Classical.propDecidable

/-- Cast helper: natValue below exp R bounds any factor below the ceiling. -/
private theorem nat_le_ceil_of_le_exp {a : ℕ} {R : ℝ}
    (h : (a : ℝ) ≤ Real.exp R) : a < ⌈Real.exp R⌉₊ + 1 := by
  have h2 : (a : ℝ) ≤ (⌈Real.exp R⌉₊ : ℝ) := le_trans h (Nat.le_ceil _)
  have h3 : a ≤ ⌈Real.exp R⌉₊ := by exact_mod_cast h2
  omega

/-- The two prime-power cutoff enumerations agree. -/
theorem activePairs_eq_concrete (R : ℝ) :
    activePrimePowerPairsCenterBelow R = concretePrimePowerBelowCutoff R := by
  classical
  ext q
  constructor
  · intro hq
    have hmem := (valid_primePower_center_le_finite R).mem_toFinset.mp hq
    obtain ⟨hvalid, hcenter⟩ := hmem
    have hpow_le : ((q.p ^ q.m : ℕ) : ℝ) ≤ Real.exp R := by
      have hpos : (0 : ℝ) < ((q.p ^ q.m : ℕ) : ℝ) := by
        have := hvalid.1.pos
        positivity
      have hlog : Real.log ((q.p ^ q.m : ℕ) : ℝ) ≤ R := by
        first
          | exact hcenter
          | simpa [PrimePowerPair.center, PrimePowerPair.natValue] using hcenter
      calc ((q.p ^ q.m : ℕ) : ℝ)
          = Real.exp (Real.log ((q.p ^ q.m : ℕ) : ℝ)) := (Real.exp_log hpos).symm
        _ ≤ Real.exp R := Real.exp_le_exp.mpr hlog
    rw [concretePrimePowerBelowCutoff, Finset.mem_filter]
    refine ⟨?_, hvalid, hcenter⟩
    rw [Finset.mem_product]
    have hm_pos : 0 < q.m := hvalid.2
    constructor
    · rw [Finset.mem_range]
      apply nat_le_ceil_of_le_exp
      have h1 : q.p ≤ q.p ^ q.m := Nat.le_self_pow hm_pos.ne' q.p
      calc (q.p : ℝ) ≤ ((q.p ^ q.m : ℕ) : ℝ) := by exact_mod_cast h1
        _ ≤ Real.exp R := hpow_le
    · rw [Finset.mem_range]
      apply nat_le_ceil_of_le_exp
      have h2 : q.m < 2 ^ q.m := Nat.lt_two_pow_self
      have h3 : (2:ℕ) ^ q.m ≤ q.p ^ q.m :=
        Nat.pow_le_pow_left hvalid.1.two_le q.m
      have h1 : q.m ≤ q.p ^ q.m := le_of_lt (lt_of_lt_of_le h2 h3)
      calc (q.m : ℝ) ≤ ((q.p ^ q.m : ℕ) : ℝ) := by exact_mod_cast h1
        _ ≤ Real.exp R := hpow_le
  · intro hq
    rw [concretePrimePowerBelowCutoff, Finset.mem_filter] at hq
    exact (valid_primePower_center_le_finite R).mem_toFinset.mpr hq.2

/-- hB: along the genuine exhaustion, B_stage tends to Bcan on Re s > 1. -/
theorem galerkin_hB
    (s : ℂ) (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto (fun n : ℕ => galerkinStagePackage.B_stage (galerkinStageSeq n) s)
      atTop (𝓝 (galerkinBcanLimitData.Bcan s)) := by
  have hconv := shiftedLaplaceConcreteFiniteCanonical_tendsto_Bshared_sigma1 s hs
  have hmodel : (shiftedLaplaceModelPackageAt 1).Bshared s
      = galerkinBcanLimitData.Bcan s := by
    show shiftedLaplaceLogDerivModel s
      = (shiftedLaplacePrimePackageAt 1).Bshared s
    exact (shiftedLaplacePrime_h_model s hs).symm
  rw [← hmodel]
  refine hconv.congr (fun n => ?_)
  show finiteCanonicalPrimePowerPackage
      (concretePrimePowerBelowCutoff ((n : ℝ) + 1))
      shiftedLaplaceHeatKernelC s
    = galerkinStagePackage.B_stage (galerkinStageSeq n) s
  show finiteCanonicalPrimePowerPackage
      (concretePrimePowerBelowCutoff ((n : ℝ) + 1))
      shiftedLaplaceHeatKernelC s
    = finiteCanonicalPrimePowerPackage
        (activePrimePowerPairsCenterBelow ((galerkinStageSeq n).R))
        shiftedLaplaceHeatKernelC s
  rw [galerkinStageSeq_R, activePairs_eq_concrete]

/-- **V9 endpoint.** RH from the two remaining convergence structures on the
genuine operator, alpha-aligned to the galerkin exhaustion. -/
theorem RH_from_galerkin_F_R
    (F : DFHLimitData galerkinStagePackage)
    (R : DMasterResidualData galerkinStagePackage)
    (hFalpha : F.alpha = galerkinStageSeq)
    (hRalpha : R.alpha = galerkinStageSeq) :
    RiemannHypothesis := by
  have hsigma0 : galerkinStagePackage.sigma0 = 1 := rfl
  have hRHP : RightHalfPlane galerkinStagePackage.sigma0 ⊆ Ω := by
    exact rightHalfPlane_subset_Omega galerkinStagePackage.sigma0
      (by rw [hsigma0]; norm_num)
  have hoverlap : DOverlapIdentityAPI galerkinStagePackage
      galerkinBcanLimitData F R := by
    refine DOverlapIdentityAPI_from_pointwise_stage_limits
      galerkinStageSplitAPI ?_ ?_ ?_
    · intro s hs
      exact F.pointwise_F_stage_tendsto_of_RHP_subset_Omega hRHP s hs
    · intro s hs
      have hs1 : s ∈ RightHalfPlane (1 : ℝ) := by
        rw [← hsigma0]; exact hs
      have := galerkin_hB s hs1
      rw [← hFalpha] at this
      exact this
    · intro s hs
      have := R.pointwise_R_stage_tendsto_of_RHP_subset_Omega hRHP s hs
      rw [hRalpha, ← hFalpha] at this
      exact this
  exact RH_from_DExportLayer
    { P := galerkinStagePackage
      B := galerkinBcanLimitData
      F := F
      R := R
      canRem := buildDCanRemAPIFromMasterResidual _ _ _ _
      overlap := hoverlap }
    (by rw [hsigma0])
    galerkinBcanLimitData_Cshared

#print axioms activePairs_eq_concrete
#print axioms galerkin_hB
#print axioms RH_from_galerkin_F_R

end
end RHFormalization
