-- SENTINEL: BRIDGE-v1
import RHFormalization.AdaptiveGalerkinDefectGate
import RHFormalization.AdmissibleS1MassSqrt
import RHFormalization.CanonicalPrimePowerHeatKernelGaussianCoreBounds
import RHFormalization.AdmissibleWeightNonneg

/-!
# Adaptive stage mass = S₁ mass (defect-gate bridge)

`adaptiveStageMass n` (pairs-indexed, ‖weightC‖) equals `S1mass (admR n)`
(codes-indexed, ppWeightReal), via the ppCode/ppDecode roundtrip and the
nonnegativity of the frozen weight Λ(q)/√q. Combined with R0
(`S1mass_admR_le_sqrt`), the gate's weighted stage sum inherits the
√(n+2) rate.
-/

namespace RHFormalization

/-- The pairs-indexed defect-gate mass equals the codes-indexed S₁ mass. -/
theorem adaptiveStageMass_eq_S1mass (n : ℕ) :
    adaptiveStageMass n = S1mass (admR n) := by
  classical
  have hcodes : activePrimePowerCodesCenterBelow (admR n)
      = (activePrimePowerPairsCenterBelow (admR n)).image ppCode := rfl
  unfold adaptiveStageMass S1mass
  rw [hcodes, Finset.sum_image]
  · refine Finset.sum_congr rfl (fun q _hq => ?_)
    have h1 : ppWeightReal (ppCode q) = q.weightReal := by
      simp [ppWeightReal, ppDecode_ppCode, PrimePowerPair.weightC]
    rw [h1, norm_weightC_eq_abs_weightReal,
      abs_of_nonneg (PrimePowerPair.weightReal_nonneg q)]
  · intro m _hm k _hk hmk
    have h := congrArg ppDecode hmk
    rwa [ppDecode_ppCode, ppDecode_ppCode] at h

/-- **The gate mass rate**: `adaptiveStageMass n ≤ 2·(√(n+2) + 2)`. -/
theorem adaptiveStageMass_le_sqrt (n : ℕ) :
    adaptiveStageMass n ≤ 2 * (Real.sqrt ((n : ℝ) + 2) + 2) := by
  rw [adaptiveStageMass_eq_S1mass]
  exact S1mass_admR_le_sqrt n

#print axioms adaptiveStageMass_eq_S1mass
#print axioms adaptiveStageMass_le_sqrt

end RHFormalization
