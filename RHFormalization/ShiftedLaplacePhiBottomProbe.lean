import RHFormalization.ShiftedLaplacePhiDeriv
import RHFormalization.ShiftedLaplaceBranchIdentity
import RHFormalization.ExplicitFormulaRegularBranch
import RHFormalization.DefaultZeroMultiplicity
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

theorem polePoint_shiftedPhi_eq_of_mem_Omega
    {z : ℂ} (hzΩ : z ∈ Ω) :
    polePoint (shiftedPhi z) = z := by
  unfold shiftedPhi polePoint
  set a : ℂ := Complex.sqrt (z + (1/4:ℂ)) with ha
  have hsqrt_sq : a ^ 2 = z + (1/4:ℂ) := by
    -- use the same sqrt-square theorem style your repo already uses
    simpa [a, ha] using sq_sqrt (z + (1/4:ℂ))
  have hcalc :
      -((a + (1/2:ℂ)) * (1 - (a + (1/2:ℂ)))) = a ^ 2 - (1/4:ℂ) := by
    ring
  rw [hcalc, hsqrt_sq]
  ring

theorem zeta_shiftedPhi_ne_zero_of_notWitness_probe
    (ZF : ZetaZeroFacts)
    (z : ℂ)
    (hzΩ : z ∈ Ω)
    (hnotW : ∀ W : ZeroWitness, z ≠ W.s0) :
    riemannZeta (shiftedPhi z) ≠ 0 := by
  intro hzeta
  have hpole : polePoint (shiftedPhi z) = z :=
    polePoint_shiftedPhi_eq_of_mem_Omega hzΩ

  have hNT : IsNontrivialZetaZero (shiftedPhi z) := by
    refine ⟨hzeta, ?_, ?_⟩
    · -- lower strip bound: Re(phi z) > 0
      unfold shiftedPhi
      simp [Complex.add_re]
      have hsqrt_nonneg : 0 ≤ (Complex.sqrt (z + (1/4:ℂ))).re := by
        exact Complex.sqrt_re_nonneg (z + (1/4:ℂ))
      linarith
    · -- upper strip bound: if Re(phi z) ≥ 1, zero-free half-plane contradicts hzeta
      by_contra hnot
      have hle : 1 ≤ (shiftedPhi z).re := le_of_not_gt hnot
      exact (riemannZeta_ne_zero_of_one_le_re hle) hzeta

  have hoffI : IsOffCritical (shiftedPhi z) := by
    have hΩp : polePoint (shiftedPhi z) ∈ Ω := by
      simpa [hpole] using hzΩ
    exact offCritical_of_polePoint_mem_Omega (shiftedPhi z) hNT hΩp

  have hoff : (shiftedPhi z).re ≠ 1 / 2 := by
    simpa [IsOffCritical] using hoffI

  exact hnotW (mkZeroWitness ZF (shiftedPhi z) hNT hoff) hpole.symm

#print axioms polePoint_shiftedPhi_eq_of_mem_Omega

end
end RHFormalization
