/-
Pillar (c), regular-point case — REP VERSION:
at every non-witness z ∈ Ω, HarchΩ = model + ZpoleRepSeries is analytic.
Model half: shiftedLaplaceModel_regular (banked gate).
Rep-Zpole half: repZpole_analyticAt_nonpole fed by the pillar-(b)
unconditional envelope. Bridge: non-witness ⟹ z ∉ ZeroPoleSet.
-/
import RHFormalization.ShiftedLaplaceHarchOmega
import RHFormalization.ShiftedLaplaceModelHRegularProof
import RHFormalization.ShiftedLaplaceRepMeromorphic
import RHFormalization.HsumUnconditional

namespace RHFormalization

noncomputable section

open Complex Set

/-- Bridge: a non-witness point of Ω is not in the zero-pole set. -/
theorem not_mem_ZeroPoleSet_of_not_witness
    {z : ℂ} (hzΩ : z ∈ Ω) (hznw : ∀ W : ZeroWitness, z ≠ W.s0) :
    z ∉ ZeroPoleSet := by
  intro hmem
  rw [mem_ZeroPoleSet_iff] at hmem
  obtain ⟨ρ, hnz, hzpp⟩ := hmem
  have hΩρ : polePoint ρ ∈ Ω := hzpp ▸ hzΩ
  have hoff : IsOffCritical ρ := offCritical_of_polePoint_mem_Omega ρ hnz hΩρ
  exact hznw ⟨ρ, hnz, hoff, z, hzpp, hzΩ⟩ rfl

/-- The rep series is analytic at every non-witness point of Ω — unconditional. -/
theorem zpoleRepSeries_analyticAt_regular_unconditional
    {z : ℂ} (hzΩ : z ∈ Ω) (hznw : ∀ W : ZeroWitness, z ≠ W.s0) :
    AnalyticAt ℂ (ZpoleRepSeries defaultZeroMultiplicityData) z :=
  repZpole_analyticAt_nonpole defaultZeroMultiplicityData
    unconditionalZeroPoleEnvelope z hzΩ
    (not_mem_ZeroPoleSet_of_not_witness hzΩ hznw)

/-- **Pillar (c), regular case (rep version).** HarchΩ is analytic at every
non-witness point of Ω. Unconditional. -/
theorem shiftedLaplaceHarchOmega_analyticAt_regular
    {z : ℂ} (hzΩ : z ∈ Ω) (hznw : ∀ W : ZeroWitness, z ≠ W.s0) :
    AnalyticAt ℂ shiftedLaplaceHarchOmega z :=
  shiftedLaplaceHarchOmega_analyticAt
    (shiftedLaplaceModel_regular z hzΩ hznw)
    (zpoleRepSeries_analyticAt_regular_unconditional hzΩ hznw)

#print axioms not_mem_ZeroPoleSet_of_not_witness
#print axioms shiftedLaplaceHarchOmega_analyticAt_regular

end

end RHFormalization
