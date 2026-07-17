import RHFormalization.ShiftedLaplaceBppFromBridge
import RHFormalization.ReflectionPairPoleClass
import RHFormalization.ZetaMultReflection

namespace RHFormalization
noncomputable section
open Complex Filter Topology

theorem groupedResidueCoeff_pair_eq_two_mul (W : ZeroWitness) :
    groupedResidueCoeff defaultZeroMultiplicityData
        (pairGroupedPoleClass defaultZeroMultiplicityData W)
      = (2 * (zetaZeroMult W.ρ : ℂ)) := by
  obtain ⟨hz, h0, h1⟩ := W.h_zero
  unfold groupedResidueCoeff groupedMultiplicitySum pairGroupedPoleClass
  simp only [defaultZeroMultiplicityData]
  have hne : W.ρ ≠ 1 - W.ρ := by
    intro hc
    have hcre := congrArg Complex.re hc
    simp [Complex.sub_re, Complex.one_re] at hcre
    exact W.h_offline (by linarith [hcre])
  rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
  rw [← zetaZeroMult_reflection h0 h1]
  push_cast
  ring

#print axioms groupedResidueCoeff_pair_eq_two_mul

end
end RHFormalization
