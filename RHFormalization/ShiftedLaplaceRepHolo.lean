import RHFormalization.ShiftedLaplaceRepWitnessFromBridge
import RHFormalization.ShiftedLaplaceHoloLocalReduction

namespace RHFormalization
noncomputable section
open Complex

theorem shiftedLaplace_rep_holo_from_localExtensions
    (sigma0 : ℝ)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h
              (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
                + ZpoleRepSeries defaultZeroMultiplicityData s) W.s0)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC
            (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
              + ZpoleRepSeries defaultZeroMultiplicityData s) z) :
    HolomorphicOnC
      (fun s => (shiftedLaplacePrimePackageAt sigma0).Bshared s
        + ZpoleRepSeries defaultZeroMultiplicityData s) Ω := by
  apply holomorphicOnC_from_local_extensions_Omega
  intro z hzΩ
  by_cases hw : ∃ W : ZeroWitness, z = W.s0
  · obtain ⟨W, rfl⟩ := hw
    exact h_witness W
  · push_neg at hw
    exact ⟨_, h_regular z hzΩ (fun W => hw W), Filter.EventuallyEq.rfl⟩

#print axioms shiftedLaplace_rep_holo_from_localExtensions

end
end RHFormalization
