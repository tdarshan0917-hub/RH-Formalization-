import RHFormalization.ShiftedLaplaceRepMeromorphicDirect
import RHFormalization.ShiftedLaplaceRepHZppFree
import RHFormalization.ShiftedLaplaceRepWitnessFromBridge
import RHFormalization.ShiftedLaplaceRepCorrectedHarch
import RHFormalization.DefaultPrincipalPartGenuinePole
import RHFormalization.ReflectionPairPoleClass
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter Metric

/-- Rep-side principal part provider. -/
theorem shiftedLaplace_hZpp_rep_provider :
    ∀ W : ZeroWitness,
      HasPrincipalPartAtC (ZpoleRepSeries defaultZeroMultiplicityData)
        W.s0 ((zetaZeroMult W.ρ : ℂ)) :=
  shiftedLaplace_hZpp_rep_free

/-- Nonzero coefficient for the rep principal part. -/
theorem zetaZeroMult_complex_ne_zero_of_witness
    (W : ZeroWitness) :
    ((zetaZeroMult W.ρ : ℕ) : ℂ) ≠ 0 := by
  have hpos : 0 < zetaZeroMult W.ρ := by
    simpa [defaultZeroMultiplicityData, zetaZeroMult] using
      defaultZeroMultiplicityData.h_mult_pos W.ρ W.h_zero
  have hne_nat : zetaZeroMult W.ρ ≠ 0 := Nat.ne_of_gt hpos
  exact_mod_cast hne_nat

/-- Rep-side genuine pole provider from the principal part. -/
theorem shiftedLaplace_rep_genuine_poles :
    ∀ W : ZeroWitness,
      HasGenuinePole (ZpoleRepSeries defaultZeroMultiplicityData) W.s0 := by
  intro W
  exact
    ⟨((zetaZeroMult W.ρ : ℕ) : ℂ),
      zetaZeroMult_complex_ne_zero_of_witness W,
      shiftedLaplace_hZpp_rep_provider W⟩

#print axioms shiftedLaplace_hZpp_rep_provider
#print axioms zetaZeroMult_complex_ne_zero_of_witness
#print axioms shiftedLaplace_rep_genuine_poles

-- Confirm corrected Rep H-side names are now available in this provider file.
#check shiftedLaplace_hBpp_from_bridge
#check shiftedLaplace_hBpp_singleton_from_bridge
#check shiftedLaplaceRepCorrectedHarchPackage
#check shiftedLaplaceRepCorrectedHarchPackage_split
#check repCorrectedGlobal_holomorphicOn
#check repRaw
#check buildHSideGroupedPoleNormalFormDataFromPrincipalPartsPair

end
end RHFormalization
