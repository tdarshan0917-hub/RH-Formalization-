import RHFormalization.ShiftedLaplaceRepMeromorphic
import RHFormalization.ShiftedLaplaceRepHZppFree
import RHFormalization.MeromorphyAssembly
import RHFormalization.EnvelopeFromZeroDensity
import Mathlib

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter Metric

/-
Direct meromorphy for the representative zero-pole series.

Do NOT use the generic `zeroPolePartial` convergence API here:
`ZpoleRepSeries` is built from representative partials, not the full
`ZeroExhaustion.zeroSet` partials.
-/
theorem ZpoleRepSeries_meromorphicOn_Omega_direct :
    MeromorphicOnC (ZpoleRepSeries defaultZeroMultiplicityData) Ω := by
  intro x hxΩ
  by_cases hx : x ∈ ZeroPoleSet
  · obtain ⟨ρ, hρ, hps⟩ := hx
    have hΩρ : polePoint ρ ∈ Ω := hps ▸ hxΩ
    have hoff : IsOffCritical ρ :=
      offCritical_of_polePoint_mem_Omega ρ hρ hΩρ
    let W : ZeroWitness :=
      { ρ := ρ
        h_zero := hρ
        h_offline := hoff
        s0 := polePoint ρ
        hs0_def := rfl
        hs0_in_Omega := hΩρ }
    have hpole :
        MeromorphicAt
          (ZpoleRepSeries defaultZeroMultiplicityData)
          W.s0 := by
      exact
        hasPrincipalPartAtC_meromorphicAt
          (ZpoleRepSeries defaultZeroMultiplicityData)
          W.s0
          ((zetaZeroMult W.ρ : ℂ))
          (shiftedLaplace_hZpp_rep_free W)
    exact hps ▸ hpole
  · exact
      (repZpole_analyticAt_nonpole
        defaultZeroMultiplicityData
        (buildEnvelopeFromZeroDensity
          defaultZeroMultiplicityData
          hsum_unconditional)
        x
        hxΩ
        hx).meromorphicAt

/-
Package direct Rep meromorphy into the existing generic API shape.

The convergence argument is intentionally ignored: the representative series has
a direct meromorphy proof, so we can satisfy the API without creating a fake
representative ZeroExhaustion.
-/
noncomputable def repZpoleMeromorphicFromSeriesAPI_direct :
    ZpoleMeromorphicFromSeriesAPI
      defaultZeroMultiplicityData
      defaultZeroExhaustion
      (ZpoleRepSeries defaultZeroMultiplicityData) :=
  { h_meromorphic := by
      intro _convergence _h_genuine_poles
      exact ZpoleRepSeries_meromorphicOn_Omega_direct }

#print axioms ZpoleRepSeries_meromorphicOn_Omega_direct
#print axioms repZpoleMeromorphicFromSeriesAPI_direct

end
end RHFormalization
