import RHFormalization.ExplicitPrimePackageIdentity
import RHFormalization.HExplicitFormulaWitnessBranchFromPrincipalParts
import RHFormalization.MeromorphyAssembly

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

-- Existing tools we want to use.
#check zpole_analyticAt_nonpole
#check offCritical_of_polePoint_mem_Omega
#check mkZeroWitness
#check Harch_holomorphic_from_principalParts_and_regular
#check Harch_holomorphic_from_witness_and_regular
#check designedY_BsharedOppositePrincipalPartData_of_tsum_principalParts
#check h_pp_from_convergence

-- Can Lean build a local extension for a sum from two analytic-at facts?
example
    (Zpole : ℂ → ℂ)
    (z : ℂ)
    (hB : HolomorphicAtC designedY.B.Cshared.Bshared z)
    (hZ : HolomorphicAtC Zpole z) :
    ∃ h : ℂ → ℂ,
      HolomorphicAtC h z ∧
        LocalEqAtC h
          (fun s : ℂ => designedY.B.Cshared.Bshared s + Zpole s)
          z := by
  refine ⟨fun s : ℂ => designedY.B.Cshared.Bshared s + Zpole s, ?_, ?_⟩
  · first
      | exact hB.add hZ
      | simpa [Pi.add_def] using hB.add hZ
  · exact Filter.EventuallyEq.rfl

-- Can "not equal to any witness pole" imply "not in ZeroPoleSet" inside Ω?
-- This is the key regular-branch geometry.
example
    (z : ℂ)
    (hzΩ : z ∈ Ω)
    (hnotW : ∀ W : ZeroWitness, z ≠ W.s0) :
    z ∉ ZeroPoleSet := by
  intro hzPole
  rcases hzPole with ⟨ρ, hρ, rfl⟩
  have hoff : IsOffCritical ρ := offCritical_of_polePoint_mem_Omega ρ hρ hzΩ
  exact hnotW (mkZeroWitness hρ hoff) rfl

end

end RHFormalization
