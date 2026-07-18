import RHFormalization.AppendixHZeroDensityInterfaceEndpoint
import RHFormalization.HExplicitFormulaSplit
import RHFormalization.HExplicitFormulaLocalExtensionAssembly

/-!
# RHFormalization.AppendixHOverlapFromLocalExtensions

This is NOT another RH endpoint.

Goal:
  remove the bare `h_appendixH_overlap / h_split` input by proving the split
  from local Appendix-H extension data.

The idea is:

  local holomorphic witnesses for Bshared + Zpole
  + regularity away from zero-witness points
  => HolomorphicOnC (Bshared + Zpole) Ω
  => define Harch := Bshared + Zpole
  => Bshared = Harch - Zpole by ring/simp.

This is the first real attack on the remaining h_split wall.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

#check Harch_holomorphic_from_witness_and_regular
#check HarchPackageFromBsharedAddZpole
#check HarchPackageFromBsharedAddZpole_split
#check RH_from_appendixH_interface_zeroDensity

/--
Build the Appendix-H archimedean package from local extensions of
`Bshared + ZpoleSeries`.
-/
def appendixHPackage_from_localExtensions
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h
              (fun s : ℂ =>
                designedY.B.Cshared.Bshared s
                  + ZpoleSeries defaultZeroMultiplicityData s)
              W.s0)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            HolomorphicAtC
              (fun s : ℂ =>
                designedY.B.Cshared.Bshared s
                  + ZpoleSeries defaultZeroMultiplicityData s)
              z) :
    HArchPackage :=
  HarchPackageFromBsharedAddZpole
    designedY
    (ZpoleSeries defaultZeroMultiplicityData)
    (Harch_holomorphic_from_witness_and_regular
      designedY
      (ZpoleSeries defaultZeroMultiplicityData)
      h_witness
      h_regular)

/--
The actual Appendix-H/E overlap split obtained from local extension data.

This is the theorem that begins removing the raw `h_split` input.
-/
theorem appendixH_overlap_from_localExtensions
    (sigmaH : ℝ)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h
              (fun s : ℂ =>
                designedY.B.Cshared.Bshared s
                  + ZpoleSeries defaultZeroMultiplicityData s)
              W.s0)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
          (∀ W : ZeroWitness, z ≠ W.s0) →
            HolomorphicAtC
              (fun s : ℂ =>
                designedY.B.Cshared.Bshared s
                  + ZpoleSeries defaultZeroMultiplicityData s)
              z) :
    ∀ s : ℂ,
      s ∈ RightHalfPlane sigmaH →
        designedY.B.Cshared.Bshared s =
          (appendixHPackage_from_localExtensions h_witness h_regular).Harch s
            - ZpoleSeries defaultZeroMultiplicityData s := by
  exact
    HarchPackageFromBsharedAddZpole_split
      designedY
      (ZpoleSeries defaultZeroMultiplicityData)
      (Harch_holomorphic_from_witness_and_regular
        designedY
        (ZpoleSeries defaultZeroMultiplicityData)
        h_witness
        h_regular)
      sigmaH

#check appendixHPackage_from_localExtensions
#check appendixH_overlap_from_localExtensions
#print axioms appendixH_overlap_from_localExtensions

end

end RHFormalization
