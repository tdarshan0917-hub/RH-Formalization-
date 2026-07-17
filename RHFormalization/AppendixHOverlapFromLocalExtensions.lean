import RHFormalization.AppendixHZeroDensityInterfaceEndpoint
import RHFormalization.HExplicitFormulaWitnessBranchFromPrincipalParts
import RHFormalization.HExplicitFormulaSplit

/-!
# RHFormalization.AppendixHOverlapFromLocalExtensions

This file repairs the regular-branch mismatch.

`Harch_holomorphic_from_witness_and_regular` expects local extension data at
regular points:

  ∃ h, HolomorphicAtC h z ∧ LocalEqAtC h (Bshared + Zpole) z

not merely:

  HolomorphicAtC (Bshared + Zpole) z.

At regular points we choose the extension to be the function itself.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

abbrev defaultAppendixHFunction : ℂ → ℂ :=
  fun s => designedY.B.Cshared.Bshared s
    + ZpoleSeries defaultZeroMultiplicityData s

/-- Turn ordinary holomorphy at a regular point into the local-extension
shape required by `Harch_holomorphic_from_witness_and_regular`. -/
theorem defaultAppendixH_regular_extensions
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC defaultAppendixHFunction z) :
    ∀ z : ℂ,
      z ∈ Ω →
      (∀ W : ZeroWitness, z ≠ W.s0) →
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h z ∧
            LocalEqAtC h
              (fun s => designedY.B.Cshared.Bshared s
                + ZpoleSeries defaultZeroMultiplicityData s) z := by
  intro z hzΩ hnot
  refine
    ⟨fun s => designedY.B.Cshared.Bshared s
        + ZpoleSeries defaultZeroMultiplicityData s, ?_, ?_⟩
  · simpa [defaultAppendixHFunction] using h_regular z hzΩ hnot
  · exact Filter.EventuallyEq.rfl

/-- Local witness extensions plus regular holomorphy imply the V9 `h_holo`
statement. -/
theorem designed_h_holo_from_localExtensions
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h defaultAppendixHFunction W.s0)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC defaultAppendixHFunction z) :
    HolomorphicOnC defaultAppendixHFunction Ω := by
  have hw :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h
              (fun s => designedY.B.Cshared.Bshared s
                + ZpoleSeries defaultZeroMultiplicityData s) W.s0 := by
    intro W
    simpa [defaultAppendixHFunction] using h_witness W

  have hr :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          ∃ h : ℂ → ℂ,
            HolomorphicAtC h z ∧
              LocalEqAtC h
                (fun s => designedY.B.Cshared.Bshared s
                  + ZpoleSeries defaultZeroMultiplicityData s) z :=
    defaultAppendixH_regular_extensions h_regular

  simpa [defaultAppendixHFunction] using
    Harch_holomorphic_from_witness_and_regular
      designedY
      (ZpoleSeries defaultZeroMultiplicityData)
      hw
      hr

/-- Build the Appendix-H package from local extension data. -/
def appendixHPackage_from_localExtensions
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h defaultAppendixHFunction W.s0)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC defaultAppendixHFunction z) :
    HArchPackage :=
  HarchPackageFromBsharedAddZpole
    designedY
    (ZpoleSeries defaultZeroMultiplicityData)
    (by
      simpa [defaultAppendixHFunction] using
        designed_h_holo_from_localExtensions h_witness h_regular)

/-- The constructed package satisfies the Appendix-H overlap identity. -/
theorem appendixH_overlap_from_localExtensions
    (sigmaH : ℝ)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h defaultAppendixHFunction W.s0)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC defaultAppendixHFunction z)
    (s : ℂ) :
    s ∈ RightHalfPlane sigmaH →
      designedY.B.Cshared.Bshared s =
        (appendixHPackage_from_localExtensions h_witness h_regular).Harch s
          - ZpoleSeries defaultZeroMultiplicityData s := by
  intro hs
  have hholo :
      HolomorphicOnC
        (fun s => designedY.B.Cshared.Bshared s
          + ZpoleSeries defaultZeroMultiplicityData s) Ω := by
    simpa [defaultAppendixHFunction] using
      designed_h_holo_from_localExtensions h_witness h_regular

  simpa [appendixHPackage_from_localExtensions, defaultAppendixHFunction] using
    HarchPackageFromBsharedAddZpole_split
      designedY
      (ZpoleSeries defaultZeroMultiplicityData)
      hholo
      sigmaH
      s
      hs

/-- Zero-density Appendix-H endpoint with `h_holo` replaced by local extension data. -/
theorem RH_from_appendixH_localExtensions_zeroDensity
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // IsNontrivialZetaZero ρ} =>
          ↑(defaultZeroMultiplicityData.mult ρ.1) / (1 + ρ.1.im ^ 2)))
    (sigmaH : ℝ)
    (hσH : 0 ≤ sigmaH)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h defaultAppendixHFunction W.s0)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC defaultAppendixHFunction z) :
    RiemannHypothesis :=
  RH_from_appendixH_interface_zeroDensity
    h_real_zero_free
    hsum
    (appendixHPackage_from_localExtensions h_witness h_regular)
    sigmaH
    hσH
    (appendixH_overlap_from_localExtensions sigmaH h_witness h_regular)

#print axioms defaultAppendixH_regular_extensions
#print axioms designed_h_holo_from_localExtensions
#print axioms appendixHPackage_from_localExtensions
#print axioms appendixH_overlap_from_localExtensions
#print axioms RH_from_appendixH_localExtensions_zeroDensity

end

end RHFormalization
