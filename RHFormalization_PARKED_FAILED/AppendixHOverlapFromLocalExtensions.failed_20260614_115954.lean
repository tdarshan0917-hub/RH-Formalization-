import RHFormalization.AppendixHZeroDensityInterfaceEndpoint
import RHFormalization.HExplicitFormulaHolomorphyLocal
import RHFormalization.HExplicitFormulaSplit

/-!
# RHFormalization.AppendixHOverlapFromLocalExtensions

Repair of the local-extension Appendix-H bridge.

The failed version passed a regular-point hypothesis of type

  HolomorphicAtC F z

where `Harch_holomorphic_from_witness_and_regular` expects

  ∃ h, HolomorphicAtC h z ∧ LocalEqAtC h F z.

At regular points we choose `h := F`; local equality is reflexive.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

abbrev defaultAppendixHFunction : ℂ → ℂ :=
  fun s => designedY.B.Cshared.Bshared s
    + ZpoleSeries defaultZeroMultiplicityData s

/-- Convert ordinary regular-point holomorphy into the local-extension shape
expected by `Harch_holomorphic_from_witness_and_regular`. -/
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

/-- Local witness extensions plus regular holomorphy imply the old V9 `h_holo`
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
    simpa [defaultAppendixHFunction] using h_witness

  simpa [defaultAppendixHFunction] using
    Harch_holomorphic_from_witness_and_regular
      designedY
      (ZpoleSeries defaultZeroMultiplicityData)
      hw
      (defaultAppendixH_regular_extensions h_regular)

/-- Build the Appendix-H archimedean package from local extensions. -/
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

/-- The resulting package satisfies the Appendix-H overlap identity. -/
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

/-- Zero-density Appendix-H endpoint, with `h_holo` replaced by local extension data. -/
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
