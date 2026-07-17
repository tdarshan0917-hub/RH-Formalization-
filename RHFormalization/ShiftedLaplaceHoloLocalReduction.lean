import RHFormalization.HExplicitFormulaSplitChosenCshared
import RHFormalization.AnalyticWrappers

/-!
# RHFormalization.ShiftedLaplaceHoloLocalReduction

Generic local-extension reduction for the shifted/Laplace H-side function.

The previous attempt incorrectly used
`Harch_holomorphic_from_local_extensions`, which is specialized to
`Y.B.Cshared.Bshared + Zpole`.

Here we prove the generic local-extension lemma directly:

  if every z ∈ Ω has a local holomorphic extension locally equal to f,
  then f is holomorphic on Ω.

Then we specialize it to

  shiftedLaplacePrimePackageAt sigma0 + ZpoleSeries defaultZeroMultiplicityData.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-- The shifted/Laplace Appendix-H function. -/
abbrev shiftedLaplaceAppendixHFunction (sigma0 : ℝ) : ℂ → ℂ :=
  fun s : ℂ =>
    (shiftedLaplacePrimePackageAt sigma0).Bshared s
      + ZpoleSeries defaultZeroMultiplicityData s

/--
Generic local-extension-to-global-holomorphy lemma on Ω.

This is the package-generic version of the specialized
`Harch_holomorphic_from_local_extensions`.
-/
theorem holomorphicOnC_from_local_extensions_Omega
    (f : ℂ → ℂ)
    (hlocal :
      ∀ z : ℂ,
        z ∈ Ω →
          ∃ h : ℂ → ℂ,
            HolomorphicAtC h z ∧ LocalEqAtC h f z) :
    HolomorphicOnC f Ω := by
  intro z hzΩ
  rcases hlocal z hzΩ with ⟨h, hh, hEq⟩
  have hfz : HolomorphicAtC f z :=
    holomorphicAtC_congr hh hEq
  simpa [HolomorphicAtC] using hfz.analyticWithinAt

/--
Regular holomorphy can be wrapped as a local extension by choosing the function itself.
-/
theorem shiftedLaplace_regular_extensions
    (sigma0 : ℝ)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC (shiftedLaplaceAppendixHFunction sigma0) z) :
    ∀ z : ℂ,
      z ∈ Ω →
      (∀ W : ZeroWitness, z ≠ W.s0) →
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h z ∧
            LocalEqAtC h (shiftedLaplaceAppendixHFunction sigma0) z := by
  intro z hzΩ hnot
  refine ⟨shiftedLaplaceAppendixHFunction sigma0, ?_, ?_⟩
  · exact h_regular z hzΩ hnot
  · exact Filter.EventuallyEq.rfl

/--
Shifted/Laplace h_holo from local extensions at witness points and regular points.
-/
theorem shiftedLaplace_holo_from_localExtensions
    (sigma0 : ℝ)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h (shiftedLaplaceAppendixHFunction sigma0) W.s0)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC (shiftedLaplaceAppendixHFunction sigma0) z) :
    HolomorphicOnC (shiftedLaplaceAppendixHFunction sigma0) Ω := by
  apply holomorphicOnC_from_local_extensions_Omega
  intro z hzΩ
  by_cases hzW : ∃ W : ZeroWitness, z = W.s0
  · rcases hzW with ⟨W, rfl⟩
    exact h_witness W
  · have hnot : ∀ W : ZeroWitness, z ≠ W.s0 := by
      intro W hz_eq
      exact hzW ⟨W, hz_eq⟩
    exact shiftedLaplace_regular_extensions sigma0 h_regular z hzΩ hnot

/--
Build the shifted/Laplace Harch package from local extension data.
-/
def shiftedLaplaceHarchPackageFromLocalExtensions
    (sigma0 : ℝ)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h (shiftedLaplaceAppendixHFunction sigma0) W.s0)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC (shiftedLaplaceAppendixHFunction sigma0) z) :
    HArchPackage :=
  shiftedLaplaceHarchPackageFromHolo
    sigma0
    (shiftedLaplace_holo_from_localExtensions sigma0 h_witness h_regular)

/--
The shifted/Laplace split follows from local extension data.
-/
theorem shiftedLaplaceHarchPackageFromLocalExtensions_split
    (sigma0 : ℝ)
    (h_witness :
      ∀ W : ZeroWitness,
        ∃ h : ℂ → ℂ,
          HolomorphicAtC h W.s0 ∧
            LocalEqAtC h (shiftedLaplaceAppendixHFunction sigma0) W.s0)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC (shiftedLaplaceAppendixHFunction sigma0) z)
    (s : ℂ) :
    s ∈ RightHalfPlane sigma0 →
      (shiftedLaplacePrimePackageAt sigma0).Bshared s =
        (shiftedLaplaceHarchPackageFromLocalExtensions
          sigma0 h_witness h_regular).Harch s
          - ZpoleSeries defaultZeroMultiplicityData s := by
  intro hs
  exact
    shiftedLaplaceHarchPackageFromHolo_split
      sigma0
      (shiftedLaplace_holo_from_localExtensions sigma0 h_witness h_regular)
      s
      hs

#print axioms holomorphicOnC_from_local_extensions_Omega
#print axioms shiftedLaplace_regular_extensions
#print axioms shiftedLaplace_holo_from_localExtensions
#print axioms shiftedLaplaceHarchPackageFromLocalExtensions
#print axioms shiftedLaplaceHarchPackageFromLocalExtensions_split

end

end RHFormalization
