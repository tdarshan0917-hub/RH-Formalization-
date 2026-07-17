import RHFormalization.ShiftedLaplaceWitnessCancellation

/-!
# RHFormalization.ShiftedLaplaceHoloFromCancellation

This is the compositor theorem for the shifted/Laplace Appendix-H h_holo target.

Already banked:
- `shiftedLaplace_holo_from_localExtensions`
- `shiftedLaplace_witness_extensions_from_cancellation_data`

This file composes them:

  witness cancellation data at every ZeroWitness
  + regular-point holomorphy away from witnesses
  ⇒ shifted/Laplace h_holo on Ω.

No `designedY`.
No old displacement kernel.
No root or endpoint edits.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
Shifted/Laplace h_holo from the two concrete local analytic inputs:
witness cancellation and regular-point holomorphy.
-/
theorem shiftedLaplace_holo_from_cancellation_and_regular
    (sigma0 : ℝ)
    (hcancel :
      ∀ W : ZeroWitness,
        ShiftedLaplaceWitnessCancellationData sigma0 W)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC (shiftedLaplaceAppendixHFunction sigma0) z) :
    HolomorphicOnC (shiftedLaplaceAppendixHFunction sigma0) Ω :=
  shiftedLaplace_holo_from_localExtensions
    sigma0
    (shiftedLaplace_witness_extensions_from_cancellation_data sigma0 hcancel)
    h_regular

/--
Build the shifted/Laplace Harch package from cancellation data and regular holomorphy.
-/
def shiftedLaplaceHarchPackageFromCancellationAndRegular
    (sigma0 : ℝ)
    (hcancel :
      ∀ W : ZeroWitness,
        ShiftedLaplaceWitnessCancellationData sigma0 W)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC (shiftedLaplaceAppendixHFunction sigma0) z) :
    HArchPackage :=
  shiftedLaplaceHarchPackageFromLocalExtensions
    sigma0
    (shiftedLaplace_witness_extensions_from_cancellation_data sigma0 hcancel)
    h_regular

/--
The shifted/Laplace Appendix-H split follows from cancellation data and regular holomorphy.
-/
theorem shiftedLaplaceHarchPackageFromCancellationAndRegular_split
    (sigma0 : ℝ)
    (hcancel :
      ∀ W : ZeroWitness,
        ShiftedLaplaceWitnessCancellationData sigma0 W)
    (h_regular :
      ∀ z : ℂ,
        z ∈ Ω →
        (∀ W : ZeroWitness, z ≠ W.s0) →
          HolomorphicAtC (shiftedLaplaceAppendixHFunction sigma0) z)
    (s : ℂ) :
    s ∈ RightHalfPlane sigma0 →
      (shiftedLaplacePrimePackageAt sigma0).Bshared s =
        (shiftedLaplaceHarchPackageFromCancellationAndRegular
          sigma0 hcancel h_regular).Harch s
          - ZpoleSeries defaultZeroMultiplicityData s := by
  intro hs
  exact
    shiftedLaplaceHarchPackageFromLocalExtensions_split
      sigma0
      (shiftedLaplace_witness_extensions_from_cancellation_data sigma0 hcancel)
      h_regular
      s
      hs

#print axioms shiftedLaplace_holo_from_cancellation_and_regular
#print axioms shiftedLaplaceHarchPackageFromCancellationAndRegular
#print axioms shiftedLaplaceHarchPackageFromCancellationAndRegular_split

end

end RHFormalization
