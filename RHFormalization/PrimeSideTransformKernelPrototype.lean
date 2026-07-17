import RHFormalization.TwoInputEndpointFromEta
import RHFormalization.CanonicalPrimePowerConcreteTsumPackage

/-!
# RHFormalization.PrimeSideTransformKernelPrototype

This file introduces the missing model object for the h_holo track:
an s-dependent Laplace/Stieltjes-style prime-side kernel.

It does NOT alter the current endpoint.
It does NOT claim the final explicit-formula theorem.
It only creates the right kind of B-side object so we stop asking the
constant displacement kernel to carry nonzero principal parts.

Current false target:
  displacementCanonicalKernel (heatKernelG 1)

Correct model direction:
  Laplace transform of G_t or shifted K_t = exp(-t/4) G_t.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/-- Raw Laplace transform model of the one-dimensional heat kernel:
    ∫₀∞ exp(-s t) G_t(a) dt = (1 / (2 sqrt s)) exp(-a sqrt s),
with the principal complex square-root convention. -/
def rawLaplaceHeatKernelC : CanonicalKernelC :=
  fun a s =>
    (1 : ℂ) / (2 * Complex.sqrt s) *
      Complex.exp (-(a : ℂ) * Complex.sqrt s)

/-- Shifted closure kernel corresponding to K_t = exp(-t/4) G_t.
The formal transform is the raw transform evaluated at s + 1/4. -/
def shiftedLaplaceHeatKernelC : CanonicalKernelC :=
  fun a s =>
    (1 : ℂ) / (2 * Complex.sqrt (s + (1 / 4 : ℂ))) *
      Complex.exp (-(a : ℂ) * Complex.sqrt (s + (1 / 4 : ℂ)))

/-- The prime-side package built from the shifted s-dependent transform kernel.
This is only a prototype package; it is not yet wired into the endpoint. -/
def shiftedLaplacePrimePackage : CanonicalPrimePowerPackage :=
  canonicalPrimePowerPackageFromKernelTsum 0 shiftedLaplaceHeatKernelC

/-- Unfolding lemma for the transformed package. -/
theorem shiftedLaplacePrimePackage_Bshared_eq_tsum (s : ℂ) :
    shiftedLaplacePrimePackage.Bshared s =
      ∑' q : PrimePowerPair,
        q.weightC * shiftedLaplaceHeatKernelC q.center s := by
  rfl

/-- Sanity check: the new kernel is visibly s-dependent in its definition. -/
theorem shiftedLaplaceHeatKernelC_apply (a : ℝ) (s : ℂ) :
    shiftedLaplaceHeatKernelC a s =
      (1 : ℂ) / (2 * Complex.sqrt (s + (1 / 4 : ℂ))) *
        Complex.exp (-(a : ℂ) * Complex.sqrt (s + (1 / 4 : ℂ))) := by
  rfl

#print axioms rawLaplaceHeatKernelC
#print axioms shiftedLaplaceHeatKernelC
#print axioms shiftedLaplacePrimePackage
#print axioms shiftedLaplacePrimePackage_Bshared_eq_tsum
#print axioms shiftedLaplaceHeatKernelC_apply

end

end RHFormalization
