import RHFormalization.CanonicalPrimePowerPackage
import RHFormalization.DOperatorExport

/-!
# RHFormalization.PrimePowerWeightNormalizationLock

Locks the global prime-power normalization used by the canonical package.

This file is not an RH endpoint.

It records theorem-backed facts that the Lean package is using the manuscript's
frozen normalization

  w(q) = Λ(q) / sqrt(q)

and that the finite canonical package uses the complexified prime-power weight.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter
open scoped BigOperators

/--
The scalar spike weight is definitionally the manuscript normalization
`Λq / sqrt q`.
-/
theorem spikeWeight_eq_Lambda_div_sqrt
    (Λq q : ℝ) :
    spikeWeight Λq q = Λq / Real.sqrt q := by
  rfl

/--
The complex prime-power weight is the complexification of the real
prime-power weight.
-/
theorem PrimePowerPair.weightC_eq_coe_weightReal
    (q : PrimePowerPair) :
    q.weightC = (q.weightReal : ℂ) := by
  rfl

/--
The finite canonical prime-power package is exactly the finite weighted sum
using `q.weightC`.
-/
theorem finiteCanonicalPrimePowerPackage_eq_weighted_sum
    (I : Finset PrimePowerPair)
    (K : CanonicalKernelC)
    (s : ℂ) :
    finiteCanonicalPrimePowerPackage I K s =
      I.sum (fun q : PrimePowerPair => q.weightC * K q.center s) := by
  rfl

/--
The finite canonical prime-power package can also be written using the
complexification of `q.weightReal`.
-/
theorem finiteCanonicalPrimePowerPackage_eq_weightReal_sum
    (I : Finset PrimePowerPair)
    (K : CanonicalKernelC)
    (s : ℂ) :
    finiteCanonicalPrimePowerPackage I K s =
      I.sum (fun q : PrimePowerPair => (q.weightReal : ℂ) * K q.center s) := by
  simp [finiteCanonicalPrimePowerPackage, PrimePowerPair.weightC_eq_coe_weightReal]

end

end RHFormalization
