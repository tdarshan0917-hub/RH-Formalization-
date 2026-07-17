import RHFormalization.ShiftedLaplaceSqrtNonzero
import RHFormalization.OmegaTopology

/-!
# RHFormalization.ShiftedLaplaceOmegaGeometry

Geometry step for the shifted/Laplace B-regular branch.

Already banked:
- atomic shifted/Laplace kernel holomorphy;
- finite shifted/Laplace package holomorphy;
- shifted sqrt holomorphy on `Complex.slitPlane`;
- shifted sqrt nonzero from nonzero shifted argument.

This file proves the Ω geometry needed to feed those results:

  z ∈ Ω ⇒ shiftedLaplaceShift z ∈ Complex.slitPlane
  z ∈ Ω ⇒ shiftedLaplaceShift z ≠ 0.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

/--
If `z ∈ Ω`, then `z + 1/4` lies in Mathlib's principal square-root slit plane.
-/
theorem shiftedLaplaceShift_mem_slitPlane_of_mem_Omega
    (z : ℂ)
    (hzΩ : z ∈ Ω) :
    shiftedLaplaceShift z ∈ Complex.slitPlane := by
  have hz_cases : 0 < z.re ∨ z.im ≠ 0 :=
    (mem_Omega_iff_re_pos_or_im_ne_zero z).mp hzΩ
  rw [Complex.mem_slitPlane_iff]
  rcases hz_cases with hz_re | hz_im
  · left
    have hquarter : (0 : ℝ) < (1 / 4 : ℝ) := by norm_num
    have hpos : 0 < z.re + (1 / 4 : ℝ) := by linarith
    simpa [shiftedLaplaceShift] using hpos
  · right
    simpa [shiftedLaplaceShift] using hz_im

/--
If `z ∈ Ω`, then the shifted argument `z + 1/4` is nonzero.
-/
theorem shiftedLaplaceShift_ne_zero_of_mem_Omega
    (z : ℂ)
    (hzΩ : z ∈ Ω) :
    shiftedLaplaceShift z ≠ 0 :=
  Complex.slitPlane_ne_zero
    (shiftedLaplaceShift_mem_slitPlane_of_mem_Omega z hzΩ)

/--
Finite shifted/Laplace prime-power packages are holomorphic at every `z ∈ Ω`.
-/
theorem finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
    (I : Finset PrimePowerPair)
    (z : ℂ)
    (hzΩ : z ∈ Ω) :
    HolomorphicAtC
      (finiteCanonicalPrimePowerPackage I shiftedLaplaceHeatKernelC)
      z :=
  finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_shift_branch
    I
    z
    (shiftedLaplaceShift_mem_slitPlane_of_mem_Omega z hzΩ)
    (shiftedLaplaceShift_ne_zero_of_mem_Omega z hzΩ)

#print axioms shiftedLaplaceShift_mem_slitPlane_of_mem_Omega
#print axioms shiftedLaplaceShift_ne_zero_of_mem_Omega
#print axioms finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega

end

end RHFormalization
