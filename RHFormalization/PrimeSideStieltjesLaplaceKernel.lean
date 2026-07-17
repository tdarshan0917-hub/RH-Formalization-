import RHFormalization.PrimeSideOperatorBridgeBLocalEF

/-!
# RHFormalization.PrimeSideStieltjesLaplaceKernel

GreenSwan phase.

The old displacement kernel

  displacementCanonicalKernel G := fun a _s => G a

is constant in `s`, so it cannot be the pole-producing Stieltjes/Laplace
prime-side object.

This file introduces the first explicit `s`-dependent candidate kernel.
It is deliberately separate from the green endpoint and does not replace
anything yet.

Analytic shape:
  Laplace transform of the shifted one-dimensional heat kernel

    K_t(a) = exp(-t/4) * (4πt)^(-1/2) * exp(-a^2/(4t))

has resolvent/Stieltjes profile

    exp(-a * sqrt(s + 1/4)) / (2 * sqrt(s + 1/4))

for a ≥ 0, on the principal branch.

Prime-power centers are positive, so no absolute value is needed at the
prime-power usage point.
-/

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter
open scoped BigOperators

/--
The shifted Laplace/resolvent variable.

The `+ 1/4` is the standard shift corresponding to
`exp(-t/4) * heatKernel`.
-/
def shiftedSpectralParameter (s : ℂ) : ℂ :=
  s + ((1 : ℂ) / 4)

/--
Candidate Stieltjes/Laplace transform of the shifted heat kernel at displacement
`a`.

This is the first concrete `s`-dependent replacement candidate for the old
displacement-only kernel.
-/
noncomputable def stieltjesLaplaceKernelCore
    (a : ℝ)
    (s : ℂ) : ℂ :=
  ((1 : ℂ) / 2)
    * (Complex.sqrt (shiftedSpectralParameter s))⁻¹
    * Complex.exp (-(a : ℂ) * Complex.sqrt (shiftedSpectralParameter s))

/--
The corresponding canonical kernel shape.
-/
noncomputable def stieltjesLaplaceCanonicalKernel :
    CanonicalKernelC :=
  fun a s => stieltjesLaplaceKernelCore a s

/--
The prime-power package obtained from the `s`-dependent Stieltjes/Laplace
kernel.

This is NOT yet asserted to be equal to `designedY.toOperatorResolventBridge.B`.
That identification is the next mathematical bridge.
-/
noncomputable def stieltjesLaplacePrimePowerPackage
    (s : ℂ) : ℂ :=
  ∑' q : PrimePowerPair,
    q.weightC * stieltjesLaplaceCanonicalKernel q.center s

#check shiftedSpectralParameter
#check stieltjesLaplaceKernelCore
#check stieltjesLaplaceCanonicalKernel
#check stieltjesLaplacePrimePowerPackage
#check RH_from_operatorBridgeB_localEF

end

end RHFormalization
