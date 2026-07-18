# H_HOLO_GUARDRAIL

Current green state:
- RH_from_eta_zeroDensity_holo is green.
- AppendixHOverlapFromLocalExtensions is green.
- h_real_zero_free is closed by EtaPositivity.
- Remaining inputs: hsum and h_holo.

Critical invariant:
The current designedY.B.Cshared.Bshared is built from

  displacementCanonicalKernel (heatKernelG 1)

and this kernel ignores s:

  fun G a _s => G a

Therefore the current explicit Bshared is constant in s and cannot carry
nonzero principal parts.

Hard stop:
Do not attempt to prove

  HasPrincipalPartAtC
    (fun s => ∑' q, q.weightC *
      displacementCanonicalKernel (heatKernelG 1) q.center s)
    W.s0
    nonzeroCoeff

This is the false loop.

Next real target:
Introduce or identify the actual s-dependent Stieltjes/Laplace/resolvent
prime-side kernel, then prove principal parts for that transformed object.
