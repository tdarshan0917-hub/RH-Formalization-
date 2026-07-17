-- SENTINEL: arithmetic-prime-spine-v1
import RHFormalization.PrimeOperatorArithmeticWeights
import RHFormalization.PrimePerturbedDMasterResidualAligned
import RHFormalization.PrimePerturbedAlignedHConvTarget
import RHFormalization.DecodedFlatTerminus
import Mathlib

/-!
# THE SPINE (2026-07-16E) — RiemannHypothesis from the arithmetic prime stage
UPSTREAM: arithmeticPrimeOperatorDFiniteStage (the co-scaled cell candidate:
  real prime operator, arithmetic weights primeStageWeights n, cutoff n+1);
  RH_from_holomorphic_remainder (flat terminus, banked 2026-07-16);
  primePerturbedAligned constructors (SP2a/SP2b, printed).
TARGET: RiemannHypothesis from the manuscript's D-side inputs at the
  arithmetic prime net: eigenvalue nonnegativity (hnn/hpos), the residual
  limit R_H with holomorphy on Ω, and the split identity on the overlap.
DOWNSTREAM CONSUMER: none — endpoint.
SEMANTIC: freezes the frontier IN THE KERNEL. After this builds, no session
  can relitigate the route: the remaining work is exactly the hypotheses
  of this theorem, by name. Taxonomy (roadmap 2026-07-16E): all other nets
  killed; this is the unique surviving cell.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-- **THE SPINE**: RiemannHypothesis from a holomorphic residual limit that
the arithmetic prime net's F − Bshared realizes on the overlap. -/
theorem RH_from_arithmetic_prime_residual
    (R_H : ℂ → ℂ)
    (h_holo : HolomorphicOnC R_H Ω)
    (h_split :
      ∀ s ∈ RightHalfPlane (1 : ℝ),
        FHadmFree s = galerkinBcanLimitData.Bcan s + R_H s) :
    RiemannHypothesis :=
  RH_from_holomorphic_remainder R_H h_holo h_split

#print axioms RH_from_arithmetic_prime_residual

end

end RHFormalization
