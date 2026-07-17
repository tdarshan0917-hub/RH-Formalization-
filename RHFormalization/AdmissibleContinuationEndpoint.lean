import RHFormalization.AdmissibleGalerkinEndpoint
import RHFormalization.AdmissibleFreeFH
import RHFormalization.HonestEndpointV7

/-!
# THE CORRECTED HONEST ENDPOINT (post raw-B firewall audit)

ROUTE CARD
1. Target: RiemannHypothesis via the V7 spine (`RH_from_D_with_prime_interface`,
   banked axiom-clean; E/F/H/ZF internal).
2. F: `FHadmFree` — banked Ω-holomorphic admissible operator limit.
3. B: `(shiftedLaplacePrimePackageAt 1).Bshared` — OVERLAP-ONLY (RHP(1)).
4. R: a single hypothesized function `RHfun` — NOT definitionally F − B_stage.
5. Domain: split on RHP(1) only; Ω-holomorphy only for FH and RHfun.
6. Raw B on Ω required?  NO.
7. R = F − raw B forced on Ω?  NO (no stage families here).
8. Manuscript object: D.ANCHOR's continued remainder `R^Ω` / D.CAN-REM output.
9. Closing estimate: the manuscript's operator-side construction of `RHfun`
   (Stieltjes/Q_res representation) — the genuine remaining frontier.
10. Consumer: `RH_from_D_with_prime_interface` (V7).

Under RH, `RHfun := FHadmFree − shiftedLaplaceLogDerivModel` satisfies both
hypotheses (all polePoints then lie on the cut), so the endpoint is
NON-VACUOUS and conclusion-shaped exactly where the manuscript claims its
content: Appendix D must produce the continuation from the operator.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- **The corrected D-side endpoint**: RH from an Ω-holomorphic remainder
splitting `FHadmFree` against the canonical package on the overlap. No raw-B
object appears on Ω. -/
theorem RH_from_admissible_continuation
    (RHfun : ℂ → ℂ)
    (hRH_holo : HolomorphicOnC RHfun Ω)
    (h_split : ∀ s ∈ RightHalfPlane (1 : ℝ),
        FHadmFree s = (shiftedLaplacePrimePackageAt 1).Bshared s + RHfun s) :
    RiemannHypothesis :=
  RH_from_D_with_prime_interface
    { FH := FHadmFree
      B := (shiftedLaplacePrimePackageAt 1).Bshared
      RH := RHfun
      sigma0 := 1
      hFH_holo := FHadmFree_holo
      hRH_holo := hRH_holo
      h_split := h_split }
    (le_refl 1)
    (fun _ _ => rfl)

/-- **Model form**: RH from the single statement that the explicit difference
`FHadmFree − shiftedLaplaceLogDerivModel` (free integral minus the
ζ-log-derivative pullback) is holomorphic on Ω. -/
theorem RH_from_model_continuation
    (h_holo : HolomorphicOnC
        (fun s => FHadmFree s - shiftedLaplaceLogDerivModel s) Ω) :
    RiemannHypothesis := by
  refine RH_from_admissible_continuation
    (fun s => FHadmFree s - shiftedLaplaceLogDerivModel s) h_holo ?_
  intro s hs
  have hm : (shiftedLaplacePrimePackageAt 1).Bshared s
      = shiftedLaplaceLogDerivModel s := by
    first
      | exact shiftedLaplacePrime_h_model s hs
      | exact (shiftedLaplacePrime_h_model s hs).symm
  rw [hm]
  ring

#print axioms RH_from_admissible_continuation
#print axioms RH_from_model_continuation

end

end RHFormalization
