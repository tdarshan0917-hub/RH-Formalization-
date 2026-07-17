import RHFormalization.AdmissibleFreeTailAssembly
import RHFormalization.FHHoloFromStages

/-!
# RHFormalization.AdmissibleFreeFH

**Front F-adm, brick 2a.** Capstone of the free layer + opening of the prime
layer:

1. `FHadmFree_holo` — the integral-defined free limit is holomorphic on Ω,
   via the banked Weierstrass engine (`FH_holo_from_stage_epsN`) applied to
   the banked stage holomorphy (1b) and convergence (1d-ii). No closed form.
2. `FadmPrimeStage` — the prime/perturbation layer of the package F-slot,
   DEFINED as `F_stage − admissibleFreeStage`. Definition only.
3. `package_F_stage_eq_free_add_prime` — the exact split, anchoring the
   layered target `FHadm = FHadmFree + FHadmPrime` before any Duhamel work.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-- **The free limit is holomorphic on Ω** — Weierstrass via banked bricks;
`FHadmFree` stays integral-defined (Route A′), no closed form consumed. -/
theorem FHadmFree_holo : HolomorphicOnC FHadmFree Ω :=
  FH_holo_from_stage_epsN
    (fun n s => admissibleFreeStage n s)
    FHadmFree
    admissibleFreeStage_holo
    admissibleFreeStage_to_FHadmFree

/-- **The prime/perturbation layer of the admissible F-slot**: everything in
the package F-stage beyond the free density-normalized part. The Duhamel
representation and its limit `FHadmPrime` are the next front; the residual
stays combined (hQint discipline). -/
def FadmPrimeStage (n : ℕ) (s : ℂ) : ℂ :=
  galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
    - admissibleFreeStage n s

/-- **Exact layer split of the package F-slot**: `F_stage = free + prime`.
Anchors the layered convergence target — once `FadmPrimeStage → FHadmPrime`
is proven on Ω-compacts, `F_stage → FHadmFree + FHadmPrime` follows by
addition and Brick 1. -/
theorem package_F_stage_eq_free_add_prime (n : ℕ) (s : ℂ) :
    galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
      = admissibleFreeStage n s + FadmPrimeStage n s := by
  unfold FadmPrimeStage
  ring

#print axioms FHadmFree_holo
#print axioms package_F_stage_eq_free_add_prime

end

end RHFormalization
