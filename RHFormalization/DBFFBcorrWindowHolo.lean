import RHFormalization.DBFFBcorrWindow
import RHFormalization.AdmissibleRStageHolo
import RHFormalization.ShiftedLaplaceOmegaGeometry

/-!
# DBFFBcorrWindowHolo — per-stage Ω-holomorphy of the window-corrected residual

ROUTE CARD
1. Target: D.MASTER-RESIDUAL per-stage-holomorphy input for the
   `DBFFCorrectedBulkProvider` instantiation (Montel needs it; manuscript D.MR
   uses it explicitly). Composes with `AclassCorr` when Brick B lands.
2. Objects: `BcorrWin` (Brick A), `R_stage` (holo banked).
3. Raw B on Ω? NO. 4. R = F − raw B forced? NO. 5. True outright.
6. Manuscript: D.MR per-stage holomorphy line. 7. Consumer: Bricks B/E.
Pin facts: `.mul`/`Finset.analyticAt_sum` produce Pi-forms — congr via
`Pi.mul_apply` / `Finset.sum_apply`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/-- Each `BcorrWin` summand is holomorphic at every `z ∈ Ω`, via the banked
singleton-package holomorphy. -/
theorem BcorrWin_term_holomorphicAt (n : ℕ) (q : PrimePowerPair)
    {z : ℂ} (hz : z ∈ Ω) :
    HolomorphicAtC
      (fun s => q.weightC * ((q.center / (2 * admL n) : ℝ) : ℂ) *
        shiftedLaplaceHeatKernelC q.center s) z := by
  have hpack : HolomorphicAtC
      (finiteCanonicalPrimePowerPackage ({q} : Finset PrimePowerPair)
        shiftedLaplaceHeatKernelC) z :=
    finiteCanonicalPrimePowerPackage_shiftedLaplace_holomorphicAt_of_mem_Omega
      ({q} : Finset PrimePowerPair) z hz
  have hpackEq : finiteCanonicalPrimePowerPackage ({q} : Finset PrimePowerPair)
      shiftedLaplaceHeatKernelC
      = fun s => q.weightC * shiftedLaplaceHeatKernelC q.center s := by
    funext s
    simp [finiteCanonicalPrimePowerPackage]
  rw [hpackEq] at hpack
  have hmul : AnalyticAt ℂ
      ((fun _ : ℂ => ((q.center / (2 * admL n) : ℝ) : ℂ)) *
        fun s => q.weightC * shiftedLaplaceHeatKernelC q.center s) z :=
    analyticAt_const.mul hpack
  refine hmul.congr ?_
  filter_upwards with s
  simp only [Pi.mul_apply]
  ring

/-- **`BcorrWin` is holomorphic on Ω at every stage.** -/
theorem BcorrWin_holo (n : ℕ) :
    HolomorphicOnC (fun s => BcorrWin n s) Ω := by
  have hAt : ∀ z ∈ Ω, HolomorphicAtC (fun s => BcorrWin n s) z := by
    intro z hz
    have hterm : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
        AnalyticAt ℂ
          (fun s => q.weightC * ((q.center / (2 * admL n) : ℝ) : ℂ) *
            shiftedLaplaceHeatKernelC q.center s) z :=
      fun q _ => BcorrWin_term_holomorphicAt n q hz
    have hsum0 : AnalyticAt ℂ
        (∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          fun s => q.weightC * ((q.center / (2 * admL n) : ℝ) : ℂ) *
            shiftedLaplaceHeatKernelC q.center s) z :=
      Finset.analyticAt_sum (activePrimePowerPairsCenterBelow (admR n)) hterm
    refine hsum0.congr ?_
    filter_upwards with s
    first
      | simp [BcorrWin, Finset.sum_apply]
      | (simp only [Finset.sum_apply]
         rfl)
      | rfl
  first
    | (apply holomorphicOnC_of_forall_holomorphicAtC
       intro z hz
       exact hAt z hz)
    | (have hnhd : AnalyticOnNhd ℂ (fun s => BcorrWin n s) Ω :=
         fun z hz => hAt z hz
       exact hnhd.analyticOn)
    | (intro z hz
       exact (hAt z hz).analyticWithinAt)

/-- **Per-stage Ω-holomorphy of the window-corrected residual**
`R_stage + BcorrWin` — the D.MR per-stage input; extends to the full `Rcan`
by one more `.sub` when `AclassCorr` (Brick B) lands. -/
theorem Rcan_win_holo (n : ℕ) :
    HolomorphicOnC
      (fun s =>
        galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
          + BcorrWin n s) Ω := by
  have hR := admissible_R_stage_holo n
  have hW := BcorrWin_holo n
  have hEq : (fun s =>
      galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
        + BcorrWin n s)
      = (fun s =>
          galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s)
        + fun s => BcorrWin n s := by
    funext s; rfl
  rw [hEq]
  exact hR.add hW

#print axioms BcorrWin_term_holomorphicAt
#print axioms BcorrWin_holo
#print axioms Rcan_win_holo

end

end RHFormalization
