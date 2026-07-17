import RHFormalization.DBFFCompensator
import RHFormalization.DBFFBcorrWindowHolo
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# DBFFCompensatorHolo — Lemma D.OP.1(i): Ω-holomorphy of the compensator

ROUTE CARD
1. Target: second requirement of the `Bcorr` slot of `DBFFCorrectedBulkProvider`;
   completes D.OP.1 (overlap-vanishing banked in DBFFCompensator).
2. Objects: `compensatorM`, `sqrt_ne_zero'`, `sqrt_ne_half`, `Rcan_win_holo`.
3. Raw B on Ω? NO. 4. R = F − raw B forced? NO. 5. True outright.
6. Manuscript: D.OP-BOUND, Lemma D.OP.1(i). 7. Consumer: Bcorr assembly (O1–O3);
   `Rcan_compensated_holo` is the per-stage holo input for the compensated front.
Pin facts honored: `.mul` may yield Pi-forms (congr via `Pi.mul_apply`);
sqrt route copied from green `ShiftedLaplaceSqrtBranch`; final OnC conversion
copied from green `DBFFBcorrWindowHolo`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/-- The shifted square-root map `s ↦ √(s+1/4)` is analytic at every `z ∈ Ω`
(green SqrtBranch pattern: slit-plane preimage, `differentiableAt_sqrt`,
`DifferentiableOn.analyticOnNhd`). -/
theorem sqrtShiftFun_analyticAt {z : ℂ} (hz : z ∈ Ω) :
    AnalyticAt ℂ (fun s : ℂ => Complex.sqrt (s + (1/4:ℂ))) z := by
  have hz_shift : z + (1/4:ℂ) ∈ Complex.slitPlane := by
    first
      | exact shiftedLaplaceShift_mem_slitPlane_of_mem_Omega z hz
      | exact shiftedLaplaceShift_mem_slitPlane_of_mem_Omega hz
      | simpa using shiftedLaplaceShift_mem_slitPlane_of_mem_Omega z hz
      | simpa using shiftedLaplaceShift_mem_slitPlane_of_mem_Omega hz
  let U : Set ℂ := {w : ℂ | w + (1/4:ℂ) ∈ Complex.slitPlane}
  have hzU : z ∈ U := hz_shift
  have hcont : Continuous (fun w : ℂ => w + (1/4:ℂ)) := by fun_prop
  have hUopen : IsOpen U := by
    simpa [U] using Complex.isOpen_slitPlane.preimage hcont
  have hdiffOn :
      DifferentiableOn ℂ (fun s : ℂ => Complex.sqrt (s + (1/4:ℂ))) U := by
    intro w hw
    have hw_shift : w + (1/4:ℂ) ∈ Complex.slitPlane := hw
    have hshift_at : DifferentiableAt ℂ (fun s : ℂ => s + (1/4:ℂ)) w := by
      fun_prop
    have hsqrt_at :
        DifferentiableAt ℂ (fun s : ℂ => Complex.sqrt (s + (1/4:ℂ))) w := by
      first
        | simpa [Function.comp] using
            (Complex.differentiableAt_sqrt hw_shift).comp w hshift_at
        | simpa using
            (Complex.differentiableAt_sqrt hw_shift).comp w hshift_at
        | exact (Complex.differentiableAt_sqrt hw_shift).comp w hshift_at
    exact hsqrt_at.differentiableWithinAt
  have hAn :
      AnalyticOnNhd ℂ (fun s : ℂ => Complex.sqrt (s + (1/4:ℂ))) U :=
    DifferentiableOn.analyticOnNhd hdiffOn hUopen
  exact hAn z hzU

/-- **D.OP.1(i), pointwise**: the compensator is holomorphic at every `z ∈ Ω`. -/
theorem compensatorM_holomorphicAt (n : ℕ) {z : ℂ} (hz : z ∈ Ω) :
    HolomorphicAtC (fun s => compensatorM n s) z := by
  have hsq := sqrtShiftFun_analyticAt hz
  have h2ne : ((2:ℂ) * Complex.sqrt (z + (1/4:ℂ))) ≠ 0 :=
    mul_ne_zero (by norm_num) (sqrt_ne_zero' hz)
  have hden2ne : ((1/2:ℂ) - Complex.sqrt (z + (1/4:ℂ))) ≠ 0 := by
    first
      | exact sub_ne_zero_of_ne (Ne.symm (sqrt_ne_half hz))
      | exact sub_ne_zero.mpr (Ne.symm (sqrt_ne_half hz))
      | exact sub_ne_zero.mpr ((sqrt_ne_half hz).symm)
  -- factor 1/(2√)
  have h2an : AnalyticAt ℂ
      (fun s : ℂ => (2:ℂ) * Complex.sqrt (s + (1/4:ℂ))) z := by
    first
      | exact analyticAt_const.mul hsq
      | (refine (analyticAt_const.mul hsq).congr ?_
         filter_upwards with s
         first
           | rfl
           | (simp only [Pi.mul_apply]; done))
  have hfac : AnalyticAt ℂ
      (fun s : ℂ => 1 / ((2:ℂ) * Complex.sqrt (s + (1/4:ℂ)))) z := by
    have hinv := h2an.inv h2ne
    refine hinv.congr ?_
    filter_upwards with s
    first
      | (simp only [Pi.inv_apply, one_div]; done)
      | (rw [Pi.inv_apply, one_div])
      | (simp [Pi.inv_apply, one_div]; done)
      | (simp [Pi.inv_apply]; done)
  -- exponent
  have hlin : AnalyticAt ℂ
      (fun s : ℂ =>
        ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) * ((admR n : ℝ) : ℂ)) z := by
    first
      | exact (analyticAt_const.sub hsq).mul analyticAt_const
      | (refine ((analyticAt_const.sub hsq).mul analyticAt_const).congr ?_
         filter_upwards with s
         first
           | rfl
           | (simp only [Pi.mul_apply]; done))
  have hexp : AnalyticAt ℂ
      (fun s : ℂ =>
        Complex.exp
          (((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) * ((admR n : ℝ) : ℂ))) z := by
    first
      | exact hlin.cexp
      | exact Complex.analyticAt_exp.comp hlin
      | (have hE : AnalyticAt ℂ Complex.exp
            (((1/2:ℂ) - Complex.sqrt (z + (1/4:ℂ))) * ((admR n : ℝ) : ℂ)) := by
           have hdo : DifferentiableOn ℂ Complex.exp Set.univ :=
             Complex.differentiable_exp.differentiableOn
           exact (hdo.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
         have hcomp := hE.comp hlin
         refine hcomp.congr ?_
         filter_upwards with s
         first
           | rfl
           | (simp [Function.comp]; done))
  -- quotient exp/(1/2 − √)
  have hden2 : AnalyticAt ℂ
      (fun s : ℂ => (1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) z :=
    analyticAt_const.sub hsq
  have hquot : AnalyticAt ℂ
      (fun s : ℂ =>
        Complex.exp
          (((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ))) * ((admR n : ℝ) : ℂ))
          / ((1/2:ℂ) - Complex.sqrt (s + (1/4:ℂ)))) z := by
    first
      | exact hexp.div hden2 hden2ne
      | (have h := hexp.mul (hden2.inv hden2ne)
         refine h.congr ?_
         filter_upwards with s
         first
           | (rw [div_eq_mul_inv])
           | (simp only [Pi.mul_apply, div_eq_mul_inv]; done)
           | (simp [div_eq_mul_inv]; done))
  -- assemble
  first
    | (unfold compensatorM
       exact hfac.mul hquot)
    | (have hall := hfac.mul hquot
       refine hall.congr ?_
       filter_upwards with s
       first
         | (simp only [compensatorM, Pi.mul_apply]; done)
         | (simp [compensatorM, Pi.mul_apply]; done)
         | (simp only [Pi.mul_apply]; rfl)
         | rfl)

/-- **D.OP.1(i)**: the compensator is holomorphic on Ω at every stage. -/
theorem compensatorM_holo (n : ℕ) :
    HolomorphicOnC (fun s => compensatorM n s) Ω := by
  have hAt : ∀ z ∈ Ω, HolomorphicAtC (fun s => compensatorM n s) z :=
    fun z hz => compensatorM_holomorphicAt n hz
  first
    | (apply holomorphicOnC_of_forall_holomorphicAtC
       intro z hz
       exact hAt z hz)
    | (have hnhd : AnalyticOnNhd ℂ (fun s => compensatorM n s) Ω :=
         fun z hz => hAt z hz
       exact hnhd.analyticOn)
    | (intro z hz
       exact (hAt z hz).analyticWithinAt)

/-- **Per-stage Ω-holomorphy of the compensated window-corrected residual**
`R_stage + BcorrWin − M_α` — the compensated front's per-stage holo input. -/
theorem Rcan_compensated_holo (n : ℕ) :
    HolomorphicOnC
      (fun s =>
        galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
          + BcorrWin n s - compensatorM n s) Ω := by
  have h1 := Rcan_win_holo n
  have h2 := compensatorM_holo n
  first
    | (have hEq : (fun s =>
          galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
            + BcorrWin n s - compensatorM n s)
          = ((fun s =>
              galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
                + BcorrWin n s)
            - fun s => compensatorM n s) := by
         funext s; rfl
       rw [hEq]
       exact h1.sub h2)
    | (intro z hz
       have h := (h1 z hz).sub (h2 z hz)
       first
         | exact h
         | simpa using h)

#print axioms sqrtShiftFun_analyticAt
#print axioms compensatorM_holomorphicAt
#print axioms compensatorM_holo
#print axioms Rcan_compensated_holo

end

end RHFormalization
