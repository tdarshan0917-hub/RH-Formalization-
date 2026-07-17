import RHFormalization.RealPrimeConcreteTsumS
import RHFormalization.ShiftedLaplaceMajorant
import RHFormalization.AdmissibleGalerkinStage
import RHFormalization.AppendixDActiveSpikeCodesFromCenterCutoff

/-!
# DBFFBcorrWindow — Brick A of the corrected-bulk instantiation

ROUTE CARD
1. Target: the `Bcorr` slot of `DBFFCorrectedBulkProvider`
   (consumer: `RH_from_DBFF_corrected_bulk`). `Bcorr = BcorrWin + AclassCorr`;
   this file supplies the WINDOW component and its overlap vanishing.
2. Objects: BcorrWin n s = Σ_{q: center ≤ admR n} weightC q ·
   (center q/(2·admL n)) · shiftedLaplaceHeatKernelC (center q) s — the
   deficit between the bare package B_stage and the density-normalized
   windowed package, from D.CANONICAL-WINDOW's overlap formula
   g_{t,L}(a) = G_t(a)·(2L−|a|)₊/(2L) after the shifted Laplace transform.
3. Raw B on Ω? NO — finite sums only; bounds only on RHP(1).
4. R = F − raw B forced? NO.
5. Satisfiable/true: yes — everything here is proved outright, no fields.
6. Manuscript: D.CANONICAL-WINDOW (c_w = 1, explicit sharp-window overlap).
7. Consumer: the concrete `DBFFCorrectedBulkProvider` term (Bricks B–F).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter

open scoped Topology BigOperators

/-- **Window deficit** at admissible stage `n`: the difference between the
bare finite package and the density-normalized windowed package. -/
def BcorrWin (n : ℕ) (s : ℂ) : ℂ :=
  (activePrimePowerPairsCenterBelow (admR n)).sum fun q =>
    q.weightC * ((q.center / (2 * admL n) : ℝ) : ℂ) *
      shiftedLaplaceHeatKernelC q.center s

/-- The fixed-`s` prime mass: tsum of term norms (finite on RHP(1)). -/
def BcorrMass (s : ℂ) : ℝ :=
  ∑' q : PrimePowerPair,
    ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖

theorem admL_pos' (n : ℕ) : (0 : ℝ) < admL n := by
  show (0 : ℝ) < ((n : ℝ) + 2) ^ 3
  positivity

/-- Pointwise norm bound: window deficit ≤ (cutoff/window ratio) × mass. -/
theorem BcorrWin_norm_le (n : ℕ) {s : ℂ}
    (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    ‖BcorrWin n s‖ ≤ admR n / (2 * admL n) * BcorrMass s := by
  have hL2 : (0 : ℝ) < 2 * admL n := by
    have := admL_pos' n; linarith
  have hnorm : Summable (fun q : PrimePowerPair =>
      ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖) := by
    have hsum := aligned_h_summable s hs
    first
      | exact summable_norm_iff.mpr hsum
      | exact hsum.norm
      | exact (summable_norm_iff).mpr hsum
  have hterm : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      ‖q.weightC * ((q.center / (2 * admL n) : ℝ) : ℂ) *
          shiftedLaplaceHeatKernelC q.center s‖ ≤
        admR n / (2 * admL n) *
          ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖ := by
    intro q hq
    have hcle : q.center ≤ admR n :=
      ((activePrimePowerPairsCenterBelow_mem (admR n) q).mp hq).2
    have hfrac0 : (0 : ℝ) ≤ q.center / (2 * admL n) :=
      div_nonneg (center_nonneg q) hL2.le
    have hcnorm : ‖((q.center / (2 * admL n) : ℝ) : ℂ)‖
        = q.center / (2 * admL n) := by
      first
        | rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hfrac0]
        | rw [Complex.norm_ofReal, abs_of_nonneg hfrac0]
        | (simp only [Complex.norm_real, Real.norm_eq_abs]
           exact abs_of_nonneg hfrac0)
        | (simp [abs_of_nonneg hfrac0]
           done)
    have hfrac : q.center / (2 * admL n) ≤ admR n / (2 * admL n) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hcle (inv_nonneg.mpr hL2.le)
    calc ‖q.weightC * ((q.center / (2 * admL n) : ℝ) : ℂ) *
            shiftedLaplaceHeatKernelC q.center s‖
        = q.center / (2 * admL n) *
            ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖ := by
          rw [norm_mul, norm_mul, norm_mul, hcnorm]; ring
      _ ≤ admR n / (2 * admL n) *
            ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖ :=
          mul_le_mul_of_nonneg_right hfrac (norm_nonneg _)
  have hratio0 : (0 : ℝ) ≤ admR n / (2 * admL n) :=
    div_nonneg (admR_pos n).le hL2.le
  calc ‖BcorrWin n s‖
      ≤ (activePrimePowerPairsCenterBelow (admR n)).sum fun q =>
          ‖q.weightC * ((q.center / (2 * admL n) : ℝ) : ℂ) *
            shiftedLaplaceHeatKernelC q.center s‖ := norm_sum_le _ _
    _ ≤ (activePrimePowerPairsCenterBelow (admR n)).sum fun q =>
          admR n / (2 * admL n) *
            ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖ :=
        Finset.sum_le_sum hterm
    _ = admR n / (2 * admL n) *
          (activePrimePowerPairsCenterBelow (admR n)).sum fun q =>
            ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖ := by
        rw [Finset.mul_sum]
    _ ≤ admR n / (2 * admL n) * BcorrMass s := by
        refine mul_le_mul_of_nonneg_left ?_ hratio0
        first
          | exact sum_le_tsum _ (fun q _ => norm_nonneg _) hnorm
          | exact Finset.sum_le_tsum _ (fun q _ => norm_nonneg _) hnorm
          | exact hnorm.sum_le_tsum _ (fun q _ => norm_nonneg _)

/-- The cutoff/window ratio vanishes: `log(n+2)/(4(n+2)³) → 0`. -/
theorem admRatio_tendsto_zero :
    Tendsto (fun n : ℕ => admR n / (2 * admL n)) atTop (𝓝 (0 : ℝ)) := by
  have h0 : ∀ n : ℕ, (0 : ℝ) ≤ admR n / (2 * admL n) := by
    intro n
    have := admL_pos' n
    exact div_nonneg (admR_pos n).le (by linarith)
  have hb : ∀ n : ℕ, admR n / (2 * admL n) ≤ 1 / ((n : ℝ) + 2) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : (0 : ℝ) < (n : ℝ) + 2 := by linarith
    have h4x3 : (4 * ((n : ℝ) + 2) ^ 3) ≠ 0 := by positivity
    have h4x2 : (4 * ((n : ℝ) + 2) ^ 2) ≠ 0 := by positivity
    have hlog : Real.log ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      first
        | exact Real.log_le_self hp.le
        | (have h := Real.log_le_sub_one_of_pos hp
           linarith)
    show Real.log ((n : ℝ) + 2) / 2 / (2 * ((n : ℝ) + 2) ^ 3)
        ≤ 1 / ((n : ℝ) + 2)
    have hx1 : Real.log ((n : ℝ) + 2) * ((n : ℝ) + 2)
        ≤ ((n : ℝ) + 2) * ((n : ℝ) + 2) :=
      mul_le_mul_of_nonneg_right hlog hp.le
    have hx2 : (0 : ℝ) ≤ ((n : ℝ) + 2) * ((n : ℝ) + 2) * (4 * ((n : ℝ) + 2) - 1) := by
      nlinarith [hn0]
    first
      | (rw [div_le_div_iff₀ (by positivity) hp]
         nlinarith [hx1, hx2])
      | (rw [div_le_div_iff (by positivity) hp]
         nlinarith [hx1, hx2])
  refine squeeze_zero h0 hb ?_
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
    first
      | exact tendsto_natCast_atTop_atTop
      | exact tendsto_nat_cast_atTop_atTop
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 hcast
  simpa [one_div] using h1.inv_tendsto_atTop

/-- **Overlap vanishing (Brick A closed)**: the window deficit tends to 0
pointwise on RHP(1) — the `h_Bcorr_overlap0`-shaped fact for the window
component of `Bcorr`. -/
theorem BcorrWin_overlap0 {s : ℂ}
    (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto (fun n : ℕ => BcorrWin n s) atTop (𝓝 (0 : ℂ)) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _)
    (fun n => BcorrWin_norm_le n hs) ?_
  simpa using admRatio_tendsto_zero.mul_const (BcorrMass s)

#print axioms BcorrWin
#print axioms BcorrWin_norm_le
#print axioms admRatio_tendsto_zero
#print axioms BcorrWin_overlap0

end

end RHFormalization
