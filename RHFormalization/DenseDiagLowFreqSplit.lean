import RHFormalization.DenseCenteredDiagClosed
import Mathlib

/-!
# DenseDiagLowFreqSplit — KB3a: `C_kk = W_k + r_k` with `r_k` uniformly small

`W_k := Σ_q w(q) cos(κ_k c_q) − ∫₀^R e^{u/2} cos(κ_k u) du` (the low-frequency
witness), and `|C_kk − W_k| ≤ (2R/L)·(S1mass R + R·e^{R/2})`.
Third brick of the B8 kill theorem.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- Low-frequency witness at Galerkin mode `k`. -/
def lowFreqWitness (n : ℕ) (k : Fin (denseN n)) : ℝ :=
  (∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
      q.weightReal * Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * q.center / denseL n))
    - ∫ u in (0:ℝ)..(admR n),
        Real.exp (u / 2) * Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)

theorem abs_sin_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : |Real.sin x| ≤ x := by
  rw [abs_le]
  constructor
  · rcases le_or_gt x 1 with h | h
    · have := Real.sin_nonneg_of_nonneg_of_le_pi hx (h.trans (by linarith [Real.pi_gt_three]))
      linarith
    · linarith [Real.neg_one_le_sin x]
  · exact Real.sin_le hx

theorem weightReal_nonneg' (q : PrimePowerPair) : 0 ≤ q.weightReal := by
  unfold PrimePowerPair.weightReal
  split_ifs
  · exact div_nonneg (Real.log_natCast_nonneg _) (Real.sqrt_nonneg _)
  · exact le_rfl

/-- Pointwise: the profile differs from the pure cosine by at most `2u/L`. -/
theorem abs_diagProfile_sub_cos_le (n : ℕ) (k : Fin (denseN n)) {u : ℝ} (hu : 0 ≤ u) :
    |diagProfile n k u - Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)|
      ≤ 2 * u / denseL n := by
  have hL : (0:ℝ) < denseL n := denseL_pos n
  have hk : (0:ℝ) < ((k : ℕ) + 1 : ℝ) * Real.pi := by positivity
  have hθ0 : 0 ≤ ((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n := by positivity
  have h1 : diagProfile n k u - Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)
      = -(u / denseL n) * Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)
        + Real.sin (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)
            / (((k : ℕ) + 1 : ℝ) * Real.pi) := by
    unfold diagProfile; ring
  have huL : 0 ≤ u / denseL n := div_nonneg hu hL.le
  have hc : |-(u / denseL n) * Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)|
      ≤ u / denseL n := by
    rw [abs_mul, abs_neg, abs_of_nonneg huL]
    exact mul_le_of_le_one_right huL (Real.abs_cos_le_one _)
  have hs : |Real.sin (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)
        / (((k : ℕ) + 1 : ℝ) * Real.pi)| ≤ u / denseL n := by
    rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
    calc |Real.sin (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)|
        ≤ ((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n := abs_sin_le_self_of_nonneg hθ0
      _ = u / denseL n * (((k : ℕ) + 1 : ℝ) * Real.pi) := by ring
  rw [h1]
  calc _ ≤ |-(u / denseL n) * Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)|
          + |Real.sin (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)
              / (((k : ℕ) + 1 : ℝ) * Real.pi)| := abs_add_le _ _
    _ ≤ u / denseL n + u / denseL n := add_le_add hc hs
    _ = 2 * u / denseL n := by ring

/-- **KB3a**: the centered diagonal is the low-frequency witness up to a uniformly small remainder. -/
theorem abs_diag_sub_lowFreqWitness_le (n : ℕ) (k : Fin (denseN n)) :
    |denseCenteredMatrix n k k - lowFreqWitness n k|
      ≤ (2 * admR n / denseL n)
          * (S1mass (admR n) + admR n * Real.exp (admR n / 2)) := by
  have hL : (0:ℝ) < denseL n := denseL_pos n
  have hR : (0:ℝ) < admR n := admR_pos n
  rw [denseCenteredMatrix_diag_closed]
  unfold lowFreqWitness
  have hφ : Continuous (fun u : ℝ => Real.exp (u / 2) * diagProfile n k u) := by
    unfold diagProfile; fun_prop
  have hcs : Continuous (fun u : ℝ => Real.exp (u / 2)
      * Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)) := by fun_prop
  -- split the sums and the integrals
  have hsumsplit :
      (∑ q ∈ activePrimePowerPairsCenterBelow (admR n), q.weightReal * diagProfile n k q.center)
        - (∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
            q.weightReal * Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * q.center / denseL n))
      = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          q.weightReal * (diagProfile n k q.center
            - Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * q.center / denseL n)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun q _ => by ring)
  have hintsplit :
      (∫ u in (0:ℝ)..(admR n), Real.exp (u / 2) * diagProfile n k u)
        - (∫ u in (0:ℝ)..(admR n), Real.exp (u / 2)
            * Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n))
      = ∫ u in (0:ℝ)..(admR n), Real.exp (u / 2)
          * (diagProfile n k u - Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)) := by
    calc _ = ∫ u in (0:ℝ)..(admR n), (Real.exp (u / 2) * diagProfile n k u
              - Real.exp (u / 2) * Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)) :=
          (intervalIntegral.integral_sub (hφ.intervalIntegrable _ _)
            (hcs.intervalIntegrable _ _)).symm
      _ = _ := intervalIntegral.integral_congr (fun u _ => by first | ring | (dsimp only; ring))
  have hrearr : ∀ A B A' B' : ℝ, (A - B) - (A' - B') = (A - A') - (B - B') := by
    intro A B A' B'; ring
  rw [hrearr, hsumsplit, hintsplit]
  -- sum part
  have hsum : |∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
        q.weightReal * (diagProfile n k q.center
          - Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * q.center / denseL n))|
      ≤ (2 * admR n / denseL n) * S1mass (admR n) := by
    calc _ ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
              |q.weightReal * (diagProfile n k q.center
                - Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * q.center / denseL n))| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
              q.weightReal * (2 * admR n / denseL n) := by
            refine Finset.sum_le_sum (fun q hq => ?_)
            rw [abs_mul, abs_of_nonneg (weightReal_nonneg' q)]
            refine mul_le_mul_of_nonneg_left ?_ (weightReal_nonneg' q)
            have hcR : q.center ≤ admR n := by
              rw [activePrimePowerPairsCenterBelow_mem] at hq
              exact hq.2
            calc _ ≤ 2 * q.center / denseL n := abs_diagProfile_sub_cos_le n k (center_nonneg q)
              _ ≤ 2 * admR n / denseL n := by gcongr
      _ = (2 * admR n / denseL n) * S1mass (admR n) := by
            rw [S1mass_eq_pairs_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun q _ => by ring)
  -- integral part
  have hint : |∫ u in (0:ℝ)..(admR n), Real.exp (u / 2)
        * (diagProfile n k u - Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n))|
      ≤ (2 * admR n / denseL n) * (admR n * Real.exp (admR n / 2)) := by
    have hpt : ∀ u ∈ Set.uIoc (0:ℝ) (admR n),
        ‖Real.exp (u / 2)
          * (diagProfile n k u - Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n))‖
          ≤ Real.exp (admR n / 2) * (2 * admR n / denseL n) := by
      intro u hu
      rw [Set.uIoc_of_le hR.le] at hu
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hu0 : 0 ≤ u := hu.1.le
      have huR : u ≤ admR n := hu.2
      have he : Real.exp (u / 2) ≤ Real.exp (admR n / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have hd : |diagProfile n k u - Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)|
          ≤ 2 * admR n / denseL n := by
        calc _ ≤ 2 * u / denseL n := abs_diagProfile_sub_cos_le n k hu0
          _ ≤ 2 * admR n / denseL n := by gcongr
      exact mul_le_mul he hd (abs_nonneg _) (Real.exp_pos _).le
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hR] at h
    calc _ ≤ Real.exp (admR n / 2) * (2 * admR n / denseL n) * admR n := h
      _ = (2 * admR n / denseL n) * (admR n * Real.exp (admR n / 2)) := by ring
  calc _ ≤ |∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
              q.weightReal * (diagProfile n k q.center
                - Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * q.center / denseL n))|
          + |∫ u in (0:ℝ)..(admR n), Real.exp (u / 2)
              * (diagProfile n k u
                - Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n))| := by
        first
          | exact abs_sub _ _
          | (rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans (by rw [abs_neg]))
    _ ≤ (2 * admR n / denseL n) * S1mass (admR n)
          + (2 * admR n / denseL n) * (admR n * Real.exp (admR n / 2)) := add_le_add hsum hint
    _ = (2 * admR n / denseL n) * (S1mass (admR n) + admR n * Real.exp (admR n / 2)) := by
        ring

#print axioms abs_diag_sub_lowFreqWitness_le

end

end RHFormalization
