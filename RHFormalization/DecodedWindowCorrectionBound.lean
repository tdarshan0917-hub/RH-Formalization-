-- SENTINEL: decoded-window-correction-bound-v5
import RHFormalization.DecodedCanonicalSectorDecomposition
import RHFormalization.AdaptiveStageMassBridge
import RHFormalization.ShiftedLaplaceBranchRange
import RHFormalization.DBFFCompensator
import RHFormalization.GalerkinCanonicalResidualBound
import Mathlib

/-! # Window-correction flank: K-uniform bound, uniform in n (hypothesis-free) -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

def invSqrtFactor (s : ℂ) : ℂ := (2 * Complex.sqrt (s + (1/4:ℂ)))⁻¹

theorem invSqrtFactor_holo : HolomorphicOnC invSqrtFactor Ω := by
  intro z hz
  have hsqrt : AnalyticAt ℂ (fun s : ℂ => Complex.sqrt (s + (1/4:ℂ))) z :=
    sqrtShiftFun_analyticAt hz
  have hne : (2:ℂ) * Complex.sqrt (z + (1/4:ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (sqrt_ne_zero' hz)
  have hmul : AnalyticAt ℂ (fun s : ℂ => (2:ℂ) * Complex.sqrt (s + (1/4:ℂ))) z :=
    analyticAt_const.mul hsqrt
  have hinv : AnalyticAt ℂ invSqrtFactor z := by
    unfold invSqrtFactor
    exact hmul.inv hne
  exact hinv.analyticWithinAt

theorem kernel_eq_prefactor_mul_exp (a : ℝ) (s : ℂ) :
    shiftedLaplaceHeatKernelC a s
      = invSqrtFactor s * Complex.exp (-(a:ℂ) * Complex.sqrt (s + (1/4:ℂ))) := by
  unfold shiftedLaplaceHeatKernelC invSqrtFactor
  rw [one_div]

theorem kernel_exp_norm_le_one (a : ℝ) (ha : 0 ≤ a) (s : ℂ) :
    ‖Complex.exp (-(a:ℂ) * Complex.sqrt (s + (1/4:ℂ)))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  have hre : (-(a:ℂ) * Complex.sqrt (s + (1/4:ℂ))).re
      = -a * (Complex.sqrt (s + (1/4:ℂ))).re := by
    simp [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  have h0 := sqrt_re_nonneg (s + (1/4:ℂ))
  nlinarith

theorem admR_nonneg (n : ℕ) : 0 ≤ admR n := by
  have hx : (1:ℝ) ≤ (n:ℝ)+2 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hR : admR n = Real.log ((n:ℝ)+2) / 2 := by
    first | rfl | (unfold admR; ring) | (unfold admR; push_cast; ring)
  rw [hR]
  have := Real.log_nonneg hx
  linarith

theorem admR_mul_mass_le_adaptiveL (c : ℝ) (n : ℕ) :
    admR n * adaptiveStageMass n ≤ adaptiveL c n := by
  have hx : (2:ℝ) ≤ (n:ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hxpos : (0:ℝ) < (n:ℝ) + 2 := by linarith
  have hR : admR n = Real.log ((n:ℝ)+2) / 2 := by
    first | rfl | (unfold admR; ring) | (unfold admR; push_cast; ring)
  have hmass := adaptiveStageMass_le_sqrt n
  have hlog : Real.log ((n:ℝ)+2) ≤ (n:ℝ)+2 := by
    have h := Real.log_le_sub_one_of_pos hxpos
    linarith
  have hlog0 : 0 ≤ Real.log ((n:ℝ)+2) := Real.log_nonneg (by linarith)
  have hsqrt : Real.sqrt ((n:ℝ)+2) ≤ (n:ℝ)+2 := by
    have h1 : Real.sqrt ((n:ℝ)+2) ≤ Real.sqrt (((n:ℝ)+2)^2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h1
  have hsqrt0 : 0 ≤ Real.sqrt ((n:ℝ)+2) := Real.sqrt_nonneg _
  have hcube : ((n:ℝ)+2)^3 ≤ adaptiveL c n := by
    have h1 := admL_le_adaptiveL c n
    have h2 : admL n = ((n:ℝ)+2)^3 := by
      first | rfl | (unfold admL; ring) | (unfold admL; push_cast; ring)
    linarith [h2 ▸ h1]
  have hR0 := admR_nonneg n
  have hquad : ((n:ℝ)+2) + 2 ≤ ((n:ℝ)+2)^2 := by nlinarith [hx]
  have hpoly : ((n:ℝ)+2) * (((n:ℝ)+2) + 2) ≤ ((n:ℝ)+2)^3 := by
    have h := mul_le_mul_of_nonneg_left hquad hxpos.le
    calc ((n:ℝ)+2) * (((n:ℝ)+2) + 2)
        ≤ ((n:ℝ)+2) * (((n:ℝ)+2)^2) := h
      _ = ((n:ℝ)+2)^3 := by ring
  have hstep : Real.log ((n:ℝ)+2) * (Real.sqrt ((n:ℝ)+2) + 2)
      ≤ ((n:ℝ)+2) * (((n:ℝ)+2) + 2) := by
    apply mul_le_mul hlog (by linarith) (by linarith) (by linarith)
  have hkey : Real.log ((n:ℝ)+2) / 2 * (2 * (Real.sqrt ((n:ℝ)+2) + 2))
      ≤ ((n:ℝ)+2)^3 := by
    calc Real.log ((n:ℝ)+2) / 2 * (2 * (Real.sqrt ((n:ℝ)+2) + 2))
        = Real.log ((n:ℝ)+2) * (Real.sqrt ((n:ℝ)+2) + 2) := by ring
      _ ≤ ((n:ℝ)+2) * (((n:ℝ)+2) + 2) := hstep
      _ ≤ ((n:ℝ)+2)^3 := hpoly
  calc admR n * adaptiveStageMass n
      ≤ admR n * (2 * (Real.sqrt ((n:ℝ)+2) + 2)) :=
        mul_le_mul_of_nonneg_left hmass hR0
    _ = Real.log ((n:ℝ)+2) / 2 * (2 * (Real.sqrt ((n:ℝ)+2) + 2)) := by rw [hR]
    _ ≤ ((n:ℝ)+2)^3 := hkey
    _ ≤ adaptiveL c n := hcube

theorem decodedWindowCorrection_uniform_bound (c : ℝ)
    (K : Set ℂ) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ K,
      ‖decodedWindowCorrection c n s‖ ≤ C := by
  obtain ⟨CK, hCK0, hCK⟩ := exists_bound_of_holo_on_compact
    invSqrtFactor invSqrtFactor_holo K hK hKO
  refine ⟨CK, hCK0, fun n s hs => ?_⟩
  have hL : (0:ℝ) < adaptiveL c n := adaptiveL_pos c n
  have hR0 := admR_nonneg n
  have hA0 : (0:ℝ) ≤ admR n / adaptiveL c n := div_nonneg hR0 hL.le
  have hterm : ∀ q ∈ activePrimePowerPairsCenterBelow (admR n),
      ‖q.weightC * (((q.center / adaptiveL c n : ℝ)) : ℂ)
          * shiftedLaplaceHeatKernelC q.center s‖
        ≤ ‖q.weightC‖ * (admR n / adaptiveL c n) * CK := by
    intro q hq
    obtain ⟨_, hcle⟩ := (activePrimePowerPairsCenterBelow_mem (admR n) q).mp hq
    have hc0 : (0:ℝ) ≤ q.center := center_nonneg q
    have hw0 : (0:ℝ) ≤ ‖q.weightC‖ := norm_nonneg _
    have hKb : ‖shiftedLaplaceHeatKernelC q.center s‖ ≤ CK := by
      rw [kernel_eq_prefactor_mul_exp q.center s, norm_mul]
      have hst := mul_le_mul (hCK s hs)
        (kernel_exp_norm_le_one q.center hc0 s)
        (norm_nonneg (Complex.exp (-(q.center:ℂ)
          * Complex.sqrt (s + (1/4:ℂ))))) hCK0
      calc ‖invSqrtFactor s‖
            * ‖Complex.exp (-(q.center:ℂ) * Complex.sqrt (s + (1/4:ℂ)))‖
          ≤ CK * 1 := hst
        _ = CK := mul_one CK
    have hrb : ‖(((q.center / adaptiveL c n : ℝ)) : ℂ)‖
        ≤ admR n / adaptiveL c n := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg hc0 hL.le)]
      first
        | exact div_le_div_of_nonneg_right hcle hL
        | exact (div_le_div_iff_of_pos_right hL).mpr hcle
        | exact (div_le_div_right hL).mpr hcle
        | (apply div_le_div_of_le_left <;> [exact hcle; exact hL; skip])
    have hr0 : (0:ℝ) ≤ ‖(((q.center / adaptiveL c n : ℝ)) : ℂ)‖ :=
      norm_nonneg _
    have hstep1 : ‖q.weightC‖ * ‖(((q.center / adaptiveL c n : ℝ)) : ℂ)‖
        ≤ ‖q.weightC‖ * (admR n / adaptiveL c n) :=
      mul_le_mul_of_nonneg_left hrb hw0
    have hstep2 : ‖q.weightC‖ * ‖(((q.center / adaptiveL c n : ℝ)) : ℂ)‖
          * ‖shiftedLaplaceHeatKernelC q.center s‖
        ≤ (‖q.weightC‖ * (admR n / adaptiveL c n)) * CK :=
      mul_le_mul hstep1 hKb (norm_nonneg _) (mul_nonneg hw0 hA0)
    calc ‖q.weightC * (((q.center / adaptiveL c n : ℝ)) : ℂ)
            * shiftedLaplaceHeatKernelC q.center s‖
        = ‖q.weightC‖ * ‖(((q.center / adaptiveL c n : ℝ)) : ℂ)‖
            * ‖shiftedLaplaceHeatKernelC q.center s‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ (‖q.weightC‖ * (admR n / adaptiveL c n)) * CK := hstep2
      _ = ‖q.weightC‖ * (admR n / adaptiveL c n) * CK := by ring
  have hmass_def : adaptiveStageMass n
      = ∑ q ∈ activePrimePowerPairsCenterBelow (admR n), ‖q.weightC‖ := by
    first | rfl | (unfold adaptiveStageMass; rfl)
  have hfrac : admR n / adaptiveL c n * adaptiveStageMass n ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hL]
    exact admR_mul_mass_le_adaptiveL c n
  have hs1 : ‖decodedWindowCorrection c n s‖
      ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          ‖q.weightC * (((q.center / adaptiveL c n : ℝ)) : ℂ)
            * shiftedLaplaceHeatKernelC q.center s‖ := by
    unfold decodedWindowCorrection
    exact norm_sum_le _ _
  have hs2 : (∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
        ‖q.weightC * (((q.center / adaptiveL c n : ℝ)) : ℂ)
          * shiftedLaplaceHeatKernelC q.center s‖)
      ≤ ∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
          ‖q.weightC‖ * (admR n / adaptiveL c n) * CK :=
    Finset.sum_le_sum hterm
  have hs3 : (∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
        ‖q.weightC‖ * (admR n / adaptiveL c n) * CK)
      = adaptiveStageMass n * (admR n / adaptiveL c n * CK) := by
    rw [hmass_def, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  have hs4 : adaptiveStageMass n * (admR n / adaptiveL c n * CK) ≤ CK := by
    have h1 : adaptiveStageMass n * (admR n / adaptiveL c n * CK)
        = (admR n / adaptiveL c n * adaptiveStageMass n) * CK := by ring
    rw [h1]
    have h2 : (admR n / adaptiveL c n * adaptiveStageMass n) * CK
        ≤ 1 * CK := mul_le_mul_of_nonneg_right hfrac hCK0
    calc (admR n / adaptiveL c n * adaptiveStageMass n) * CK
        ≤ 1 * CK := h2
      _ = CK := one_mul CK
  have hfinal : ‖decodedWindowCorrection c n s‖ ≤ CK := by
    refine le_trans hs1 (le_trans hs2 ?_)
    rw [hs3]
    exact hs4
  exact hfinal

#print axioms invSqrtFactor_holo
#print axioms admR_mul_mass_le_adaptiveL
#print axioms decodedWindowCorrection_uniform_bound

end

end RHFormalization
