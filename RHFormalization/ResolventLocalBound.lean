import RHFormalization.ResolventTraceHolo
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Basic

/-!
# RHFormalization.ResolventLocalBound
Large-eigenvalue tail bound: for `s` with `‖s‖ ≤ R0` and `lam ≥ 2 R0`, `lam > 0`,
`‖(s+lam)⁻¹‖ ≤ 2/lam`, via `‖s+lam‖ ≥ s.re + lam ≥ lam/2`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter

theorem resolvent_norm_le_of_large
    (R0 : ℝ) (s : ℂ) (hs : ‖s‖ ≤ R0) (lam : ℝ) (hlam : 0 ≤ lam)
    (hbig : 2 * R0 ≤ lam) (hlam_pos : 0 < lam) :
    ‖(s + (lam : ℂ))⁻¹‖ ≤ 2 / lam := by
  have hR0 : 0 ≤ R0 := le_trans (norm_nonneg s) hs
  have hre : s.re + lam ≤ ‖s + (lam : ℂ)‖ := by
    have h := re_le_norm (s + (lam : ℂ))
    simpa [Complex.add_re, Complex.ofReal_re] using h
  have hRes : -R0 ≤ s.re := by
    have h := abs_re_le_norm s
    rw [abs_le] at h
    linarith [h.1, hs]
  have hlb : lam / 2 ≤ ‖s + (lam : ℂ)‖ := by linarith [hre, hRes, hbig]
  have hnorm_pos : 0 < ‖s + (lam : ℂ)‖ := lt_of_lt_of_le (by linarith) hlb
  rw [norm_inv, inv_le_iff_one_le_mul₀ hnorm_pos]
  -- goal is now: 1 ≤ 2 / lam * ‖s + lam‖, with hlb : lam/2 ≤ ‖s+lam‖
  rw [div_mul_eq_mul_div, le_div_iff₀ hlam_pos]
  nlinarith [hlb, hlam_pos]

#print axioms resolvent_norm_le_of_large
